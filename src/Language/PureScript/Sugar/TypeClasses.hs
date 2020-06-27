-- |
-- This module implements the desugaring pass which creates type synonyms for
-- type class dictionaries.
--
module Language.PureScript.Sugar.TypeClasses
  ( DesugarState
  , desugarTypeClasses
  , superClassDictionaryNames
  ) where

import Prelude.Compat

import           Control.Arrow (first)
import           Control.Monad.Error.Class (MonadError(..))
import           Control.Monad.State
import           Control.Monad.Supply.Class
import           Data.Graph
import           Data.List (partition)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe)
import           Data.Text (Text)
import qualified Language.PureScript.Constants.Prim as C
import           Language.PureScript.Crash
import           Language.PureScript.Environment
import           Language.PureScript.Errors hiding (isExported)
import           Language.PureScript.Externs
import           Language.PureScript.Label (Label(..))
import           Language.PureScript.Names
import           Language.PureScript.PSString (mkString)
import           Language.PureScript.Types
import           Language.PureScript.TypeClassDictionaries (superclassName)

type DesugarState = M.Map (ModuleName, ProperName 'ClassName) TypeClassData

type Desugar = StateT DesugarState

-- |
-- Add type synonym declarations for type class dictionary types.
--
desugarTypeClasses
  :: (MonadSupply m, MonadError MultipleErrors m)
  => [ExternsFile]
  -> [Module]
  -> m ([Module], DesugarState)
desugarTypeClasses externs = flip runStateT initialState . traverse desugarModule
  where
  initialState :: DesugarState
  initialState =
    mconcat
      [ M.mapKeys (qualify C.Prim) primClasses
      , M.mapKeys (qualify C.PrimCoerce) primCoerceClasses
      , M.mapKeys (qualify C.PrimRow) primRowClasses
      , M.mapKeys (qualify C.PrimRowList) primRowListClasses
      , M.mapKeys (qualify C.PrimSymbol) primSymbolClasses
      , M.mapKeys (qualify C.PrimTypeError) primTypeErrorClasses
      , M.fromList (externs >>= \ExternsFile{..} -> mapMaybe (fromExternsDecl efModuleName) efDeclarations)
      ]

  fromExternsDecl
    :: ModuleName
    -> ExternsDeclaration
    -> Maybe ((ModuleName, ProperName 'ClassName), TypeClassData)
  fromExternsDecl mn (EDClass name args members implies deps tcIsEmpty) = Just ((mn, name), typeClass) where
    typeClass = makeTypeClassData args members implies deps tcIsEmpty
  fromExternsDecl _ _ = Nothing

desugarModule
  :: (MonadSupply m, MonadError MultipleErrors m)
  => Module
  -> Desugar m Module
desugarModule (Module ss coms name decls exps) = do
  let (classDecls, restDecls) = partition isTypeClassDecl decls
      classVerts = fmap (\d -> (d, classDeclName d, superClassesNames d)) classDecls
  classDeclss <- parU (stronglyConnComp classVerts) (desugarClassDecl name)
  return $ Module ss coms name (restDecls ++ concat classDeclss) exps
  where
  desugarClassDecl :: (MonadSupply m, MonadError MultipleErrors m)
    => ModuleName
    -> SCC Declaration
    -> Desugar m [Declaration]
  desugarClassDecl name' (AcyclicSCC d) = desugarDecl name' d
  desugarClassDecl _ (CyclicSCC ds') = throwError . errorMessage' (declSourceSpan (head ds')) $ CycleInTypeClassDeclaration (map classDeclName ds')

  superClassesNames :: Declaration -> [Qualified (ProperName 'ClassName)]
  superClassesNames (TypeClassDeclaration _ _ _ implies _ _) = fmap constraintName implies
  superClassesNames _ = []

  constraintName :: SourceConstraint -> Qualified (ProperName 'ClassName)
  constraintName (Constraint _ cName _ _ _) = cName

  classDeclName :: Declaration -> Qualified (ProperName 'ClassName)
  classDeclName (TypeClassDeclaration _ pn _ _ _ _) = Qualified (Just name) pn
  classDeclName _ = internalError "Expected TypeClassDeclaration"

{- Desugar type class declarations
--
-- Type classes become type synonyms for their dictionaries and additional
-- values are generated to access individual members of a dictionary, with the
-- appropriate type.
--
-- E.g. the following
--
--   module Test where
--
--   class Foo a where
--     foo :: a -> a
--
--   {- Superclasses -}
--
--   class (Foo a) <= Sub a where
--     sub :: a
--
-- becomes:
--
--   <TypeClassDeclaration Foo ...>
--
--   type Foo a = { foo :: a -> a }
--
--   -- this following type is marked as not needing to be checked so a new Abs
--   -- is not introduced around the definition in type checking, but when
--   -- called the dictionary value is still passed in for the `dict` argument
--   foo :: forall a. (Foo a) => a -> a
--   foo dict = dict.foo
--
--   {- Superclasses -}
--
--   <TypeClassDeclaration Sub ...>
--
--   type Sub a = { sub :: a
--                , "Foo0" :: {} -> Foo a
--                }
--
--   -- As with `foo` above, this type is unchecked at the declaration
--   sub :: forall a. (Sub a) => a
--   sub dict = dict.sub
--
-- and finally as the generated javascript:
--
--   function Foo(foo) {
--       this.foo = foo;
--   };
--
--   var foo = function (dict) {
--       return dict.foo;
--   };
--
--   function Sub(Foo0, sub) {
--       this["Foo0"] = Foo0;
--       this.sub = sub;
--   };
--
--   var sub = function (dict) {
--       return dict.sub;
--   };
-}
desugarDecl
  :: (MonadSupply m, MonadError MultipleErrors m)
  => ModuleName
  -> Declaration
  -> Desugar m [Declaration]
desugarDecl mn = go
  where
  go d@(TypeClassDeclaration sa name args implies deps members) = do
    modify (M.insert (mn, name) (makeTypeClassData args (map memberToNameAndType members) implies deps False))
    return $ d : typeClassDictionaryDeclaration sa name args implies members : map (typeClassMemberToDictionaryAccessor mn name args) members
  go other = return [other]

memberToNameAndType :: Declaration -> (Ident, SourceType)
memberToNameAndType (TypeDeclaration td) = unwrapTypeDeclaration td
memberToNameAndType _ = internalError "Invalid declaration in type class definition"

typeClassDictionaryDeclaration
  :: SourceAnn
  -> ProperName 'ClassName
  -> [(Text, Maybe SourceType)]
  -> [SourceConstraint]
  -> [Declaration]
  -> Declaration
typeClassDictionaryDeclaration sa name args implies members =
  let superclassTypes = superClassDictionaryNames implies `zip`
        [ function unit (foldl srcTypeApp (srcTypeConstructor (fmap (coerceProperName . dictSynonymName) superclass)) tyArgs)
        | (Constraint _ superclass _ tyArgs _) <- implies
        ]
      members' = map (first runIdent . memberToNameAndType) members
      mtys = members' ++ superclassTypes
      toRowListItem (l, t) = srcRowListItem (Label $ mkString l) t
  in TypeSynonymDeclaration sa (coerceProperName $ dictSynonymName name) args (srcTypeApp tyRecord $ rowFromList (map toRowListItem mtys, srcREmpty))

typeClassMemberToDictionaryAccessor
  :: ModuleName
  -> ProperName 'ClassName
  -> [(Text, Maybe SourceType)]
  -> Declaration
  -> Declaration
typeClassMemberToDictionaryAccessor mn name args (TypeDeclaration (TypeDeclarationData sa ident ty)) =
  let className = Qualified (Just mn) name
  in ValueDecl sa ident Private [] $
    [MkUnguarded (
     TypedValue False (TypeClassDictionaryAccessor className ident) $
       moveQuantifiersToFront (quantify (srcConstrainedType (srcConstraint className [] (map (srcTypeVar . fst) args) Nothing) ty))
    )]
typeClassMemberToDictionaryAccessor _ _ _ _ = internalError "Invalid declaration in type class definition"

unit :: SourceType
unit = srcTypeApp tyRecord srcREmpty

superClassDictionaryNames :: [Constraint a] -> [Text]
superClassDictionaryNames supers =
  [ superclassName pn index
  | (index, Constraint _ pn _ _ _) <- zip [0..] supers
  ]
