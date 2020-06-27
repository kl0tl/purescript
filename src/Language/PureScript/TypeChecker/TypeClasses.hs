-- |
-- This module implements the desugaring pass which creates type synonyms for
-- type class dictionaries.
--
module Language.PureScript.TypeChecker.TypeClasses
  ( desugarTypeClass
  , superClassDictionaryNames
  ) where

import Prelude.Compat

import           Control.Arrow (first)
import           Data.Text (Text)
import           Language.PureScript.Crash
import           Language.PureScript.Environment
import           Language.PureScript.Errors hiding (isExported)
import           Language.PureScript.Label (Label(..))
import           Language.PureScript.Names
import           Language.PureScript.PSString (mkString)
import           Language.PureScript.Types
import           Language.PureScript.TypeClassDictionaries (superclassName)

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
--   -- The following type is marked as not needing to be checked so a new Abs
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
desugarTypeClass
  :: Qualified (ProperName 'ClassName)
  -> [(Text, Maybe SourceType)]
  -> [SourceConstraint]
  -> [Declaration]
  -> (TypeClassDictionary, [TypeClassDictionaryAccessor])
desugarTypeClass qualifiedClassName args implies members =
  ( typeClassDictionary (disqualify qualifiedClassName) implies members
  , map (typeClassMemberToDictionaryAccessor qualifiedClassName args) members
  )

memberToNameAndType :: Declaration -> (Ident, SourceType)
memberToNameAndType (TypeDeclaration td) = unwrapTypeDeclaration td
memberToNameAndType _ = internalError "Invalid declaration in type class definition"

type TypeClassDictionary =
  ( ProperName 'TypeName
  , SourceType
  )

typeClassDictionary
  :: ProperName 'ClassName
  -> [SourceConstraint]
  -> [Declaration]
  -> TypeClassDictionary
typeClassDictionary className implies members =
  let superclassTypes = superClassDictionaryNames implies `zip`
        [ function unit (foldl srcTypeApp (srcTypeConstructor (fmap (coerceProperName . dictSynonymName) superclass)) tyArgs)
        | (Constraint _ superclass _ tyArgs _) <- implies
        ]
      members' = map (first runIdent . memberToNameAndType) members
      mtys = members' ++ superclassTypes
      toRowListItem (l, t) = srcRowListItem (Label $ mkString l) t
  in (coerceProperName $ dictSynonymName className, srcTypeApp tyRecord $ rowFromList (map toRowListItem mtys, srcREmpty))

type TypeClassDictionaryAccessor =
  ( SourceAnn
  , Ident
  , Expr
  )

typeClassMemberToDictionaryAccessor
  :: Qualified (ProperName 'ClassName)
  -> [(Text, Maybe SourceType)]
  -> Declaration
  -> TypeClassDictionaryAccessor
typeClassMemberToDictionaryAccessor qualifiedClassName args (TypeDeclaration (TypeDeclarationData sa ident ty)) =
  (sa, ident, TypedValue False (TypeClassDictionaryAccessor qualifiedClassName ident) $
    moveQuantifiersToFront (quantify (srcConstrainedType (srcConstraint qualifiedClassName [] (map (srcTypeVar . fst) args) Nothing) ty))
  )
typeClassMemberToDictionaryAccessor _ _ _ = internalError "Invalid declaration in type class definition"

unit :: SourceType
unit = srcTypeApp tyRecord srcREmpty

superClassDictionaryNames :: [Constraint a] -> [Text]
superClassDictionaryNames supers =
  [ superclassName pn index
  | (index, Constraint _ pn _ _ _) <- zip [0..] supers
  ]
