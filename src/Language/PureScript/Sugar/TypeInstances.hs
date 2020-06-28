-- |
-- This module implements the desugaring pass which creates dictionary
-- expressions for type class instances.
--
module Language.PureScript.Sugar.TypeInstances
  ( desugarTypeInstances
  , typeClassMemberName
  ) where

import Prelude.Compat

import           Control.Arrow (first, second)
import           Control.Monad.Error.Class (MonadError(..))
import           Control.Monad.Reader
import           Control.Monad.Supply.Class
import           Data.List (find, partition)
import qualified Data.Map as M
import           Data.Maybe (catMaybes, mapMaybe, isJust, fromMaybe)
import qualified Data.List.NonEmpty as NEL
import qualified Data.Set as S
import           Data.Text (Text)
import           Language.PureScript.Crash
import           Language.PureScript.Environment
import           Language.PureScript.Errors hiding (isExported)
import           Language.PureScript.Names
import           Language.PureScript.PSString (mkString)
import           Language.PureScript.Sugar.CaseDeclarations
import           Language.PureScript.Sugar.TypeClasses (DesugarState, superClassDictionaryNames)
import           Language.PureScript.Types

-- |
-- Add value declarations for type class instance dictionary expressions.
--
desugarTypeInstances
  :: MonadError MultipleErrors m
  => MonadReader DesugarState m
  => MonadSupply m
  => [Module]
  -> m [Module]
desugarTypeInstances = traverse $ \case
  Module ss coms name decls (Just exps) -> do
    let (classDecls, restDecls) = partition isTypeClassDecl decls
    (restNewExpss, restDeclss) <- unzip <$> parU restDecls (desugarDecl name exps)
    return $ Module ss coms name (concat restDeclss ++ classDecls) $ Just (exps ++ catMaybes restNewExpss)
  _ -> internalError "Exports should have been elaborated in name desugaring"

{- Desugar type class instance declarations
--
-- Type instances become dictionary declarations.
--
-- E.g. the following instances
--
--   module Test where
--
--   class Foo a where
--     foo :: a -> a
--
--   instance fooString :: Foo String where
--     foo s = s ++ s
--
--   instance fooArray :: (Foo a) => Foo [a] where
--     foo = map foo
--
--   {- Superclasses -}
--
--   class (Foo a) <= Sub a where
--     sub :: a
--
--   instance subString :: Sub String where
--     sub = ""
--
-- become:
--
--   fooString :: {} -> Foo String
--   fooString _ = <TypeClassDictionaryConstructorApp Foo { foo: \s -> s ++ s }>
--
--   fooArray :: forall a. (Foo a) => Foo [a]
--   fooArray = <TypeClassDictionaryConstructorApp Foo { foo: map foo }>
--
--   {- Superclasses -}
--
--   subString :: {} -> Sub String
--   subString _ = { sub: "",
--                 , "Foo0": \_ -> <DeferredDictionary Foo String>
--                 }
--
-- and finally as the generated javascript:
--
--   var fooString = function (_) {
--       return new Foo(function (s) {
--           return s + s;
--       });
--   };
--
--   var fooArray = function (__dict_Foo_15) {
--       return new Foo(map(foo(__dict_Foo_15)));
--   };
--
--   var subString = function (_) {
--       return new Sub(fooString, "");
--   };
-}
desugarDecl
  :: MonadError MultipleErrors m
  => MonadReader DesugarState m
  => MonadSupply m
  => ModuleName
  -> [DeclarationRef]
  -> Declaration
  -> m (Maybe DeclarationRef, [Declaration])
desugarDecl mn exps = go
  where
  go (TypeInstanceDeclaration _ _ _ _ _ _ _ DerivedInstance{}) = internalError "Derived instance should have been desugared"
  go (TypeInstanceDeclaration _ _ _ AnonymousTypeInstance _ _ _ _) = internalError "Anonymous instance should have been desugared"
  go d@(TypeInstanceDeclaration sa _ _ (getTypeInstanceName -> Just name) deps className tys (ExplicitInstance members)) = do
    desugared <- desugarCases members
    dictDecl <- typeInstanceDictionaryDeclaration sa name mn deps className tys desugared
    return (expRef name className tys, [d, dictDecl])
  go d@(TypeInstanceDeclaration sa _ _ (getTypeInstanceName -> Just name) deps className tys (NewtypeInstanceWithDictionary dict)) = do
    let dictTy = foldl srcTypeApp (srcTypeConstructor (fmap (coerceProperName . dictSynonymName) className)) tys
        constrainedTy = quantify (foldr (srcConstrainedType) dictTy deps)
    return (expRef name className tys, [d, ValueDecl sa name Private [] [MkUnguarded (TypedValue True dict constrainedTy)]])
  go other = return (Nothing, [other])

  expRef :: Ident -> Qualified (ProperName 'ClassName) -> [SourceType] -> Maybe DeclarationRef
  expRef name className tys
    | isExportedClass className && all isExportedType (getConstructors `concatMap` tys) = Just $ TypeInstanceRef genSpan name
    | otherwise = Nothing

  isExportedClass :: Qualified (ProperName 'ClassName) -> Bool
  isExportedClass = isExported (elem . TypeClassRef genSpan)

  isExportedType :: Qualified (ProperName 'TypeName) -> Bool
  isExportedType = isExported $ \pn -> isJust . find (matchesTypeRef pn)

  isExported
    :: (ProperName a -> [DeclarationRef] -> Bool)
    -> Qualified (ProperName a)
    -> Bool
  isExported test (Qualified (Just mn') pn) = mn /= mn' || test pn exps
  isExported _ _ = internalError "Names should have been qualified in name desugaring"

  matchesTypeRef :: ProperName 'TypeName -> DeclarationRef -> Bool
  matchesTypeRef pn (TypeRef _ pn' _) = pn == pn'
  matchesTypeRef _ _ = False

  getConstructors :: SourceType -> [Qualified (ProperName 'TypeName)]
  getConstructors = everythingOnTypes (++) getConstructor
    where
    getConstructor (TypeConstructor _ tcname) = [tcname]
    getConstructor _ = []

  genSpan :: SourceSpan
  genSpan = internalModuleSourceSpan "<generated>"

typeInstanceDictionaryDeclaration
  :: forall m
   . MonadError MultipleErrors m
  => MonadReader DesugarState m
  => MonadSupply m
  => SourceAnn
  -> Ident
  -> ModuleName
  -> [SourceConstraint]
  -> Qualified (ProperName 'ClassName)
  -> [SourceType]
  -> [Declaration]
  -> m Declaration
typeInstanceDictionaryDeclaration sa@(ss, _) name mn deps className tys decls =
  rethrow (addHint (ErrorInInstance className tys)) $ do
  m <- ask

  -- Lookup the type arguments and member types for the type class
  TypeClassData{..} <-
    maybe (throwError . errorMessage' ss . UnknownName $ fmap TyClassName className) return $
      M.lookup (qualify mn className) m

  -- Replace the type arguments with the appropriate types in the member types
  let memberTypes = map (second (replaceAllTypeVars (zip (map fst typeClassArguments) tys))) typeClassMembers

  let declaredMembers = S.fromList $ mapMaybe declIdent decls

  case filter (\(ident, _) -> not $ S.member ident declaredMembers) memberTypes of
    hd : tl -> throwError . errorMessage' ss $ MissingClassMember (hd NEL.:| tl)
    [] -> do
      -- Create values for the type instance members
      members <- zip (map typeClassMemberName decls) <$> traverse (memberToValue memberTypes) decls

      -- Create the type of the dictionary
      -- The type is a record type, but depending on type instance dependencies, may be constrained.
      -- The dictionary itself is a record literal.
      let superclasses = superClassDictionaryNames typeClassSuperclasses `zip`
            [ Abs (VarBinder ss UnusedIdent) (DeferredDictionary superclass tyArgs)
            | (Constraint _ superclass _ suTyArgs _) <- typeClassSuperclasses
            , let tyArgs = map (replaceAllTypeVars (zip (map fst typeClassArguments) tys)) suTyArgs
            ]

      let props = Literal ss $ ObjectLiteral $ map (first mkString) (members ++ superclasses)
          dictTy = foldl srcTypeApp (srcTypeConstructor (fmap (coerceProperName . dictSynonymName) className)) tys
          constrainedTy = quantify (foldr srcConstrainedType dictTy deps)
          dict = TypeClassDictionaryConstructorApp className props
          result = ValueDecl sa name Private [] [MkUnguarded (TypedValue True dict constrainedTy)]
      return result

  where

  memberToValue :: [(Ident, SourceType)] -> Declaration -> m Expr
  memberToValue tys' (ValueDecl (ss', _) ident _ [] [MkUnguarded val]) = do
    _ <- maybe (throwError . errorMessage' ss' $ ExtraneousClassMember ident className) return $ lookup ident tys'
    return val
  memberToValue _ _ = internalError "Invalid declaration in type instance definition"

declIdent :: Declaration -> Maybe Ident
declIdent (ValueDeclaration vd) = Just (valdeclIdent vd)
declIdent (TypeDeclaration td) = Just (tydeclIdent td)
declIdent _ = Nothing

typeClassMemberName :: Declaration -> Text
typeClassMemberName = fromMaybe (internalError "typeClassMemberName: Invalid declaration in type class definition") . fmap runIdent . declIdent
