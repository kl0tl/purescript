-- |
-- This module implements the desugaring pass which creates dictionary
-- expressions for type class instances.
--
module Language.PureScript.TypeChecker.TypeInstances
  ( desugarTypeInstance
  , typeClassMemberName
  ) where

import Prelude.Compat

import           Control.Arrow (first, second)
import           Control.Monad (guard)
import           Control.Monad.Error.Class (MonadError(..))
import           Control.Monad.State.Class (MonadState(..))
import           Control.Monad.Writer.Class (MonadWriter(..))
import           Control.Monad.Supply.Class
import           Data.List (find)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe, isJust, fromMaybe)
import qualified Data.List.NonEmpty as NEL
import qualified Data.Set as S
import           Data.Text (Text)
import qualified Language.PureScript.Constants.Prelude as C
import           Language.PureScript.Crash
import           Language.PureScript.Environment
import           Language.PureScript.Errors hiding (isExported)
import           Language.PureScript.Names
import           Language.PureScript.PSString (mkString)
import           Language.PureScript.Sugar.CaseDeclarations
import           Language.PureScript.TypeChecker.Monad
import           Language.PureScript.TypeChecker.TypeClasses (superClassDictionaryNames)
import           Language.PureScript.TypeChecker.TypeClasses.Deriving
import           Language.PureScript.Types

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
desugarTypeInstance
  :: MonadSupply m
  => MonadState CheckState m
  => MonadError MultipleErrors m
  => MonadWriter MultipleErrors m
  => ModuleName
  -> [DeclarationRef]
  -> SourceSpan
  -> Ident
  -> [SourceConstraint]
  -> Qualified (ProperName 'ClassName)
  -> [SourceType]
  -> TypeInstanceBody
  -> m (Maybe DeclarationRef, Expr)
desugarTypeInstance mn exps ss name deps className tys body = do
  dict <- go body
  return
    ( do guard $ isExportedClass className
         guard $ all isExportedType (getConstructors `concatMap` tys)
         return $ TypeInstanceRef genSpan name
    , dict
    )
  where
  go DerivedInstance
    | className == Qualified (Just dataEq) (ProperName "Eq")
    = case tys of
      [ty] | Just (Qualified mn' tyCon, _) <- unwrapTypeConstructor ty
           , mn == fromMaybe mn mn'
           -> deriveEq ss mn tyCon >>= desugarCases >>= typeInstanceDictionary ss deps className tys
           | otherwise -> throwError . errorMessage' ss $ ExpectedTypeConstructor className tys ty
      _ -> throwError . errorMessage' ss $ InvalidDerivedInstance className tys 1
    | className == Qualified (Just dataEq) (ProperName "Eq1")
    = case tys of
        [ty] | Just (Qualified mn' _, _) <- unwrapTypeConstructor ty
             , mn == fromMaybe mn mn'
             -> desugarCases (deriveEq1 ss) >>= typeInstanceDictionary ss deps className tys
             | otherwise -> throwError . errorMessage' ss $ ExpectedTypeConstructor className tys ty
        _ -> throwError . errorMessage' ss $ InvalidDerivedInstance className tys 1
    | className == Qualified (Just dataOrd) (ProperName "Ord")
    = case tys of
        [ty] | Just (Qualified mn' tyCon, _) <- unwrapTypeConstructor ty
             , mn == fromMaybe mn mn'
             -> deriveOrd ss mn tyCon >>= desugarCases >>= typeInstanceDictionary ss deps className tys
             | otherwise -> throwError . errorMessage' ss $ ExpectedTypeConstructor className tys ty
        _ -> throwError . errorMessage' ss $ InvalidDerivedInstance className tys 1
    | className == Qualified (Just dataOrd) (ProperName "Ord1")
    = case tys of
        [ty] | Just (Qualified mn' _, _) <- unwrapTypeConstructor ty
             , mn == fromMaybe mn mn'
             -> desugarCases (deriveOrd1 ss) >>= typeInstanceDictionary ss deps className tys
             | otherwise -> throwError . errorMessage' ss $ ExpectedTypeConstructor className tys ty
        _ -> throwError . errorMessage' ss $ InvalidDerivedInstance className tys 1
    | className == Qualified (Just dataFunctor) (ProperName "Functor")
    = case tys of
        [ty] | Just (Qualified mn' tyCon, _) <- unwrapTypeConstructor ty
             , mn == fromMaybe mn mn'
             -> deriveFunctor ss mn tyCon >>= desugarCases >>= typeInstanceDictionary ss deps className tys
             | otherwise -> throwError . errorMessage' ss $ ExpectedTypeConstructor className tys ty
        _ -> throwError . errorMessage' ss $ InvalidDerivedInstance className tys 1
    | className == Qualified (Just dataNewtype) (ProperName "Newtype")
    = case tys of
        [wrappedTy, unwrappedTy]
          | Just (Qualified mn' tyCon, args) <- unwrapTypeConstructor wrappedTy
          , mn == fromMaybe mn mn'
          -> do (inst, actualUnwrappedTy) <- deriveNewtype ss mn tyCon args unwrappedTy
                desugarCases inst >>= typeInstanceDictionary ss deps className [wrappedTy, actualUnwrappedTy]
          | otherwise -> throwError . errorMessage' ss $ ExpectedTypeConstructor className tys wrappedTy
        _ -> throwError . errorMessage' ss $ InvalidDerivedInstance className tys 2
    | className == Qualified (Just dataGenericRep) (ProperName C.generic)
    = case tys of
        [actualTy, repTy]
          | Just (Qualified mn' tyCon, args) <- unwrapTypeConstructor actualTy
          , mn == fromMaybe mn mn'
          -> do (inst, inferredRepTy) <- deriveGenericRep ss mn tyCon args repTy
                desugarCases inst >>= typeInstanceDictionary ss deps className [actualTy, inferredRepTy]
          | otherwise -> throwError . errorMessage' ss $ ExpectedTypeConstructor className tys actualTy
        _ -> throwError . errorMessage' ss $ InvalidDerivedInstance className tys 2
    | otherwise = throwError . errorMessage' ss $ CannotDerive className tys
  go NewtypeInstance =
    case tys of
      _ : _ | Just (Qualified mn' tyCon, args) <- unwrapTypeConstructor (last tys)
            , mn == fromMaybe mn mn'
            -> do dict <- deriveNewtypeInstance ss mn className tys tyCon args
                  let dictTy = foldl srcTypeApp (srcTypeConstructor (fmap (coerceProperName . dictSynonymName) className)) tys
                      constrainedTy = quantify (foldr (srcConstrainedType) dictTy deps)
                  return $ TypedValue True dict constrainedTy
            | otherwise -> throwError . errorMessage' ss $ ExpectedTypeConstructor className tys (last tys)
      _ -> throwError . errorMessage' ss $ InvalidNewtypeInstance className tys
  go (ExplicitInstance members) =
    desugarCases members >>= typeInstanceDictionary ss deps className tys

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
  getConstructors = everythingOnTypes (++) $ \case
    TypeConstructor _ tcname -> [tcname]
    _ -> []

  genSpan :: SourceSpan
  genSpan = internalModuleSourceSpan "<generated>"

unwrapTypeConstructor :: SourceType -> Maybe (Qualified (ProperName 'TypeName), [SourceType])
unwrapTypeConstructor = fmap (second reverse) . go
  where
  go (TypeConstructor _ tyCon) = Just (tyCon, [])
  go (TypeApp _ ty arg) = do
    (tyCon, args) <- go ty
    return (tyCon, arg : args)
  go _ = Nothing

typeInstanceDictionary
  :: forall m
   . MonadState CheckState m
  => MonadError MultipleErrors m
  => MonadSupply m
  => SourceSpan
  -> [SourceConstraint]
  -> Qualified (ProperName 'ClassName)
  -> [SourceType]
  -> [Declaration]
  -> m Expr
typeInstanceDictionary ss deps className tys decls =
  rethrow (addHint (ErrorInInstance className tys)) $ do
  env <- getEnv

  -- Lookup the type arguments and member types for the type class
  TypeClassData{..} <-
    maybe (throwError . errorMessage' ss . UnknownName $ fmap TyClassName className) return $
      M.lookup className (typeClasses env)

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
      return $ TypedValue True dict constrainedTy

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
