{-# LANGUAGE TypeApplications #-}

module Language.PureScript.Sugar.AnonymousTypeInstances
  ( desugarAnonymousTypeInstancesModule
  ) where

import Prelude

import Control.Monad.State (MonadState, evalState, gets, modify, runState)
import Data.Map (Map)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Set (Set)
import Data.Text (Text)

import qualified Data.Char as Char
import qualified Data.Map as Map
import qualified Data.Text as Text

import Language.PureScript.AST
import Language.PureScript.Names
import Language.PureScript.PSString (decodeString)
import Language.PureScript.Types

data DesugarState =
  DesugarState
    { desugaredTypeInstances :: Map Text Integer
    }

data RenameState =
  RenameState
    { duplicateInstancesNames :: Set Text
    , renamedTypeInstances :: Map Text Integer
    }

desugarAnonymousTypeInstancesModule :: Module -> Module
desugarAnonymousTypeInstancesModule (Module ss comments moduleName decls exports) =
  let (desugared, DesugarState{..}) = traverse desugarAnonymousTypeInstance decls `runState` DesugarState mempty
      duplicateInstancesNames = Map.keysSet $ Map.filter (>1) desugaredTypeInstances
      renamed = renameImplicitTypeInstance desugared `evalState` RenameState duplicateInstancesNames mempty
  in Module ss comments moduleName renamed exports
  where
  desugarAnonymousTypeInstance (TypeInstanceDeclaration sa chain idx AnonymousTypeInstance constraints className tys body) = do
    name <- implicitTypeInstanceName className tys
    pure $ TypeInstanceDeclaration sa chain idx name constraints className tys body
  desugarAnonymousTypeInstance (DataDeclaration sa dtype name args dctors insts) =
    DataDeclaration sa dtype name args dctors <$> traverse desugarDerivedTypeInstances insts
  desugarAnonymousTypeInstance decl = pure decl

  desugarDerivedTypeInstances (DataDerivedTypeInstancesDeclaration sa strategy instances) =
    DataDerivedTypeInstancesDeclaration sa strategy <$> traverse desugarDerivedTypeInstance instances

  desugarDerivedTypeInstance (DataDerivedTypeInstance sa AnonymousTypeInstance className tys) = do
    name <- implicitTypeInstanceName className tys
    pure $ DataDerivedTypeInstance sa name className tys
  desugarDerivedTypeInstance inst = pure inst

  ƒ (instanceChainHead@TypeInstanceDeclaration{} : decls') = do
    let (instanceChainTail, rest) = span isChainedTypeInstance decls'
    renamedInstanceChain <- renameInstanceChain $ instanceChainHead : instanceChainTail
    rest' <- ƒ rest
    pure $ relinkInstanceChain renamedInstanceChain <> rest'
  ƒ (decl : decls') =
    (:) <$> renameDataDeclaration decl <*> ƒ decls'
  ƒ [] = pure $ []

  isChainedTypeInstance (TypeInstanceDeclaration _ _ idx _ _ _ _ _) = idx > 0
  isChainedTypeInstance _ = False

  renameInstanceChain instances = do
    hasDuplicateInstances <- gets $ not . null . duplicateInstancesNames
    if hasDuplicateInstances
      then traverse renameTypeInstance instances
      else pure instances

  renameTypeInstance (decl@(TypeInstanceDeclaration sa chain idx (ImplicitTypeInstanceName (Escaped name)) constraints className tys body)) = do
    name' <- rename name
    pure $ TypeInstanceDeclaration sa chain idx (ImplicitTypeInstanceName $ Escaped name') constraints className tys body
  renameTypeInstance decl = pure decl

  renameDataDeclaration (DataDeclaration sa dtype name args dctors insts) =
    DataDeclaration sa dtype name args dctors <$> traverse renameDerivedTypeInstances insts
  renameDataDeclaration decl = pure decl

  renameDerivedTypeInstances (DataDerivedTypeInstancesDeclaration sa strategy instances) =
    DataDerivedTypeInstancesDeclaration sa strategy <$> traverse renameDerivedTypeInstance instances

  renameDerivedTypeInstance (DataDerivedTypeInstance sa (ImplicitTypeInstanceName (Escaped name)) className tys) = do
    name' <- rename name
    pure $ DataDerivedTypeInstance sa (ImplicitTypeInstanceName (Escaped name')) className tys
  renameDerivedTypeInstance inst = pure inst

  rename name = do
    duplicate <- gets ((name `elem`) . duplicateInstancesNames)
    if duplicate then do
      n <- gets $ fromMaybe 0 . Map.lookup name . renamedTypeInstances
      modify (\st -> st { renamedTypeInstances = Map.insert name (n + 1) $ renamedTypeInstances st })
      pure $ name <> "_" <> Text.pack (show n)
    else pure name

  relinkInstanceChain instances =
    relinkTypeInstance (mapMaybe getTypeInstanceDeclarationName instances) <$> instances

  getTypeInstanceDeclarationName (TypeInstanceDeclaration _ _ _ name _ _ _ _) = Just name
  getTypeInstanceDeclarationName _ = Nothing

  relinkTypeInstance chain' (TypeInstanceDeclaration sa _ idx name constraints className tys body) =
    TypeInstanceDeclaration sa chain' idx name constraints className tys body
  relinkTypeInstance _ decl = decl

implicitTypeInstanceName
  :: MonadState DesugarState m
  => Qualified (ProperName 'ClassName)
  -> [SourceType]
  -> m TypeInstanceName
implicitTypeInstanceName className tys = do
  let className' = fromQualifiedName className
      tys' = mapMaybe typeInstanceArgumentName tys
      name = "$" <> Text.intercalate "$$" (className' : tys')
  modify (\st -> st { desugaredTypeInstances = Map.unionWith (+) (Map.singleton name 1) $ desugaredTypeInstances st })
  pure $ ImplicitTypeInstanceName (Escaped name)
  where
  fromQualifiedName =
    Text.replace "." "_" . showQualified (Text.replace "'" "$prime" . runProperName)
  appendAlphaNumChar symbol c =
    symbol <> if Char.isAlphaNum c || c == '_' then Just (Text.singleton c) else Nothing

  typeInstanceArgumentName ty =
    let (ty', args) = unapply ty
        name = Text.intercalate "$" $
             foldMap pure (unappliedTypeName ty')
          <> mapMaybe typeInstanceArgumentName args
    in if Text.null name then Nothing else Just name

  unapply = go [] where
    go args = \case
      TypeApp _ ty arg -> go (arg : args) ty
      ParensInType _ ty -> go args ty
      BinaryNoParensType _ op lhs rhs -> go (lhs : rhs : args) op
      ty -> (ty, args)

  unappliedTypeName = \case
    TypeConstructor _ qualName ->
      Just $ fromQualifiedName qualName
    TypeLevelString _ symbol -> do
      symbol' <- decodeString symbol
      ("sym$" <>) <$> Text.foldl appendAlphaNumChar Nothing symbol'
    _ -> Nothing
