-- | This module implements the generic deriving elaboration that takes place during typechecking.
module Language.PureScript.TypeChecker.TypeClasses.Deriving
  ( dataEq
  , deriveEq
  , deriveEq1

  , dataOrd
  , deriveOrd
  , deriveOrd1

  , dataFunctor
  , deriveFunctor

  , dataNewtype
  , deriveNewtype

  , dataGenericRep
  , deriveGenericRep

  , deriveNewtypeInstance
  ) where

import           Prelude.Compat
import           Protolude (ordNub)

import           Control.Monad (replicateM, zipWithM, unless, when)
import           Control.Monad.Error.Class (MonadError(..))
import           Control.Monad.Writer.Class (MonadWriter(..))
import           Control.Monad.State.Class (MonadState)
import           Control.Monad.Supply.Class (MonadSupply)
import           Data.Foldable (for_)
import           Data.List (foldl', sortBy, unzip5)
import qualified Data.Map as M
import qualified Data.List.NonEmpty as NEL
import           Data.Ord (comparing)
import qualified Data.Set as S
import           Data.Text (Text)
import           Language.PureScript.AST
import qualified Language.PureScript.Constants.Prelude as C
import qualified Language.PureScript.Constants.Prim as C
import           Language.PureScript.Crash
import           Language.PureScript.Environment
import           Language.PureScript.Errors
import           Language.PureScript.Names
import           Language.PureScript.Label (Label(..))
import           Language.PureScript.PSString (mkString)
import           Language.PureScript.Types
import           Language.PureScript.TypeChecker.Monad
import           Language.PureScript.TypeChecker.Newtypes (checkNewtype)
import           Language.PureScript.TypeClassDictionaries

-- | When deriving an instance for a newtype, we must ensure that all superclass
-- instances were derived in the same way. This data structure is used to ensure
-- this property.
data NewtypeDerivedInstances = NewtypeDerivedInstances
  { ndiClasses :: M.Map (ModuleName, ProperName 'ClassName) ([Text], [SourceConstraint], [FunctionalDependency])
  -- ^ A list of superclass constraints for each type class. Since type classes
  -- have not been desugared here, we need to track this.
  , ndiDerivedInstances :: S.Set ((ModuleName, ProperName 'ClassName), (ModuleName, ProperName 'TypeName))
  -- ^ A list of newtype instances which were derived in this module.
  } deriving Show

instance Semigroup NewtypeDerivedInstances where
  x <> y =
    NewtypeDerivedInstances { ndiClasses          = ndiClasses          x <> ndiClasses          y
                            , ndiDerivedInstances = ndiDerivedInstances x <> ndiDerivedInstances y
                            }

instance Monoid NewtypeDerivedInstances where
  mempty = NewtypeDerivedInstances mempty mempty

-- | Extract the name of the newtype appearing in the last type argument of
-- a derived newtype instance.
--
-- Note: since newtypes in newtype instances can only be applied to type arguments
-- (no flexible instances allowed), we don't need to bother with unification when
-- looking for matching superclass instances, which saves us a lot of work. Instead,
-- we just match the newtype name.
extractNewtypeName :: ModuleName -> [SourceType] -> Maybe (ModuleName, ProperName 'TypeName)
extractNewtypeName _ [] = Nothing
extractNewtypeName mn xs = go (last xs) where
  go (TypeApp _ ty (TypeVar _ _)) = go ty
  go (TypeConstructor _ name) = Just (qualify mn name)
  go _ = Nothing

newtypeDerivedInstances :: MonadState CheckState m => ModuleName -> m NewtypeDerivedInstances
newtypeDerivedInstances moduleName = do
  env <- getEnv
  pure $ foldMap fromTypeClass (M.toList $ typeClasses env)
      <> foldMap fromTypeInstance (foldMap (foldMap (foldMap NEL.toList . M.elems) . M.elems) . M.elems $ typeClassDictionaries env)
  where
    fromTypeClass (qualifiedClassName, TypeClassData{..}) =
      NewtypeDerivedInstances (M.singleton (qualify moduleName qualifiedClassName) (map fst typeClassArguments, typeClassSuperclasses, typeClassDependencies)) mempty
    fromTypeInstance TypeClassDictionaryInScope{..} =
      foldMap (\name -> NewtypeDerivedInstances mempty (S.singleton (qualify moduleName tcdClassName, name))) (extractNewtypeName moduleName tcdInstanceTypes)

deriveNewtypeInstance
  :: forall m
   . (MonadState CheckState m, MonadError MultipleErrors m, MonadWriter MultipleErrors m)
  => SourceSpan
  -> ModuleName
  -> Qualified (ProperName 'ClassName)
  -> [SourceType]
  -> ProperName 'TypeName
  -> [SourceType]
  -> m Expr
deriveNewtypeInstance ss mn className tys tyConNm dargs = do
    verifySuperclasses
    tyCon <- lookupTypeDecl ss mn tyConNm
    go tyCon
  where
    go (Just Newtype, tyArgNames, [(_, [wrapped])]) = do
      -- The newtype might not be applied to all type arguments.
      -- This is okay as long as the newtype wraps something which ends with
      -- sufficiently many type applications to variables.
      -- For example, we can derive Functor for
      --
      -- newtype MyArray a = MyArray (Array a)
      --
      -- since Array a is a type application which uses the last
      -- type argument
      case stripRight (takeReverse (length tyArgNames - length dargs) tyArgNames) wrapped of
        Just wrapped' -> do
          let subst = zipWith (\(name, _) t -> (name, t)) tyArgNames dargs
          return (DeferredDictionary className (init tys ++ [replaceAllTypeVars subst wrapped']))
        Nothing -> throwError . errorMessage' ss $ InvalidNewtypeInstance className tys
    go _ = throwError . errorMessage' ss $ InvalidNewtypeInstance className tys

    takeReverse :: Int -> [a] -> [a]
    takeReverse n = take n . reverse

    stripRight :: [(Text, Maybe kind)] -> SourceType -> Maybe SourceType
    stripRight [] ty = Just ty
    stripRight ((arg, _) : args) (TypeApp _ t (TypeVar _ arg'))
      | arg == arg' = stripRight args t
    stripRight _ _ = Nothing

    verifySuperclasses :: m ()
    verifySuperclasses = do
      NewtypeDerivedInstances{..} <- newtypeDerivedInstances mn
      for_ (M.lookup (qualify mn className) ndiClasses) $ \(args, superclasses, _) ->
        for_ superclasses $ \Constraint{..} -> do
          let constraintClass' = qualify (error "verifySuperclasses: unknown class module") constraintClass
          for_ (M.lookup constraintClass' ndiClasses) $ \(_, _, deps) ->
            -- We need to check whether the newtype is mentioned, because of classes like MonadWriter
            -- with its Monoid superclass constraint.
            when (not (null args) && any ((last args `elem`) . usedTypeVariables) constraintArgs) $ do
              -- For now, we only verify superclasses where the newtype is the only argument,
              -- or for which all other arguments are determined by functional dependencies.
              -- Everything else raises a UnverifiableSuperclassInstance warning.
              -- This covers pretty much all cases we're interested in, but later we might want to do
              -- more work to extend this to other superclass relationships.
              let determined = map (srcTypeVar . (args !!)) . ordNub . concatMap fdDetermined . filter ((== [length args - 1]) . fdDeterminers) $ deps
              if eqType (last constraintArgs) (srcTypeVar (last args)) && all (`elem` determined) (init constraintArgs)
                then do
                  -- Now make sure that a superclass instance was derived. Again, this is not a complete
                  -- check, since the superclass might have multiple type arguments, so overlaps might still
                  -- be possible, so we warn again.
                  for_ (extractNewtypeName mn tys) $ \nm ->
                    unless ((constraintClass', nm) `S.member` ndiDerivedInstances) $
                      tell . errorMessage' ss $ MissingNewtypeSuperclassInstance constraintClass className tys
                else tell . errorMessage' ss $ UnverifiableSuperclassInstance constraintClass className tys

unguarded :: Expr -> [GuardedExpr]
unguarded e = [MkUnguarded e]

dataGenericRep :: ModuleName
dataGenericRep = ModuleName "Data.Generic.Rep"

deriveGenericRep
  :: forall m
   . (MonadState CheckState m, MonadError MultipleErrors m, MonadSupply m)
  => SourceSpan
  -> ModuleName
  -> ProperName 'TypeName
  -> [SourceType]
  -> SourceType
  -> m ([Declaration], SourceType)
deriveGenericRep ss mn tyConNm tyConArgs repTy = do
    checkIsWildcard ss tyConNm repTy
    go =<< lookupTypeDecl ss mn tyConNm
  where
    go :: (Maybe DataDeclType, [(Text, Maybe SourceType)], [(ProperName 'ConstructorName, [SourceType])]) -> m ([Declaration], SourceType)
    go (_, args, dctors) = do
      x <- freshIdent "x"
      (reps, to, from) <- unzip3 <$> traverse makeInst dctors
      let rep = toRepTy reps
          inst | null reps =
                   -- If there are no cases, spin
                   [ ValueDecl (ss, []) (Ident "to") Public [] $ unguarded $
                      lamCase ss x
                        [ CaseAlternative
                            [NullBinder]
                            (unguarded (App toName (Var ss (Qualified Nothing x))))
                        ]
                   , ValueDecl (ss, []) (Ident "from") Public [] $ unguarded $
                      lamCase ss x
                        [ CaseAlternative
                            [NullBinder]
                            (unguarded (App fromName (Var ss (Qualified Nothing x))))
                        ]
                   ]
               | otherwise =
                   [ ValueDecl (ss, []) (Ident "to") Public [] $ unguarded $
                       lamCase ss x (zipWith ($) (map underBinder (sumBinders (length dctors))) to)
                   , ValueDecl (ss, []) (Ident "from") Public [] $ unguarded $
                       lamCase ss x (zipWith ($) (map underExpr (sumExprs (length dctors))) from)
                   ]

          subst = zipWith ((,) . fst) args tyConArgs
      return (inst, replaceAllTypeVars subst rep)

    select :: (a -> a) -> (a -> a) -> Int -> [a -> a]
    select _ _ 0 = []
    select _ _ 1 = [id]
    select l r n = take (n - 1) (iterate (r .) l) ++ [compN (n - 1) r]

    sumBinders :: Int -> [Binder -> Binder]
    sumBinders = select (ConstructorBinder ss inl . pure) (ConstructorBinder ss inr . pure)

    sumExprs :: Int -> [Expr -> Expr]
    sumExprs = select (App (Constructor ss inl)) (App (Constructor ss inr))

    compN :: Int -> (a -> a) -> a -> a
    compN 0 _ = id
    compN n f = f . compN (n - 1) f

    makeInst
      :: (ProperName 'ConstructorName, [SourceType])
      -> m (SourceType, CaseAlternative, CaseAlternative)
    makeInst (ctorName, args) = do
        (ctorTy, matchProduct, ctorArgs, matchCtor, mkProduct) <- makeProduct args
        return ( srcTypeApp (srcTypeApp (srcTypeConstructor constructor)
                                  (srcTypeLevelString $ mkString (runProperName ctorName)))
                         ctorTy
               , CaseAlternative [ ConstructorBinder ss constructor [matchProduct] ]
                                 (unguarded (foldl' App (Constructor ss (Qualified (Just mn) ctorName)) ctorArgs))
               , CaseAlternative [ ConstructorBinder ss (Qualified (Just mn) ctorName) matchCtor ]
                                 (unguarded (constructor' mkProduct))
               )

    makeProduct
      :: [SourceType]
      -> m (SourceType, Binder, [Expr], [Binder], Expr)
    makeProduct [] =
      pure (noArgs, NullBinder, [], [], noArgs')
    makeProduct args = do
      (tys, bs1, es1, bs2, es2) <- unzip5 <$> traverse makeArg args
      pure ( foldr1 (\f -> srcTypeApp (srcTypeApp (srcTypeConstructor productName) f)) tys
           , foldr1 (\b1 b2 -> ConstructorBinder ss productName [b1, b2]) bs1
           , es1
           , bs2
           , foldr1 (\e1 -> App (App (Constructor ss productName) e1)) es2
           )

    makeArg :: SourceType -> m (SourceType, Binder, Expr, Binder, Expr)
    makeArg arg = do
      argName <- freshIdent "arg"
      pure ( srcTypeApp (srcTypeConstructor argument) arg
           , ConstructorBinder ss argument [ VarBinder ss argName ]
           , Var ss (Qualified Nothing argName)
           , VarBinder ss argName
           , argument' (Var ss (Qualified Nothing argName))
           )

    underBinder :: (Binder -> Binder) -> CaseAlternative -> CaseAlternative
    underBinder f (CaseAlternative bs e) = CaseAlternative (map f bs) e

    underExpr :: (Expr -> Expr) -> CaseAlternative -> CaseAlternative
    underExpr f (CaseAlternative b [MkUnguarded e]) = CaseAlternative b (unguarded (f e))
    underExpr _ _ = internalError "underExpr: expected unguarded alternative"

    toRepTy :: [SourceType] -> SourceType
    toRepTy [] = noCtors
    toRepTy [only] = only
    toRepTy ctors = foldr1 (\f -> srcTypeApp (srcTypeApp sumCtor f)) ctors

    toName :: Expr
    toName = Var ss (Qualified (Just dataGenericRep) (Ident "to"))

    fromName :: Expr
    fromName = Var ss (Qualified (Just dataGenericRep) (Ident "from"))

    noCtors :: SourceType
    noCtors = srcTypeConstructor (Qualified (Just dataGenericRep) (ProperName "NoConstructors"))

    noArgs :: SourceType
    noArgs = srcTypeConstructor (Qualified (Just dataGenericRep) (ProperName "NoArguments"))

    noArgs' :: Expr
    noArgs' = Constructor ss (Qualified (Just dataGenericRep) (ProperName "NoArguments"))

    sumCtor :: SourceType
    sumCtor = srcTypeConstructor (Qualified (Just dataGenericRep) (ProperName "Sum"))

    inl :: Qualified (ProperName 'ConstructorName)
    inl = Qualified (Just dataGenericRep) (ProperName "Inl")

    inr :: Qualified (ProperName 'ConstructorName)
    inr = Qualified (Just dataGenericRep) (ProperName "Inr")

    productName :: Qualified (ProperName ty)
    productName = Qualified (Just dataGenericRep) (ProperName "Product")

    constructor :: Qualified (ProperName ty)
    constructor = Qualified (Just dataGenericRep) (ProperName "Constructor")

    constructor' :: Expr -> Expr
    constructor' = App (Constructor ss constructor)

    argument :: Qualified (ProperName ty)
    argument = Qualified (Just dataGenericRep) (ProperName "Argument")

    argument' :: Expr -> Expr
    argument' = App (Constructor ss argument)

checkIsWildcard :: MonadError MultipleErrors m => SourceSpan -> ProperName 'TypeName -> SourceType -> m ()
checkIsWildcard _ _ (TypeWildcard _ Nothing) = return ()
checkIsWildcard ss tyConNm _ =
  throwError . errorMessage' ss $ ExpectedWildcard tyConNm

dataEq :: ModuleName
dataEq = ModuleName "Data.Eq"

deriveEq
  :: forall m
   . (MonadState CheckState m, MonadError MultipleErrors m, MonadSupply m)
  => SourceSpan
  -> ModuleName
  -> ProperName 'TypeName
  -> m [Declaration]
deriveEq ss mn tyConNm = do
  tyCon <- lookupTypeDecl ss mn tyConNm
  eqFun <- mkEqFunction tyCon
  return [ ValueDecl (ss, []) (Ident C.eq) Public [] (unguarded eqFun) ]
  where
    mkEqFunction :: (Maybe DataDeclType, [(Text, Maybe SourceType)], [(ProperName 'ConstructorName, [SourceType])]) -> m Expr
    mkEqFunction (_, _, ctors) = do
      x <- freshIdent "x"
      y <- freshIdent "y"
      lamCase2 ss x y <$> (addCatch <$> mapM mkCtorClause ctors)

    preludeConj :: Expr -> Expr -> Expr
    preludeConj = App . App (Var ss (Qualified (Just (ModuleName "Data.HeytingAlgebra")) (Ident C.conj)))

    preludeEq :: Expr -> Expr -> Expr
    preludeEq = App . App (Var ss (Qualified (Just dataEq) (Ident C.eq)))

    preludeEq1 :: Expr -> Expr -> Expr
    preludeEq1 = App . App (Var ss (Qualified (Just dataEq) (Ident C.eq1)))

    addCatch :: [CaseAlternative] -> [CaseAlternative]
    addCatch xs
      | length xs /= 1 = xs ++ [catchAll]
      | otherwise = xs -- Avoid redundant case
      where
      catchAll = CaseAlternative [NullBinder, NullBinder] (unguarded (Literal ss (BooleanLiteral False)))

    mkCtorClause :: (ProperName 'ConstructorName, [SourceType]) -> m CaseAlternative
    mkCtorClause (ctorName, tys) = do
      identsL <- replicateM (length tys) (freshIdent "l")
      identsR <- replicateM (length tys) (freshIdent "r")
      let tests = zipWith3 toEqTest (map (Var ss . Qualified Nothing) identsL) (map (Var ss . Qualified Nothing) identsR) tys
      return $ CaseAlternative [caseBinder identsL, caseBinder identsR] (unguarded (conjAll tests))
      where
      caseBinder idents = ConstructorBinder ss (Qualified (Just mn) ctorName) (map (VarBinder ss) idents)

    conjAll :: [Expr] -> Expr
    conjAll [] = Literal ss (BooleanLiteral True)
    conjAll xs = foldl1 preludeConj xs

    toEqTest :: Expr -> Expr -> SourceType -> Expr
    toEqTest l r ty
      | Just rec <- objectType ty
      , Just fields <- decomposeRec rec =
          conjAll
          . map (\((Label str), typ) -> toEqTest (Accessor str l) (Accessor str r) typ)
          $ fields
      | isAppliedVar ty = preludeEq1 l r
      | otherwise = preludeEq l r

deriveEq1 :: SourceSpan -> [Declaration]
deriveEq1 ss =
  [ ValueDecl (ss, []) (Ident C.eq1) Public [] (unguarded preludeEq)]
  where
    preludeEq :: Expr
    preludeEq = Var ss (Qualified (Just dataEq) (Ident C.eq))

dataOrd :: ModuleName
dataOrd = ModuleName "Data.Ord"

deriveOrd
  :: forall m
   . (MonadState CheckState m, MonadError MultipleErrors m, MonadSupply m)
  => SourceSpan
  -> ModuleName
  -> ProperName 'TypeName
  -> m [Declaration]
deriveOrd ss mn tyConNm = do
  tyCon <- lookupTypeDecl ss mn tyConNm
  compareFun <- mkCompareFunction tyCon
  return [ ValueDecl (ss, []) (Ident C.compare) Public [] (unguarded compareFun) ]
  where
    mkCompareFunction :: (Maybe DataDeclType, [(Text, Maybe SourceType)], [(ProperName 'ConstructorName, [SourceType])]) -> m Expr
    mkCompareFunction (_, _, ctors) = do
      x <- freshIdent "x"
      y <- freshIdent "y"
      lamCase2 ss x y <$> (addCatch . concat <$> mapM mkCtorClauses (splitLast ctors))

    splitLast :: [a] -> [(a, Bool)]
    splitLast [] = []
    splitLast [x] = [(x, True)]
    splitLast (x : xs) = (x, False) : splitLast xs

    addCatch :: [CaseAlternative] -> [CaseAlternative]
    addCatch xs
      | null xs = [catchAll] -- No type constructors
      | otherwise = xs
      where
      catchAll = CaseAlternative [NullBinder, NullBinder] (unguarded (orderingCtor "EQ"))

    orderingName :: Text -> Qualified (ProperName a)
    orderingName = Qualified (Just (ModuleName "Data.Ordering")) . ProperName

    orderingCtor :: Text -> Expr
    orderingCtor = Constructor ss . orderingName

    orderingBinder :: Text -> Binder
    orderingBinder name = ConstructorBinder ss (orderingName name) []

    ordCompare :: Expr -> Expr -> Expr
    ordCompare = App . App (Var ss (Qualified (Just dataOrd) (Ident C.compare)))

    ordCompare1 :: Expr -> Expr -> Expr
    ordCompare1 = App . App (Var ss (Qualified (Just dataOrd) (Ident C.compare1)))

    mkCtorClauses :: ((ProperName 'ConstructorName, [SourceType]), Bool) -> m [CaseAlternative]
    mkCtorClauses ((ctorName, tys), isLast) = do
      identsL <- replicateM (length tys) (freshIdent "l")
      identsR <- replicateM (length tys) (freshIdent "r")
      let tests = zipWith3 toOrdering (map (Var ss . Qualified Nothing) identsL) (map (Var ss . Qualified Nothing) identsR) tys
          extras | not isLast = [ CaseAlternative [ ConstructorBinder ss (Qualified (Just mn) ctorName) (replicate (length tys) NullBinder)
                                                  , NullBinder
                                                  ]
                                                  (unguarded (orderingCtor "LT"))
                                , CaseAlternative [ NullBinder
                                                  , ConstructorBinder ss (Qualified (Just mn) ctorName) (replicate (length tys) NullBinder)
                                                  ]
                                                  (unguarded (orderingCtor "GT"))
                                ]
                 | otherwise = []
      return $ CaseAlternative [ caseBinder identsL
                               , caseBinder identsR
                               ]
                               (unguarded (appendAll tests))
             : extras

      where
      caseBinder idents = ConstructorBinder ss (Qualified (Just mn) ctorName) (map (VarBinder ss) idents)

    appendAll :: [Expr] -> Expr
    appendAll [] = orderingCtor "EQ"
    appendAll [x] = x
    appendAll (x : xs) = Case [x] [ CaseAlternative [orderingBinder "LT"]
                                                    (unguarded (orderingCtor "LT"))
                                  , CaseAlternative [orderingBinder "GT"]
                                                    (unguarded (orderingCtor "GT"))
                                  , CaseAlternative [ NullBinder ]
                                                    (unguarded (appendAll xs))
                                  ]

    toOrdering :: Expr -> Expr -> SourceType -> Expr
    toOrdering l r ty
      | Just rec <- objectType ty
      , Just fields <- decomposeRec rec =
          appendAll
          . map (\((Label str), typ) -> toOrdering (Accessor str l) (Accessor str r) typ)
          $ fields
      | isAppliedVar ty = ordCompare1 l r
      | otherwise = ordCompare l r

deriveOrd1 :: SourceSpan -> [Declaration]
deriveOrd1 ss =
  [ ValueDecl (ss, []) (Ident C.compare1) Public [] (unguarded dataOrdCompare)]
  where
    dataOrdCompare :: Expr
    dataOrdCompare = Var ss (Qualified (Just dataOrd) (Ident C.compare))

dataNewtype :: ModuleName
dataNewtype = ModuleName "Data.Newtype"

deriveNewtype
  :: forall m
   . (MonadState CheckState m, MonadError MultipleErrors m, MonadSupply m)
  => SourceSpan
  -> ModuleName
  -> ProperName 'TypeName
  -> [SourceType]
  -> SourceType
  -> m ([Declaration], SourceType)
deriveNewtype ss mn tyConNm tyConArgs unwrappedTy = do
    checkIsWildcard ss tyConNm unwrappedTy
    go =<< lookupTypeDecl ss mn tyConNm
  where
    go :: (Maybe DataDeclType, [(Text, Maybe SourceType)], [(ProperName 'ConstructorName, [SourceType])]) -> m ([Declaration], SourceType)
    go (Just Newtype, args, dctors) = do
      checkNewtype tyConNm dctors
      wrappedIdent <- freshIdent "n"
      unwrappedIdent <- freshIdent "a"
      let (ctorName, [ty]) = head dctors
      let inst =
            [ ValueDecl (ss, []) (Ident "wrap") Public [] $ unguarded $
                Constructor ss (Qualified (Just mn) ctorName)
            , ValueDecl (ss, []) (Ident "unwrap") Public [] $ unguarded $
                lamCase ss wrappedIdent
                  [ CaseAlternative
                      [ConstructorBinder ss (Qualified (Just mn) ctorName) [VarBinder ss unwrappedIdent]]
                      (unguarded (Var ss (Qualified Nothing unwrappedIdent)))
                  ]
            ]
          subst = zipWith ((,) . fst) args tyConArgs
      return (inst, replaceAllTypeVars subst ty)
    go _ = throwError . errorMessage' ss $ CannotDeriveNewtypeForData tyConNm

lookupTypeDecl :: (MonadState CheckState m, MonadError MultipleErrors m)
  => SourceSpan
  -> ModuleName
  -> ProperName 'TypeName
  -> m (Maybe DataDeclType, [(Text, Maybe SourceType)], [(ProperName 'ConstructorName, [SourceType])])
lookupTypeDecl ss moduleName typeName = do
  env <- getEnv
  maybe (throwError . errorMessage' ss $ CannotFindDerivingType typeName) pure $ do
    (_, DataType args dctors) <- M.lookup (Qualified (Just moduleName) typeName) (types env)
    pure ( (\(dtype, _, _, _) -> dtype) <$> case dctors of
              (ctorName, _) : _ ->
                M.lookup (Qualified (Just moduleName) ctorName) (dataConstructors env)
              _ -> Nothing
         , map (\(v, k, _) -> (v, k)) args
         , dctors
         )

lam :: SourceSpan -> Ident -> Expr -> Expr
lam ss = Abs . VarBinder ss

lamCase :: SourceSpan -> Ident -> [CaseAlternative] -> Expr
lamCase ss s = lam ss s . Case [mkVar ss s]

lamCase2 :: SourceSpan -> Ident -> Ident -> [CaseAlternative] -> Expr
lamCase2 ss s t = lam ss s . lam ss t . Case [mkVar ss s, mkVar ss t]

mkVarMn :: SourceSpan -> Maybe ModuleName -> Ident -> Expr
mkVarMn ss mn = Var ss . Qualified mn

mkVar :: SourceSpan -> Ident -> Expr
mkVar ss = mkVarMn ss Nothing

isAppliedVar :: Type a -> Bool
isAppliedVar (TypeApp _ (TypeVar _ _) _) = True
isAppliedVar _ = False

objectType :: Type a -> Maybe (Type a)
objectType (TypeApp _ (TypeConstructor _ C.Record) rec) = Just rec
objectType _ = Nothing

decomposeRec :: SourceType -> Maybe [(Label, SourceType)]
decomposeRec = fmap (sortBy (comparing fst)) . go
  where go (RCons _ str typ typs) = fmap ((str, typ) :) (go typs)
        go (REmptyKinded _ _) = Just []
        go _ = Nothing

decomposeRec' :: SourceType -> [(Label, SourceType)]
decomposeRec' = sortBy (comparing fst) . go
  where go (RCons _ str typ typs) = (str, typ) : go typs
        go _ = []

dataFunctor :: ModuleName
dataFunctor = ModuleName "Data.Functor"

deriveFunctor
  :: forall m
   . (MonadState CheckState m, MonadError MultipleErrors m, MonadSupply m)
  => SourceSpan
  -> ModuleName
  -> ProperName 'TypeName
  -> m [Declaration]
deriveFunctor ss mn tyConNm = do
  tyCon <- lookupTypeDecl ss mn tyConNm
  mapFun <- mkMapFunction tyCon
  return [ ValueDecl (ss, []) (Ident C.map) Public [] (unguarded mapFun) ]
  where
    mkMapFunction :: (Maybe DataDeclType, [(Text, Maybe SourceType)], [(ProperName 'ConstructorName, [SourceType])]) -> m Expr
    mkMapFunction (_, tys, ctors) = case reverse tys of
      [] -> throwError . errorMessage' ss $ KindsDoNotUnify (kindType -:> kindType) kindType
      ((iTy, _) : _) -> do
        f <- freshIdent "f"
        m <- freshIdent "m"
        lam ss f . lamCase ss m <$> mapM (mkCtorClause iTy f) ctors

    mkCtorClause :: Text -> Ident -> (ProperName 'ConstructorName, [SourceType]) -> m CaseAlternative
    mkCtorClause iTyName f (ctorName, ctorTys) = do
      idents <- replicateM (length ctorTys) (freshIdent "v")
      args <- zipWithM transformArg idents ctorTys
      let ctor = Constructor ss (Qualified (Just mn) ctorName)
          rebuilt = foldl' App ctor args
          caseBinder = ConstructorBinder ss (Qualified (Just mn) ctorName) (VarBinder ss <$> idents)
      return $ CaseAlternative [caseBinder] (unguarded rebuilt)
      where
        fVar = mkVar ss f
        mapVar = mkVarMn ss (Just dataFunctor) (Ident C.map)

        transformArg :: Ident -> SourceType -> m Expr
        transformArg ident = fmap (foldr App (mkVar ss ident)) . goType where

          goType :: SourceType -> m (Maybe Expr)
          -- argument matches the index type
          goType (TypeVar _ t) | t == iTyName = return (Just fVar)

          -- records
          goType recTy | Just row <- objectType recTy =
              traverse buildUpdate (decomposeRec' row) >>= (traverse buildRecord . justUpdates)
            where
              justUpdates :: [Maybe (Label, Expr)] -> Maybe [(Label, Expr)]
              justUpdates = foldMap (fmap return)

              buildUpdate :: (Label, SourceType) -> m (Maybe (Label, Expr))
              buildUpdate (lbl, ty) = do upd <- goType ty
                                         return ((lbl,) <$> upd)

              buildRecord :: [(Label, Expr)] -> m Expr
              buildRecord updates = do
                arg <- freshIdent "o"
                let argVar = mkVar ss arg
                    mkAssignment ((Label l), x) = (l, App x (Accessor l argVar))
                return (lam ss arg (ObjectUpdate argVar (mkAssignment <$> updates)))

          -- quantifiers
          goType (ForAll _ scopedVar _ t _) | scopedVar /= iTyName = goType t

          -- constraints
          goType (ConstrainedType _ _ t) = goType t

          -- under a `* -> *`, just assume functor for now
          goType (TypeApp _ _ t) = fmap (App mapVar) <$> goType t

          -- otherwise do nothing - will fail type checking if type does actually contain index
          goType _ = return Nothing
