{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Eval (
    eval
  , eval'
  , evalStmt
  , runEval
  , runEval'
  , withConstraint
  , unconstrained
  , Equals(..)
) where

import Control.Monad.State
import Data.List (sortBy)

import Language.MinPS.Syntax
import Language.MinPS.Environment
import Language.MinPS.Value

eval :: MonadState Env m => CTerm -> m Value
eval = eval' . emptyC

eval' :: MonadState Env m => Closure (CTerm) -> m Value
eval' (CLet ctxt t :@ c) = do
  c' <- evalContext ctxt c
  eval' (t :@ c')

eval' (CType :@ _) = pure VType

eval' (CVar x :@ c)
  | Just i <- lookup x c = do
      env <- get
      case lookupE i env of
        Just (EnvEntry _ _ (Right t)) -> eval' t
    -- a horrible hack; we're going to rely on the typechecker to never
    --   give us "truly undefined" bindings; however, we will, in normalisation
    --   and equality checking
    --   need a way to mark variables which should "normalize to themselves";
    --   e.g. variables introduced by binders in pi or sigma types
    --   note that i usually, but not always, == j
    --   (it might get repointed in the course of equality checking)
        Just (EnvEntry _ _ (Left j)) -> evalNeutral $ NVar j
        Nothing -> error "ICE: undeclared variable passed check"
  | otherwise = error "ICE: unbound variable passed check"

eval' (CPi x ty t :@ c) = pure $ VPi x ((ty, t) :@ c)
eval' (CSigma x ty t :@ c) = pure $ VSigma x ((ty, t) :@ c)
eval' (CLam x t :@ c) = pure $ VLam x (t :@ c)
eval' (CPair t u :@ c) = pure $ VPair ((t, u) :@ c)
eval' (CEnum lbls :@ _) = pure $ VEnum lbls
eval' (CEnumLabel lbl :@ _) = pure $ VEnumLabel lbl
eval' (CLift t :@ c) = pure $ VLift (t :@ c)
eval' (CBox t :@ c) = pure $ VBox (t :@ c)
eval' (CRec t :@ c) = pure $ VRec (t :@ c)
eval' (CFold t :@ c) = pure $ VFold (t :@ c)

eval' (CApp f x :@ c) = eval' (f :@ c) >>= \case
  VNeutral n -> evalNeutral $ NApp n (x :@ c)
  VLam v (body :@ c') -> do
    i <- declareE v Nothing
    defineE i (x :@ c)
    eval' (body :@ (v, i):c')
  v -> errorV v "ICE: invalid application passed check"

eval' (CSplit t x y u :@ c) = eval' (t :@ c) >>= \case
  VNeutral n -> evalNeutral $ NSplit n x y (u :@ c)
  VPair ((t1, t2) :@ c') -> do
    iX <- declareE x Nothing
    defineE iX (t1 :@ c')
    iY <- declareE y Nothing
    defineE iY (t2 :@ c')
    eval' (u :@ (y, iY):(x, iX):c)
  v -> errorV v "ICE: invalid split passed check"

eval' (CCase t cases :@ c) = eval' (t :@ c) >>= \case
  VNeutral n -> evalNeutral $ NCase n (cases :@ c)
  VEnumLabel l -> case lookup l cases of
    Just u -> eval' (u :@ c)
    Nothing -> error "ICE: invalid case passed check"
  v -> errorV v "ICE: invalid case passed check"

eval' (CForce t :@ c) = eval' (t :@ c) >>= \case
  VNeutral n -> evalNeutral $ NForce n
  VBox t' -> eval' t'
  v -> errorV v "ICE: invalid force passed check"

eval' (CUnfold t x u :@ c) = eval' (t :@ c) >>= \case
  VNeutral n -> evalNeutral $ NUnfold n x (u :@ c)
  VFold t' -> do
    i <- declareE x Nothing
    defineE i t'
    eval' (u :@ (x, i):c)
  v -> errorV v "ICE: invalid unfold passed check"

errorV :: Value -> String -> a
errorV v s = error $ s ++ ": " ++ show v

evalStmt :: MonadState Env m => Stmt 'Checked -> Scope -> m Scope
evalStmt (Declare x ty) c = do
  i <- declareE x $ Just (ty :@ c)
  pure ((x, i):c)
evalStmt (Define x t) c = case lookup x c of
  Just i -> do
    defineE i (t :@ c)
    pure c
  _ -> error "ICE: define-without-declare passed check"
evalStmt (DeclareDefine x ty t) c =
  evalStmt (Declare x ty) c >>= evalStmt (Define x t)

evalContext :: MonadState Env m => Context 'Checked -> Scope -> m Scope
evalContext [] c = pure c
evalContext (stmt:rest) c = do
  c' <- evalStmt stmt c
  evalContext rest c'

runEval :: Env -> CTerm -> Value
runEval e t = evalState (eval t) e

runEval' :: Env -> Closure (CTerm) -> Value
runEval' e t = evalState (eval' t) e

withConstraint :: MonadState Env m
               => Closure (CTerm)
               -> Label
               -> m a
               -> m a
withConstraint t l m = gets getConstraints >>= \case
  Inconsistent -> m
  Constraints cs -> do
    v <- eval' t
    case v of
      VEnumLabel l' -> if l == l'
        then m
        else locally $ modify (setConstraints Inconsistent) >> m
      VNeutral n -> locally $ do
        modify (setConstraints $ Constraints $ (n, l):cs)
        m
      _ -> error "ICE: withConstraint on invalid term!"

unconstrained :: MonadState Env m => m a -> m a
unconstrained = locally . ((modify (setConstraints $ Constraints [])) >>)

-- something something constraints?
evalNeutral :: MonadState Env m => Neutral -> m Value
evalNeutral n = do
  consts <- gets getConstraints
  case consts of
    Constraints cs -> go cs
    Inconsistent ->
      error "ICE: evalNeutral called with inconsistent constraints"
  where
    go [] = pure $ VNeutral n
    go ((n', l):rest) = do
      eq <- n .=. n'
      if eq
        then pure $ VEnumLabel l
        else go rest

class Equals a where
  (.=.) :: MonadState Env m => a -> a -> m Bool
infix 3 .=.

instance Equals Value where
  VPi x ((tyX, t) :@ c) .=. VPi y ((tyY, u) :@ d) = do
    eqTy <- join $ (.=.) <$> eval' (tyX :@ c) <*> eval' (tyY :@ d)
    eqTU <- equalsBound (Just (tyX :@ c)) x (t :@ c) y (u :@ d)
    pure $ eqTy && eqTU

  VSigma x ((tyX, t) :@ c) .=. VSigma y ((tyY, u) :@ d) = do
    eqTy <- join $ (.=.) <$> eval' (tyX :@ c) <*> eval' (tyY :@ d)
    eqTU <- equalsBound (Just (tyX :@ c)) x (t :@ c) y (u :@ d)
    pure $ eqTy && eqTU

  VLam x t .=. VLam y u = equalsBound Nothing x t y u

  VPair ((t1, t2) :@ c) .=. VPair ((u1, u2) :@ d) = do
    eq1 <- join $ (.=.) <$> eval' (t1 :@ c) <*> eval' (u1 :@ d)
    eq2 <- join $ (.=.) <$> eval' (t2 :@ c) <*> eval' (u2 :@ d)
    pure $ eq1 && eq2

  VBox t .=. VBox u = equalsBoxed t u

  VLift t .=. VLift u = join $ (.=.) <$> eval' t <*> eval' u
  VRec t .=. VRec u = join $ (.=.) <$> eval' t <*> eval' u
  VFold t .=. VFold u = join $ (.=.) <$> eval' t <*> eval' u

  VNeutral x .=. VNeutral y = x .=. y

  -- handle the "boring" cases
  x .=. y = pure $ x == y

equalsBound :: MonadState Env m
            => Maybe (Closure (CTerm))
            -> Ident
            -> Closure (CTerm)
            -> Ident
            -> Closure (CTerm)
            -> m Bool
equalsBound ty x (t :@ c) y (u :@ d) = do
  iX <- declareE x ty
  vT <- eval' (t :@ (x, iX):c)
  vU <- eval' (u :@ (y, iX):d)
  vT .=. vU

equalsBound2 :: MonadState Env m
            => Maybe (Closure (CTerm))
            -> Ident
            -> Maybe (Closure (CTerm))
            -> Ident
            -> Closure (CTerm)
            -> Ident
            -> Ident
            -> Closure (CTerm)
            -> m Bool
equalsBound2 tyX x tyY y (t :@ c) w z (u :@ d) = do
  iX <- declareE x tyX
  iY <- declareE y tyY
  vT <- eval' (t :@ (y, iY):(x, iX):c)
  vU <- eval' (u :@ (z, iY):(w, iX):d)
  vT .=. vU

-- alpha equality for things inside boxes
equalsBoxed :: MonadState Env m
            => Closure (CTerm)
            -> Closure (CTerm)
            -> m Bool
equalsBoxed t u
  | t == u = pure True

-- move Lets to the left and evaluate
equalsBoxed (CLet ctxt t :@ c) u = do
  c' <- evalContext ctxt c
  equalsBoxed (t :@ c') u

equalsBoxed t u@(CLet _ _ :@ _) = equalsBoxed u t

equalsBoxed (CVar x :@ c) (CVar y :@ d) =
  case (lookup x c, lookup y d) of
    -- invoke crazy repoint logic
    (Just i, Just j) -> NVar i .=. NVar j
    _ -> error "ICE: equalsBoxed walked into undefined variable"

equalsBoxed (CPi x t u :@ c) (CPi y v w :@ d) = do
  eqArg <- equalsBoxed (t :@ c) (v :@ d)
  i <- declareE x Nothing
  eqRes <- equalsBoxed (u :@ (x, i):c) (w :@ (y, i):d)
  pure $ eqArg && eqRes

equalsBoxed (CSigma x t u :@ c) (CSigma y v w :@ d) = do
  eqArg <- equalsBoxed (t :@ c) (v :@ d)
  i <- declareE x Nothing
  eqRes <- equalsBoxed (u :@ (x, i):c) (w :@ (y, i):d)
  pure $ eqArg && eqRes

equalsBoxed (CLam x t :@ c) (CLam y u :@ d) = do
  i <- declareE x Nothing
  equalsBoxed (t :@ (x, i):c) (u :@ (y, i):d)

equalsBoxed (CApp t u :@ c) (CApp v w :@ d) =
  (&&) <$> (equalsBoxed (t :@ c) (v :@ d))
       <*> (equalsBoxed (u :@ c) (w :@ d))

equalsBoxed (CPair t u :@ c) (CPair v w :@ d) =
  (&&) <$> (equalsBoxed (t :@ c) (v :@ d))
       <*> (equalsBoxed (u :@ c) (w :@ d))

equalsBoxed (CSplit t x y u :@ c) (CSplit v a b w :@ d) = do
  eqArg <- equalsBoxed (t :@ c) (v :@ d)
  i <- declareE x Nothing
  j <- declareE y Nothing
  eqRes <- equalsBoxed (u :@ (y, j):(x, i):c) (w :@ (b, j):(a, i):d)
  pure $ eqArg && eqRes

equalsBoxed (CCase t cs :@ c) (CCase u ds :@ d) = do
  eqArg <- equalsBoxed (t :@ c) (u :@ d)
  eqCases <- zipWithM eqCase (byLabel cs) (byLabel ds)
  pure $ eqArg && and eqCases
  where
    eqCase (l, w) (m, v)
      | l /= m = pure False
      | otherwise = equalsBoxed (w :@ c) (v :@ d)
    byLabel = sortBy (\(l, _) (m, _) -> compare l m)

equalsBoxed (CLift t :@ c) (CLift u :@ d) = equalsBoxed (t :@ c) (u :@ d)
equalsBoxed (CBox t :@ c) (CBox u :@ d) = equalsBoxed (t :@ c) (u :@ d)
equalsBoxed (CForce t :@ c) (CForce u :@ d) = equalsBoxed (t :@ c) (u :@ d)
equalsBoxed (CRec t :@ c) (CRec u :@ d) = equalsBoxed (t :@ c) (u :@ d)
equalsBoxed (CFold t :@ c) (CFold u :@ d) = equalsBoxed (t :@ c) (u :@ d)

equalsBoxed (CUnfold t x u :@ c) (CUnfold v y w :@ d) = do
  eqArg <- equalsBoxed (t :@ c) (v :@ d)
  i <- declareE x Nothing
  eqRes <- equalsBoxed (u :@ (x, i):c) (w :@ (y, i):d)
  pure $ eqArg && eqRes

-- handle CType, CEnumLabel, CEnum
equalsBoxed (t :@ _) (u :@ _)
  | t == u = pure True
  | otherwise = pure False

instance Equals Neutral where
  -- see the following comment from the original implementation:
  {- ^ Necessary e.g. to evaluate t12 in the following code:
    Eq : (a:CType) -> a -> a -> CType;
    Eq = \ a x y -> (P : a -> CType) -> P x -> P y;

    refl : (a:CType) -> (x:a) -> Eq a x x;
    refl = \ a x P px -> px;

    A : CType;
    a : A;

    t12 : Eq (^A) (let y:A=y in [y]) (let z:A=z in [z])
        = refl (^A)  (let y:A=y in [y]);
  -}

  NVar i .=. NVar j
    | i == j = pure True
    | otherwise = do
        env <- get
        case (lookupE i env, lookupE j env) of
          (Just (EnvEntry _ _ t1), Just (EnvEntry _ _ t2)) -> case (t1, t2) of
            (Left i', Left j') -> pure $ i' == j'
            (Left _, _) -> pure False
            (_, Left _) -> pure False
            (Right t1', Right t2') -> locally $ do
              repointE i i
              repointE j i
              join $ (.=.) <$> eval' t1' <*> eval' t2'
          (_, _) -> error "ICE: invalid environment index"

  NApp n t .=. NApp m u = do
    nEq <- n .=. m
    case nEq of
      False -> pure False
      True -> join $ (.=.) <$> eval' t <*> eval' u

  NSplit n x y t .=. NSplit m w z u = do
    nEq <- n .=. m
    case nEq of
      False -> pure False
      True -> equalsBound2 Nothing x Nothing y t w z u

  NCase n (casesN :@ c) .=. NCase m (casesM :@ d) = do
    nEq <- n .=. m
    case nEq of
      False -> pure False
      True -> go casesN casesM
    where
      go [] [] = pure True
      go [] _ = pure False
      go _ [] = pure False
      go ((lN, t):restN) ((lM, u):restM) = do
        let lblEq = lN == lM
        tEq <- join $ (.=.) <$> eval' (t :@ c) <*> eval' (u :@ d)
        if lblEq && tEq
          then go restN restM
          else pure False

  NForce n .=. NForce m = n .=. m

  NUnfold n x t .=. NUnfold m y u = do
    nEq <- n .=. m
    case nEq of
      False -> pure False
      True -> equalsBound Nothing x t y u

  _ .=. _ = pure False
