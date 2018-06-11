{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Equals (
    Equals(..)
) where

import Language.MinPS.Environment
import Language.MinPS.Syntax
import Language.MinPS.Value
import Language.MinPS.Eval

import Control.Monad.State

class Equals a where
  (.=.) :: MonadState Env m => a -> a -> m Bool
infix 3 .=.

instance Equals Value where
  VType .=. VType = pure True
  VEnum xs .=. VEnum ys = pure $ xs == ys
  VEnumLabel x .=. VEnumLabel y = pure $ x == y
  VNeutral x .=. VNeutral y = x .=. y

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

  VLift t .=. VLift u = join $ (.=.) <$> eval' t <*> eval' u
  VRec t .=. VRec u = join $ (.=.) <$> eval' t <*> eval' u
  VFold t .=. VFold u = join $ (.=.) <$> eval' t <*> eval' u

  _ .=. _ = pure False

equalsBound :: MonadState Env m
            => Maybe (Closure (Term 'Checked))
            -> Ident
            -> Closure (Term 'Checked)
            -> Ident
            -> Closure (Term 'Checked)
            -> m Bool
equalsBound ty x (t :@ c) y (u :@ d) = do
  iX <- declareE x ty
  vT <- eval' (t :@ (x, iX):c)
  vU <- eval' (u :@ (y, iX):d)
  vT .=. vU

equalsBound2 :: MonadState Env m
            => Maybe (Closure (Term 'Checked))
            -> Ident
            -> Maybe (Closure (Term 'Checked))
            -> Ident
            -> Closure (Term 'Checked)
            -> Ident
            -> Ident
            -> Closure (Term 'Checked)
            -> m Bool
equalsBound2 tyX x tyY y (t :@ c) w z (u :@ d) = do
  iX <- declareE x tyX
  iY <- declareE y tyY
  vT <- eval' (t :@ (y, iY):(x, iX):c)
  vU <- eval' (u :@ (z, iY):(w, iX):d)
  vT .=. vU

instance Equals Neutral where
  -- see the following comment from the original implementation:
  {- ^ Necessary e.g. to evaluate t12 in the following code:
    Eq : (a:Type) -> a -> a -> Type;
    Eq = \ a x y -> (P : a -> Type) -> P x -> P y;

    refl : (a:Type) -> (x:a) -> Eq a x x;
    refl = \ a x P px -> px;

    A : Type;
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
    tEq <- join $ (.=.) <$> eval' t <*> eval' u
    pure $ nEq && tEq

  NSplit n x y t .=. NSplit m w z u = do
    nEq <- n .=. m
    tEq <- equalsBound2 Nothing x Nothing y t w z u
    pure $ nEq && tEq

  NCase n (casesN :@ c) .=. NCase m (casesM :@ d) = do
    nEq <- n .=. m
    casesEq <- go casesN casesM
    pure $ nEq && casesEq
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
    tEq <- equalsBound Nothing x t y u
    pure $ nEq && tEq

  _ .=. _ = pure False
