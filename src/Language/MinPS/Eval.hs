{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}

module Language.MinPS.Eval (
    eval
  , eval'
) where

import Language.MinPS.Syntax
import Language.MinPS.Value

eval :: Term 'Checked -> Value
eval = eval' []

eval' :: Closure -> Term 'Checked -> Value
eval' c (Let ctxt t) = eval' (evalContext ctxt c) t
eval' _ Type = VType
eval' c (Var i) = lookupVar c i
eval' c (Pi x ty t) = VPi c x ty t
eval' c (Sigma x ty t) = VSigma c x ty t
eval' c (Lam x t) = VLam c x t
eval' c (Pair t u) = VPair c t u
eval' _ (Enum lbls) = VEnum lbls
eval' _ (EnumLabel lbl) = VEnumLabel lbl
eval' c (Lift t) = VLift c t
eval' c (Box t) = VBox c t
eval' c (Rec t) = VRec c t
eval' c (Fold t) = VFold c t

eval' c (App f x) = case eval' c f of
  VNeutral n -> VNeutral (NApp n c x)
  VLam c' _ body -> eval' ((eval' c x):c') body
  _ -> error "ICE: invalid application passed check"

eval' c (Split t x y u) = case eval' c t of
  VNeutral n -> VNeutral (NSplit n c x y u)
  VPair c' t1 t2 -> eval' ((eval' c' t2):(eval' c' t1):c) u
  _ -> error "ICE: invalid split passed check"

eval' c (Case t cases) = case (eval' c t) of
  VNeutral n -> VNeutral (NCase n c cases)
  VEnumLabel l -> case lookup l cases of
    Just u -> eval' c u
    Nothing -> error "ICE: invalid case passed check"
  _ -> error "ICE: invalid case passed check"

eval' c (Force t) = case (eval' c t) of
  VNeutral n -> VNeutral (NForce n)
  VBox c' t' -> eval' c' t'
  _ -> error "ICE: invalid force passed check"

eval' c (Unfold t x u) = case (eval' c t) of
  VNeutral n -> VNeutral (NUnfold n c x u)
  VFold c' t' -> eval' ((eval' c' t'):c) u
  _ -> error "ICE: invalid unfold passed check"

lookupVar :: Closure -> Int -> Value
lookupVar c i = go i c i where
  go ix [] _ = VNeutral (NVar ix)
  go _ (v:_) 0 = v
  go ix (_:vs) n = go ix vs (n - 1)

evalContext :: Context 'Checked -> Closure -> Closure
evalContext [] c = c
evalContext ((_, _, t):rest) c = evalContext rest ((eval' c t):c)
