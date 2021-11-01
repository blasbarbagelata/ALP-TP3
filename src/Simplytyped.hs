module Simplytyped
  ( conversion
  ,    -- conversion a terminos localmente sin nombre
    eval
  ,          -- evaluador
    infer
  ,         -- inferidor de tipos
    quote          -- valores -> terminos
  )
where

import           Data.List
import           Data.Maybe
import           Prelude                 hiding ( (>>=) )
import           Text.PrettyPrint.HughesPJ      ( render )
import           PrettyPrinter
import           Common

-- conversion a términos localmente sin nombres
conversion :: LamTerm -> Term
conversion = conversion' []

conversion' :: [String] -> LamTerm -> Term
conversion' b (LVar n    )      = maybe (Free (Global n)) Bound (n `elemIndex` b)
conversion' b (LApp t u  )      = conversion' b t :@: conversion' b u
conversion' b (LAbs n t u)      = Lam t (conversion' (n : b) u)
conversion' b (LLet s t e)      = Let (conversion' b t) (conversion' (s : b) e)
conversion' b LZero             = Zero
conversion' b (LSucc t   )      = Succ (conversion' b t)
conversion' b (LRec t1 t2 t3)   = Rec (conversion' b t1) (conversion' b t2) (conversion' b t3)
conversion' b LNil              = Nil
conversion' b (LCons t1 t2)     = Cons (conversion' b t1) (conversion' b t2)
conversion' b (LRecL t1 t2 t3)   = RecL (conversion' b t1) (conversion' b t2) (conversion' b t3)

-----------------------
--- eval
-----------------------

sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
sub _ _ (Bound j) | otherwise = Bound j
sub _ _ (Free n   )           = Free n
sub i t (u   :@: v)           = sub i t u :@: sub i t v
sub i t (Lam t'  u)           = Lam t' (sub (i + 1) t u)
sub i t (Let t' e )           = Let (sub i t t') (sub (i+1) t e)
sub i t Zero                  = Zero
sub i t (Succ u   )           = Succ (sub i t u)
sub i t (Rec t1 t2 t3)        = Rec (sub i t t1) (sub i t t2) (sub i t t3)
sub i t Nil                   = Nil
sub i t (Cons u   v)          = Cons (sub i t u) (sub i t v)
sub i t (RecL t1 t2 t3)       = Rec (sub i t t1) (sub i t t2) (sub i t t3)

-- evaluador de términos
eval :: NameEnv Value Type -> Term -> Value
eval _ (Bound _             ) = error "variable ligada inesperada en eval"
eval e (Free  n             ) = fst $ fromJust $ lookup n e
eval _ (Lam      t   u      ) = VLam t u
eval e (Lam _ u  :@: Lam s v) = eval e (sub 0 (Lam s v) u)
eval e (Lam t u1 :@: u2) = let v2 = eval e u2 in eval e (sub 0 (quote v2) u1)
eval e (u        :@: v      ) = case eval e u of
  VLam t u' -> eval e (Lam t u' :@: v)
  _         -> error "Error de tipo en run-time, verificar type checker"
eval e (Let u v             ) = eval e (sub 0 (quote (eval e u)) v)
eval e Zero                   = VNat VZero
eval e (Succ t              ) = case eval e t of
  VNat num -> VNat (VSuc num)
  _        -> error "Error de tipo en run-time, verificar type checker"
eval e (Rec t1 t2 t3)         = case eval e t3 of
  VNat VZero        -> eval e t1
  VNat (VSuc nv)    -> let t = quote (VNat nv)
                           r' = eval e (Rec t1 t2 t) 
                       in eval e ((t2 :@: quote r') :@: t)
  _                 -> error "Error de tipo en run-time, verificar type checker"
eval e Nil                    = VList VNil
eval e (Cons t1 t2)           = case eval e t1 of
    VNat nv     -> case eval e t2 of
                        VList l -> VList (VCons (VNat nv) l)
                        _       -> error "Error de tipo en run-time, verificar type checker"
    _           -> error "Error de tipo en run-time, verificar type checker"
eval e (RecL t1 t2 t3)        = case eval e t3 of
    VList VNil            -> eval e t1
    VList (VCons nv lv)   -> let n = quote nv
                                 l = quote (VList lv)
                                 rl = quote (eval e (RecL t1 t2 l))
                             in eval e (t2 :@: n :@: l :@: rl)
    _                       ->error "Error de tipo en run-time, verificar type checker"


-----------------------
--- quoting
-----------------------

quote :: Value -> Term
quote (VLam t f) = Lam t f
quote (VNat VZero) = Zero
quote (VNat (VSuc n)) = Succ (quote (VNat n))
quote (VList VNil) = Nil
quote (VList (VCons v vl)) = Cons (quote v) (quote (VList vl))

----------------------
--- type checker
-----------------------

-- type checker
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=)
  :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v
-- fcs. de error

matchError :: Type -> Type -> Either String Type
matchError t1 t2 =
  err
    $  "se esperaba "
    ++ render (printType t1)
    ++ ", pero "
    ++ render (printType t2)
    ++ " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i) = ret (c !! i)
infer' _ e (Free  n) = case lookup n e of
  Nothing     -> notfoundError n
  Just (_, t) -> ret t
infer' c e (t :@: u) = infer' c e t >>= \tt -> infer' c e u >>= \tu ->
  case tt of
    FunT t1 t2 -> if (tu == t1) then ret t2 else matchError t1 tu
    _          -> notfunError tt
infer' c e (Lam t u) = infer' (t : c) e u >>= \tu -> ret $ FunT t tu
infer' c e (Let t u) = infer' c e t >>= \tu -> infer' (tu:c) e u
infer' c e Zero      = ret NatT
infer' c e (Succ n ) = infer' c e n >>= \tn -> if tn == NatT then ret tn else matchError NatT tn
infer' c e (Rec t1 t2 t3) = infer' c e t1 >>= \tn1 -> infer' c e t2 >>= \tn2 ->
    case tn2 of
        FunT tt1 (FunT NatT tt2) -> if (tt1 == tn1 && tt2 == tn1) then infer' c e t3 >>= \tn3 -> if tn3 == NatT then ret tn1 else matchError NatT tn3
                                                                  else matchError (FunT tn1 (FunT NatT tn1)) (FunT tt1 (FunT NatT tt2))
        tt                       -> matchError (FunT tn1 (FunT NatT tn1)) tt
infer' c e Nil          = ret ListNat
infer' c e (Cons t1 t2) = infer' c e t1 >>= \tl -> 
    case tl of 
        NatT -> infer' c e t2 >>= \tll -> case tll of
                                            ListNat -> ret ListNat
                                            _       -> matchError ListNat tll
        _    -> matchError NatT tl
infer' c e (RecL t1 t2 t3) = infer' c e t1 >>= \tl1 -> infer' c e t2 >>= \tl2 ->
    case tl2 of
        FunT NatT (FunT ListNat (FunT tt1 tt2)) -> if tt1 == tl1 && tt2 == tl1 then infer' c e t3 >>= \tl3 -> case tl3 of
                                                                                                                ListNat -> ret tl1
                                                                                                                _       -> matchError ListNat tl3
                                                                               else matchError (FunT NatT (FunT ListNat (FunT tl1 tl1))) (FunT NatT (FunT ListNat (FunT tt1 tt2)))
        _                                       -> matchError (FunT NatT (FunT ListNat (FunT tl1 tl1))) tl2
----------------------------------
