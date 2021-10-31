module PrettyPrinter
  ( printTerm
  ,     -- pretty printer para terminos
    printType     -- pretty printer para tipos
  )
where

import           Common
import           Text.PrettyPrint.HughesPJ
import           Prelude                 hiding ( (<>) )
import System.Posix.Internals (c_dup2)
-- lista de posibles nombres para variables
vars :: [String]
vars =
  [ c : n
  | n <- "" : map show [(1 :: Integer) ..]
  , c <- ['x', 'y', 'z'] ++ ['a' .. 'w']
  ]

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

-- pretty-printer de términos

pp :: Int -> [String] -> Term -> Doc
pp ii vs (Bound k         ) = text (vs !! (ii - k - 1))
pp _  _  (Free  (Global s)) = text s

pp ii vs (i :@: c         ) = sep
  [ parensIf (isLam i) (pp ii vs i)
  , nest 1 (parensIf (isLam c || isApp c) (pp ii vs c))
  ]
pp ii vs (Lam t c) =
  text "\\"
    <> text (vs !! ii)
    <> text ":"
    <> printType t
    <> text ". "
    <> pp (ii + 1) vs c

pp ii vs (Let t u) =
  text "let "
    <> text (vs !! ii)
    <> text " = "
    <> parensIf (notValue t) (pp ii vs t)
    <> text " in "
    <> pp (ii + 1) vs u

pp ii vs (Succ t) = 
    text "suc "
    <> parensIf (notValue t) (pp ii vs t)

pp ii vs (Rec t1 t2 t3) = 
    sep [text "R",
         parensIf (notValue t1) (pp ii vs t1),
         parensIf (notValue t2) (pp ii vs t2),
         parensIf (notValue t3) (pp ii vs t3)]
         
pp ii vs Zero = text "0"

isZero :: Term -> Bool
isZero Zero = True
isZero _    = False

isVar :: Term -> Bool 
isVar (Bound _) = True
isVar (Free _)  = True 
isVar _         = False 

notValue :: Term -> Bool
notValue t = not (isZero t || isVar t)

isLam :: Term -> Bool
isLam (Lam _ _) = True
isLam _         = False

isApp :: Term -> Bool
isApp (_ :@: _) = True
isApp _         = False

isLet :: Term -> Bool
isLet (Let _ _) = True
isLet _         = False

-- pretty-printer de tipos
printType :: Type -> Doc
printType EmptyT = text "E"
printType NatT   = text "Nat"
printType (FunT t1 t2) =
  sep [parensIf (isFun t1) (printType t1), text "->", printType t2]


isFun :: Type -> Bool
isFun (FunT _ _) = True
isFun _          = False

fv :: Term -> [String]
fv (Bound _         ) = []
fv (Free  (Global n)) = [n]
fv (t   :@: u       ) = fv t ++ fv u
fv (Lam _   u       ) = fv u
fv (Let t u         ) = fv t ++ fv u
fv Zero               = []
fv (Succ t          ) = fv t
fv (Rec a b c       ) = fv a ++ fv b ++ fv c         
---
printTerm :: Term -> Doc
printTerm t = pp 0 (filter (\v -> not $ elem v (fv t)) vars) t

