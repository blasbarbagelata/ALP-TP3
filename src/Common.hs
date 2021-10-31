module Common where

  -- Comandos interactivos o de archivos
  data Stmt i = Def String i           --  Declarar un nuevo identificador x, let x = t
              | Eval i                 --  Evaluar el término
    deriving (Show)
  
  instance Functor Stmt where
    fmap f (Def s i) = Def s (f i)
    fmap f (Eval i)  = Eval (f i)

  -- Tipos de los nombres
  data Name
     =  Global  String
    deriving (Show, Eq)

  -- Entornos
  type NameEnv v t = [(Name, (v, t))]

  -- Tipo de los tipos
  data Type = EmptyT
            | NatT
            | FunT Type Type

            deriving (Show, Eq)
  
  -- Términos con nombres
  data LamTerm  =  LVar String
                |  LAbs String Type LamTerm
                |  LApp LamTerm LamTerm
                |  LLet String LamTerm LamTerm
                |  LZero
                |  LSucc LamTerm
                |  LRec LamTerm LamTerm LamTerm
       deriving (Show, Eq)


  -- Términos localmente sin nombres
  data Term  = Bound Int
             | Free Name 
             | Term :@: Term
             | Lam Type Term
             | Let Term Term
             | Zero
             | Succ Term
             | Rec Term Term Term
       deriving (Show, Eq)

  -- Valores
  data Value = VLam Type Term
             | VNat NumVal
          deriving (Show, Eq)
  data NumVal = VZero | VSuc NumVal deriving (Show, Eq)

  -- Contextos del tipado
  type Context = [Type]
