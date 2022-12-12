{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

-- Original type checker code by Stephanie Weirich at Dagstuhl (Sept 04)
--

module Main where

import Data.Functor.Identity
import qualified Language.Haskell.Exts as HSE
import System.Environment
import Data.List
import System.Directory

--------------------------------------------------------------------------------
-- Untyped AST

data UTerm
  = UVar String
  | ULam String UType UTerm
  | UApp UTerm UTerm
  | UIf UTerm UTerm UTerm
  | UPure UTerm
  | UBind UTerm UTerm
  | UPrim Prim

--------------------------------------------------------------------------------
-- Untyped type

data UType
  = UArr UType UType
  | UBool
  | UIo UType
  | UString

--------------------------------------------------------------------------------
-- Primitive functions

data Prim
  = DoesFileExist
  | WriteFile
  | PString String
  | PBool Bool

tcPrim :: Prim -> Typed (Term g)
tcPrim (PString string) = Typed String (Prim string)
tcPrim (PBool bool) = Typed Bool (Prim bool)
tcPrim DoesFileExist = Typed (Arr String (Io Bool)) (Prim doesFileExist)
tcPrim WriteFile =
  Typed
    (Arr String (Arr String (Io Bool)))
    (Prim (\fp str -> True <$ writeFile fp str))

--------------------------------------------------------------------------------
-- Typed type

data Ty t where
  Bool :: Ty Bool
  String :: Ty String
  Arr :: Ty a -> Ty b -> Ty (a -> b)
  Io :: Ty a -> Ty (IO a)

showType :: Ty a -> String
showType Bool = "Bool"
showType (Arr t1 t2) = "(" ++ showType t1 ++ ") -> (" ++ showType t2 ++ ")"
showType (Io a) = "(IO " ++ showType a ++ ")"

--------------------------------------------------------------------------------
-- Typed AST

data Term g t where
  -- Basic simply-typed lambda calculus
  Var :: Var g t -> Term g t
  Lam :: Ty a -> Term (g, a) b -> Term g (a -> b)
  App :: Term g (s -> t) -> Term g s -> Term g t
  -- Conditionals
  If :: Term g Bool -> Term g a -> Term g a -> Term g a
  -- Monad support
  Pure :: Term g a -> Term g (IO a)
  Bind :: Term g (IO a) -> Term g (a -> IO b) -> Term g (IO b)
  -- Primitives that can be used directly
  Prim :: a -> Term g a

data Var g t where
  ZVar :: Var (h, t) t
  SVar :: Var h t -> Var (h, s) t

data Typed thing = forall ty. Typed (Ty ty) (thing ty)

--------------------------------------------------------------------------------
-- Typechecking types

data ExType = forall t. ExType (Ty t)

tcType :: UType -> ExType
tcType UBool = ExType Bool
tcType UString = ExType String
tcType (UIo t1) = case tcType t1 of ExType t1' -> ExType (Io t1')
tcType (UArr t1 t2) = case tcType t1 of
  ExType t1' ->
    case tcType t2 of
      ExType t2' ->
        ExType (Arr t1' t2')

--------------------------------------------------------------------------------
-- Type checker helpers

data Equal a b where
  Equal :: Equal c c

-- The type environment and lookup
data TyEnv g where
  Nil :: TyEnv g
  Cons :: String -> Ty t -> TyEnv h -> TyEnv (h, t)

lookupVar :: String -> TyEnv g -> Typed (Var g)
lookupVar _ Nil = error "Variable not found"
lookupVar v (Cons s ty e)
  | v == s = Typed ty ZVar
  | otherwise = case lookupVar v e of
      Typed ty v -> Typed ty (SVar v)

cmpTy :: Ty a -> Ty b -> Maybe (Equal a b)
cmpTy Bool Bool = Just Equal
cmpTy String String = Just Equal
cmpTy (Io a1) (Io b1) =
  do
    Equal <- cmpTy a1 b1
    return Equal
cmpTy (Arr a1 a2) (Arr b1 b2) =
  do
    Equal <- cmpTy a1 b1
    Equal <- cmpTy a2 b2
    return Equal

--------------------------------------------------------------------------------
-- Type checker

check :: UTerm -> TyEnv () -> Typed (Term ())
check = tc

tc :: UTerm -> TyEnv g -> Typed (Term g)
tc (UVar v) env = case lookupVar v env of
  Typed ty v -> Typed ty (Var v)
tc (UPrim prim) env =
  tcPrim prim
tc (UPure a) env =
  case tc a env of
    Typed a_ty' a' -> Typed (Io a_ty') (Pure a')
tc (UBind e1 e2) env =
  case tc e2 env of
    Typed (Arr bndr_ty (Io body_ty)) e1' ->
      case tc e1 env of
        Typed (Io arg_ty) e2' ->
          case cmpTy arg_ty bndr_ty of
            Nothing -> error "Type error"
            Just Equal -> Typed (Io body_ty) (Bind e2' e1')
tc (ULam s ty body) env =
  case tcType ty of
    ExType bndr_ty' ->
      case tc body (Cons s bndr_ty' env) of
        Typed body_ty' body' ->
          Typed
            (Arr bndr_ty' body_ty')
            (Lam bndr_ty' body')
tc (UApp e1 e2) env =
  case tc e1 env of
    Typed (Arr bndr_ty body_ty) e1' ->
      case tc e2 env of
        Typed arg_ty e2' ->
          case cmpTy arg_ty bndr_ty of
            Nothing -> error "Type error"
            Just Equal -> Typed body_ty (App e1' e2')
tc (UIf e1 e2 e3) env =
  case tc e1 env of
    Typed Bool e1' ->
      case tc e2 env of
        Typed t2 e2' ->
          case tc e3 env of
            Typed t3 e3' ->
              case cmpTy t2 t3 of
                Nothing -> error "Type error"
                Just Equal -> Typed t2 (If e1' e2' e3')

--------------------------------------------------------------------------------
-- Evaluator

eval :: env -> Term env t -> t
eval env (Var v) = lookp v env
eval env (If cond true false) = if eval env cond then eval env true else eval env false
eval env (Lam _ e) = \x -> eval (env, x) e
eval env (App e1 e2) = (eval env e1) (eval env e2)
eval env (Pure e1) = pure (eval env e1)
eval env (Bind m f) = eval env m >>= eval env f
eval _ (Prim a) = a

lookp :: Var env t -> env -> t
lookp ZVar (_, x) = x
lookp (SVar v) (env, x) = lookp v env

--------------------------------------------------------------------------------
-- Top-level entry point

main :: IO ()
main =
  ( case check test Nil of
      Typed t ex ->
        case t of
          Io String -> do
            bool <- eval () ex
            print bool
          _ -> pure ()
  )

test :: UTerm
test =
  UBind
    (UApp (UPrim DoesFileExist) (UPrim (PString "heller.hs")))
    ( ULam
        "x"
        UBool
        ( UIf
            (UVar "x")
            (UPure (UPrim (PString "File exists!")))
            ( UBind
                (UApp (UApp (UPrim WriteFile) (UPrim $ PString "heller.hs")) (UPrim $ PString "output here!"))
                ( ULam
                    "_"
                    UBool
                    (UPure (UPrim $ PString "Wrote heller.hs"))
                )
            )
        )
    )

-- main :: IO ()
-- main = do
--   (filePath:_) <- getArgs
--   string <- readFile filePath
--   case HSE.parseModule string >>= parseModule of
--     HSE.ParseOk binds ->
--       case lookup "main" binds of
--         Nothing -> error "No main declaration!"
--         Just expr -> Hell.reify $ Hell.eval expr

-- parseModule :: Show a => HSE.Module a -> HSE.ParseResult [(String, Term () (IO ()))]
-- parseModule (HSE.Module _ Nothing [] [] decls) =
--   traverse parseDecl decls
--   where parseDecl (HSE.PatBind _ (HSE.PVar _ (HSE.Ident _ string)) (HSE.UnGuardedRhs _ exp') Nothing) =
--           do e <- parseE exp'
--              pure (string, e)
--         parseE (HSE.Var _ (HSE.UnQual _ (HSE.Ident _ string))) =
--           pure $ Hell.prim string
--         parseE (HSE.App _ f x) = do
--           Hell.A <$> parseE f <*> parseE x
--         parseE (HSE.Lit _ (HSE.String _ string _original)) =
--           pure $ Hell.T string
--         parseE (HSE.Do _ stmts) = do
--           stmts' <- traverse parseStmt stmts
--           pure $ foldr (\m f -> Hell.A (Hell.A then' m) f) (Hell.reflect (pure () :: IO ())) stmts'
--         parseE (HSE.List _ xs) = Hell.reflect <$> traverse parseE xs
--         parseE expr' = error $ "Can't parse " ++ show expr'
--         parseStmt (HSE.Qualifier _ e) = parseE e
