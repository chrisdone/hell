{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

-- Original type checker code by Stephanie Weirich at Dagstuhl (Sept 04)
--

module Main where

import Data.Functor.Identity
import System.Directory

--------------------------------------------------------------------------------
-- Untyped AST

data UTerm
  = UVar String
  | ULam String UType UTerm
  | UApp UTerm UTerm
  | UConBool Bool
  | UConString String
  | UIf UTerm UTerm UTerm
  | UPure UTerm
  | UPrim Prim
  | UBind UTerm UTerm

--------------------------------------------------------------------------------
-- Untyped type

data UType
  = UBool
  | UArr UType UType
  | UIo UType
  | UString

--------------------------------------------------------------------------------
-- Primitive functions

data Prim = DoesFileExist | WriteFile

tcPrim :: Prim -> Typed (Term g)
tcPrim DoesFileExist = Typed (Arr String (Io Bool)) (Prim1 doesFileExist)
tcPrim WriteFile =
  Typed
    (Arr String (Arr String (Io Bool)))
    (Prim2 (\fp str -> True <$ writeFile fp str))

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
  Var :: Var g t -> Term g t
  Lam :: Ty a -> Term (g, a) b -> Term g (a -> b)
  App :: Term g (s -> t) -> Term g s -> Term g t
  ConBool :: Bool -> Term g Bool
  ConString :: String -> Term g String
  If :: Term g Bool -> Term g a -> Term g a -> Term g a
  Pure :: Term g a -> Term g (IO a)
  Bind :: Term g (IO a) -> Term g (a -> IO b) -> Term g (IO b)
  Prim1 :: (a -> b) -> Term g (a -> b)
  Prim2 :: (a -> b -> c) -> Term g (a -> b -> c)

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

tc :: UTerm -> TyEnv g -> Typed (Term g)
tc (UVar v) env = case lookupVar v env of
  Typed ty v -> Typed ty (Var v)
tc (UConBool b) env =
  Typed Bool (ConBool b)
tc (UConString b) env =
  Typed String (ConString b)
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
eval _ (ConBool c) = c
eval _ (ConString c) = c
eval env (If cond true false) = if eval env cond then eval env true else eval env false
eval env (Lam _ e) = \x -> eval (env, x) e
eval env (App e1 e2) = (eval env e1) (eval env e2)
eval env (Pure e1) = pure (eval env e1)
eval env (Bind m f) = eval env m >>= eval env f
eval _ (Prim1 a) = a
eval _ (Prim2 a) = a

lookp :: Var env t -> env -> t
lookp ZVar (_, x) = x
lookp (SVar v) (env, x) = lookp v env

--------------------------------------------------------------------------------
-- Top-level example

check :: UTerm -> TyEnv () -> Typed (Term ())
check = tc

main =
  ( case check test Nil of
      Typed t ex ->
        case t of
          Io String -> do
            bool <- eval () ex
            print bool
          _ -> pure ()
  )

uNot = ULam "x" UBool (UIf (UVar "x") (UConBool False) (UConBool True))

test :: UTerm
test =
  UBind
    (UApp (UPrim DoesFileExist) (UConString "heller.hs"))
    ( ULam
        "x"
        UBool
        ( UIf
            (UVar "x")
            (UPure (UConString "File exists!"))
            ( UBind
                (UApp (UApp (UPrim WriteFile) (UConString "heller.hs")) (UConString "output here!"))
                ( ULam
                    "_"
                    UBool
                    (UPure (UConString "Wrote heller.hs"))
                )
            )
        )
    )
