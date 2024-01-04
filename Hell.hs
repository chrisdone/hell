--
-- Welcome to Hell
--
-- Haskell as a scripting language!
--
-- Special thanks to Stephanie Weirich, whose type-safe typechecker
-- this is built upon, and for the Type.Reflection module, which has
-- made some of this more ergonomic.

{-# LANGUAGE ExistentialQuantification, TypeApplications, BlockArguments #-}
{-# LANGUAGE GADTs, PolyKinds, TupleSections, StandaloneDeriving, Rank2Types #-}
{-# LANGUAGE ViewPatterns, LambdaCase, ScopedTypeVariables, PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings, MultiWayIf #-}

module Main (main) where

-- All modules tend to be imported qualified by their last component,
-- e.g. 'Data.Graph' becomes 'Graph', and are then exposed to the Hell
-- guest language as such.

import qualified Data.Graph as Graph
import qualified Data.Eq as Eq
import qualified Data.Ord as Ord
import qualified Data.Bool as Bool
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Text.Show as Show
import qualified Data.Function as Fun
import qualified Data.Generics.Schemes as SYB
import qualified Type.Reflection as Type
import qualified Data.Maybe as Maybe
import qualified Language.Haskell.Exts as HSE
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Builder as ByteString hiding (writeFile)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Text.IO as Text
import qualified System.IO as IO
import qualified System.IO.Error as Error
import qualified Control.Concurrent.Async as Async
import qualified System.Directory as Dir
import qualified Options.Applicative as Options

-- Things used within the host language.

import Data.Traversable
import Data.Bifunctor
import System.Process.Typed as Process
import Control.Monad.State
import System.Environment
import Data.Map (Map)
import Data.Text (Text)
import Data.ByteString (ByteString)
import Data.Constraint
import GHC.Types
import Type.Reflection (SomeTypeRep(..), TypeRep, typeRepKind, typeRep, pattern TypeRep)

-- Testing support

import Test.Hspec
import Test.QuickCheck

------------------------------------------------------------------------------
-- Main entry point

data Command
  = Run FilePath
  | Check FilePath
  | Version
  | Exec String

main :: IO ()
main = dispatch =<< Options.execParser opts
  where
    opts = Options.info (commandParser Options.<**> Options.helper)
      ( Options.fullDesc
     <> Options.progDesc "Runs and typechecks Hell scripts"
     <> Options.header "hell - A Haskell-driven scripting language" )

commandParser :: Options.Parser Command
commandParser =
  Options.asum [
   Run <$> Options.strArgument (Options.metavar "FILE" <> Options.help "Run the given .hell file"),
   Check <$> Options.strOption (Options.long "check" <> Options.metavar "FILE" <> Options.help "Typecheck the given .hell file"),
   Version <$ Options.flag () () (Options.long "version" <> Options.help "Print the version"),
   Exec <$> Options.strOption (Options.long "exec" <> Options.help "Execute the given expression" <> Options.metavar "EXPR")
  ]

dispatch :: Command -> IO ()
dispatch Version = putStrLn "2023-12-12"
dispatch (Run filePath) = do
  string <- readFile filePath
  case HSE.parseModuleWithMode HSE.defaultParseMode { HSE.extensions = HSE.extensions HSE.defaultParseMode ++ [HSE.EnableExtension HSE.PatternSignatures, HSE.EnableExtension HSE.TypeApplications] } string >>= parseModule of
    HSE.ParseFailed _ e -> error $ e
    HSE.ParseOk binds
      | anyCycles binds -> error "Cyclic bindings are not supported!"
      | otherwise ->
            case desugarAll binds of
              Left err -> error $ "Error desugaring! " ++ show err
              Right terms ->
                case lookup "main" terms of
                  Nothing -> error "No main declaration!"
                  Just main' ->
                    case check main' Nil of
                       Typed t ex ->
                         case Type.eqTypeRep (typeRepKind t) (typeRep @Type) of
                           Just Type.HRefl ->
                             case Type.eqTypeRep t (typeRep @(IO ())) of
                               Just Type.HRefl ->
                                 let action :: IO () = eval () ex
                                 in action
                               Nothing -> error $ "Type isn't IO (), but: " ++ show t
dispatch (Check filePath) = do
  string <- readFile filePath
  case HSE.parseModuleWithMode HSE.defaultParseMode { HSE.extensions = HSE.extensions HSE.defaultParseMode ++ [HSE.EnableExtension HSE.PatternSignatures, HSE.EnableExtension HSE.TypeApplications] } string >>= parseModule of
    HSE.ParseFailed _ e -> error $ e
    HSE.ParseOk binds
      | anyCycles binds -> error "Cyclic bindings are not supported!"
      | otherwise ->
            case desugarAll binds of
              Left err -> error $ "Error desugaring! " ++ show err
              Right terms ->
                case lookup "main" terms of
                  Nothing -> error "No main declaration!"
                  Just main' ->
                    case check main' Nil of
                       Typed t ex ->
                         case Type.eqTypeRep (typeRepKind t) (typeRep @Type) of
                           Just Type.HRefl ->
                             case Type.eqTypeRep t (typeRep @(IO ())) of
                               Just Type.HRefl ->
                                 let action :: IO () = eval () ex
                                 in pure ()
                               Nothing -> error $ "Type isn't IO (), but: " ++ show t
dispatch (Exec string) = do
  case HSE.parseExpWithMode HSE.defaultParseMode { HSE.extensions = HSE.extensions HSE.defaultParseMode ++ [HSE.EnableExtension HSE.PatternSignatures, HSE.EnableExtension HSE.TypeApplications] } string of
    HSE.ParseFailed _ e -> error $ e
    HSE.ParseOk e ->
            case desugarExp mempty e of
              Left err -> error $ "Error desugaring! " ++ show err
              Right uterm ->
                    case check uterm Nil of
                       Typed t ex ->
                         case Type.eqTypeRep (typeRepKind t) (typeRep @Type) of
                           Just Type.HRefl ->
                             case Type.eqTypeRep t (typeRep @(IO ())) of
                               Just Type.HRefl ->
                                 let action :: IO () = eval () ex
                                 in action
                               Nothing -> error $ "Type isn't IO (), but: " ++ show t

--------------------------------------------------------------------------------
-- Get declarations from the module

parseModule :: HSE.Module HSE.SrcSpanInfo -> HSE.ParseResult [(String, HSE.Exp HSE.SrcSpanInfo)]
parseModule (HSE.Module _ Nothing [] [] decls) =
  traverse parseDecl decls
  where
    parseDecl (HSE.PatBind _ (HSE.PVar _ (HSE.Ident _ string)) (HSE.UnGuardedRhs _ exp') Nothing) =
          pure (string, exp')
    parseDecl _ = error "Can't parse that!"

--------------------------------------------------------------------------------
-- Typed AST support
--
-- We define a well-typed, well-indexed GADT AST which can be evaluated directly.

data Term g t where
  Var :: Var g t -> Term g t
  Lam :: TypeRep (a :: Type) -> Term (g, a) b -> Term g (a -> b)
  App :: Term g (s -> t) -> Term g s -> Term g t
  Lit :: a -> Term g a

data Var g t where
  ZVar :: (t -> a) -> Var (h, t) a
  SVar :: Var h t -> Var (h, s) t

--------------------------------------------------------------------------------
-- Evaluator
--

-- This is the entire evaluator. Type-safe and total.
eval :: env -> Term env t -> t
eval env (Var v) = lookp v env
eval env (Lam _ e) = \x -> eval (env, x) e
eval env (App e1 e2) = (eval env e1) (eval env e2)
eval _env (Lit a) = a

-- Type-safe, total lookup. The final @slot@ determines which slot of
-- a given tuple to pick out.
lookp :: Var env t -> env -> t
lookp (ZVar slot) (_, x) = slot x
lookp (SVar v) (env, x) = lookp v env

--------------------------------------------------------------------------------
-- The "untyped" AST
--
-- This is the AST that is not interpreted, and is just
-- type-checked. The HSE AST is desugared into this one.

data UTerm
  = UVar String
  | ULam Binding SomeStarType UTerm
  | UApp UTerm UTerm
  | UForall [SomeStarType] Forall
  | ULit (forall g. Typed (Term g))
  | UBind UTerm UTerm
  | UList [UTerm] (Maybe SomeStarType)
  | UTuple [UTerm]
  | UIf UTerm UTerm UTerm

data Binding = Singleton String | Tuple [String]

data Forall
  = Unconstrained (forall (a :: Type) g. TypeRep a -> Forall)
  | Constrained (forall (a :: Type) g. (Show a, Eq a, Ord a) => TypeRep a -> Forall)
  | Final (forall g. Typed (Term g))

lit :: Type.Typeable a => a -> UTerm
lit l = ULit (Typed (Type.typeOf l) (Lit l))

data SomeStarType = forall (a :: Type). SomeStarType (TypeRep a)
deriving instance Show SomeStarType
instance Eq SomeStarType where
  SomeStarType x == SomeStarType y = Type.SomeTypeRep x == Type.SomeTypeRep y

pattern StarTypeRep t <- (toStarType -> Just (SomeStarType t)) where
  StarTypeRep t = SomeTypeRep t

toStarType :: SomeTypeRep -> Maybe SomeStarType
toStarType (SomeTypeRep t) = do
  Type.HRefl <- Type.eqTypeRep (typeRepKind t) (typeRep @Type)
  pure $ SomeStarType t

--------------------------------------------------------------------------------
-- The type checker

data Typed (thing :: Type -> Type) = forall ty. Typed (TypeRep (ty :: Type)) (thing ty)

typed :: Type.Typeable a => a -> Typed (Term g)
typed l = Typed (Type.typeOf l) (Lit l)

-- The type environment and lookup
data TyEnv g where
  Nil :: TyEnv g
  Cons :: Binding -> TypeRep (t :: Type) -> TyEnv h -> TyEnv (h, t)

-- The top-level checker used by the main function.
check :: UTerm -> TyEnv () -> Typed (Term ())
check = tc

-- Type check a term given an environment of names.
tc :: UTerm -> TyEnv g -> Typed (Term g)
tc (UTuple [x,y]) env =
  case (tc x env, tc y env) of
    (Typed (TypeRep @x) x', Typed (TypeRep @y) y') ->
      Typed (typeRep @(x,y)) $ App (App (Lit ((,) :: x -> y -> (x,y))) x') y'
tc (UTuple [x,y,z]) env =
  case (tc x env, tc y env, tc z env) of
    (Typed (TypeRep @x) x', Typed (TypeRep @y) y', Typed (TypeRep @z) z') ->
      Typed (typeRep @(x,y,z)) $ App (App (App (Lit ((,,) :: x -> y -> z -> (x,y,z))) x') y') z'
tc (UVar v) env = case lookupVar v env of
  Typed ty v -> Typed ty (Var v)
tc (ULam s (SomeStarType bndr_ty') body) env =
      case tc body (Cons s bndr_ty' env) of
        Typed body_ty' body' ->
          Typed
            (Type.Fun bndr_ty' body_ty')
            (Lam bndr_ty' body')
tc (UApp e1 e2) env =
  case tc e1 env of
    Typed (Type.Fun bndr_ty body_ty) e1' ->
      case tc e2 env of
        Typed arg_ty e2' ->
          case Type.eqTypeRep arg_ty bndr_ty of
            Nothing -> error $ "Type error: " ++ show arg_ty ++ " vs " ++ show bndr_ty
            Just (Type.HRefl) ->
             let kind = typeRepKind body_ty
             in
             case Type.eqTypeRep kind (typeRep @Type) of
               Just Type.HRefl
                 -> Typed body_ty
                     (App e1'
                          e2')
-- Mono-typed terms
tc (ULit lit) _env = lit
-- Polytyped terms, must be, syntactically, fully-saturated
tc (UForall reps fall) _env = go reps fall where
  go :: [SomeStarType] -> Forall -> Typed (Term g)
  go [] (Final typed) = typed
  go (SomeStarType rep:reps) (Unconstrained f) = go reps (f rep)
  go (SomeStarType rep:reps) (Constrained f) =
    if
      | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Int) -> go reps (f rep)
      | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Bool) -> go reps (f rep)
      | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Char) -> go reps (f rep)
      | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Text) -> go reps (f rep)
      | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @ByteString) -> go reps (f rep)
      | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @ExitCode) -> go reps (f rep)
      | otherwise -> error $ "type doesn't have enough instances " ++ show rep
  go _ _ = error "forall type arguments mismatch."
-- Special handling for `if'
tc (UIf i t e) env =
  case tc i env of
    Typed i_ty i'
      | Just Type.HRefl <- Type.eqTypeRep i_ty (typeRep @Bool) ->
        case (tc t env, tc e env) of
          (Typed (t_ty :: TypeRep a) t', Typed e_ty e')
            | Just Type.HRefl <- Type.eqTypeRep t_ty e_ty ->
               Typed t_ty (App (App (App (Lit (Bool.bool @a)) e') t') i')
            | otherwise ->
              error $ "If branches types don't match: " ++ show t_ty ++ " vs " ++ show e_ty
      | otherwise -> error $ "If's condition isn't Bool, got: " ++ show i_ty
-- Bind needs special type-checker handling, because do-notation lacks
-- the means to pass the types about >>=
tc (UBind m f) env =
  case tc m env of
    Typed m_ty' m'
      | Just Type.HRefl <- Type.eqTypeRep (typeRepKind m_ty') (typeRep @Type) ->
       case tc f env of
         Typed f_ty' f'
          | Just Type.HRefl <- Type.eqTypeRep (typeRepKind f_ty') (typeRep @Type) ->
           -- Happy path:
           --
           -- m_ty' == typeRep @(IO a)
           -- f_ty' == typeRep @(a -> IO b)
           -- final type is: IO b
           case (m_ty', f_ty') of
              (Type.App io1 a1, Type.Fun a2 final@(Type.App io2 (b :: TypeRep b)))
                | Just Type.HRefl <- Type.eqTypeRep io1 (typeRep @IO),
                  Just Type.HRefl <- Type.eqTypeRep io2 (typeRep @IO),
                  Just Type.HRefl <- Type.eqTypeRep a1 a2,
                  Just Type.HRefl <- Type.eqTypeRep (typeRepKind a1) (typeRep @Type),
                  Just Type.HRefl <- Type.eqTypeRep (typeRepKind a2) (typeRep @Type),
                  Just Type.HRefl <- Type.eqTypeRep (typeRepKind b) (typeRep @Type) ->
                  Typed final (App (App (Lit (>>=)) m') f')
              _ -> error "Bind in do-notation type mismatch."
-- Lists
-- 1. Empty list; we don't have anything to check, but we need a type.
-- 2. Populated list, we don't need a type, and expect something immediately.
tc (UList [] (Just (SomeStarType (t :: TypeRep t)))) env =
  Typed (Type.App (typeRep @[]) t) (Lit ([] :: [t]))
tc (UList [x] Nothing) env =
  case tc x env of
    Typed rep t' ->
      Typed (Type.App (typeRep @[]) rep) (App (Lit (:[])) t')
tc (UList (x:xs) Nothing) env =
  case (tc x env, tc (UList xs Nothing) env) of
    (Typed a_rep a, Typed as_rep as) ->
      case Type.eqTypeRep (Type.App (typeRep @[]) a_rep) as_rep of
        Just Type.HRefl ->
          Typed as_rep (App (App (Lit (:)) a) as)
tc UList{} env = error "List must either be [x,..] or [] @T"

-- Make a well-typed literal - e.g. @lit Text.length@ - which can be
-- embedded in the untyped AST.
lookupVar :: String -> TyEnv g -> Typed (Var g)
lookupVar str Nil = error $ "Variable not found: " ++ str
lookupVar v (Cons (Singleton s) ty e)
  | v == s = Typed ty (ZVar id)
  | otherwise = case lookupVar v e of
      Typed ty v -> Typed ty (SVar v)
lookupVar v (Cons (Tuple ss) ty e)
  | Just i <- lookup v $ zip ss [0..] =
    case ty of
      Type.App (Type.App tup x) y
       | Just Type.HRefl <- Type.eqTypeRep tup (typeRep @(,)) ->
          case i of
            0 -> Typed x $ ZVar \(a,_) -> a
            1 -> Typed y $ ZVar \(_,b) -> b
      Type.App (Type.App (Type.App tup x) y) z
       | Just Type.HRefl <- Type.eqTypeRep tup (typeRep @(,,)) ->
          case i of
            0 -> Typed x $ ZVar \(a,_,_) -> a
            1 -> Typed y $ ZVar \(_,b,_) -> b
            2 -> Typed z $ ZVar \(_,_,c) -> c
  | otherwise = case lookupVar v e of
      Typed ty v -> Typed ty (SVar v)

--------------------------------------------------------------------------------
-- Desugar expressions

data DesugarError = InvalidConstructor String | InvalidVariable String | UnknownType String | UnsupportedSyntax String | BadParameterSyntax String | KindError
  deriving (Show, Eq)

nestedTyApps :: HSE.Exp HSE.SrcSpanInfo -> Maybe (HSE.QName HSE.SrcSpanInfo, [HSE.Type HSE.SrcSpanInfo])
nestedTyApps = go [] where
  go acc (HSE.App _ (HSE.Var _ qname) (HSE.TypeApp _ ty)) = pure (qname, ty:acc)
  go acc (HSE.App _ e (HSE.TypeApp _ ty)) = go (ty:acc) e
  go acc _ = Nothing

desugarExp :: Map String UTerm -> HSE.Exp HSE.SrcSpanInfo -> Either DesugarError UTerm
desugarExp globals = go where
  go = \case
    HSE.Paren _ x -> go x
    HSE.If _ i t e -> UIf <$> go i <*> go t <*> go e
    HSE.Tuple _ HSE.Boxed terms -> UTuple <$> traverse go terms
    HSE.List _ xs -> UList <$> traverse go xs <*> pure Nothing
    HSE.App _ (HSE.List _ xs) (HSE.TypeApp _ ty) -> UList <$> traverse go xs <*> fmap Just (desugarType ty)
    HSE.Lit _ lit' -> case lit' of
      HSE.Char _ char _ -> pure $ lit char
      HSE.String _ string _ -> pure $ lit $ Text.pack string
      HSE.Int _ int _ -> pure $ lit (fromIntegral int :: Int)
    app@HSE.App{} | Just (qname, tys) <- nestedTyApps app -> do
      reps <- traverse desugarType tys
      desugarQName globals qname reps
    HSE.Var _ qname ->
      desugarQName globals qname []
    HSE.App _ f x -> UApp <$> go f <*> go x
    HSE.InfixApp _ x (HSE.QVarOp l f) y -> UApp <$> (UApp <$> go (HSE.Var l f) <*> go x) <*> go y
    HSE.Lambda _ pats e -> do
      args <- traverse desugarArg pats
      e' <- go e
      pure $ foldr (\(name,ty) inner  -> ULam name ty inner)  e' args
    HSE.Con _ qname ->
      case qname of
        HSE.Qual _ (HSE.ModuleName _ prefix) (HSE.Ident _ string)
          | Just uterm <- Map.lookup (prefix ++ "." ++ string) supportedLits ->
            pure uterm
        _ -> Left $ InvalidConstructor $ show qname
    HSE.Do _ stmts -> do
      let loop f [HSE.Qualifier _ e] = f <$> go e
          loop f (s:ss) = do
            case s of
              HSE.Generator _ pat e -> do
                 (s, rep) <- desugarArg pat
                 m <- go e
                 loop (f . (\f -> UBind m (ULam s rep f))) ss
              HSE.LetStmt _ (HSE.BDecls _ [HSE.PatBind _ pat (HSE.UnGuardedRhs _ e) Nothing]) -> do
                 (s, rep) <- desugarArg pat
                 value <- go e
                 loop (f . (\f -> UApp (ULam s rep f) value)) ss
              HSE.Qualifier _ e -> do
                e' <- go e
                loop (f . UApp (UApp then' e')) ss
          loop _ _ = error "Malformed do-notation!"
      loop id stmts
    e -> Left $ UnsupportedSyntax $ show e

desugarQName :: Map String UTerm -> HSE.QName HSE.SrcSpanInfo -> [SomeStarType] -> Either DesugarError UTerm
desugarQName globals qname [] =
  case qname of
    HSE.UnQual _ (HSE.Ident _ string) -> Right $ UVar string
    HSE.Qual _ (HSE.ModuleName _ "Main") (HSE.Ident _ string)
      | Just uterm  <- Map.lookup string globals ->
        pure uterm
    HSE.Qual _ (HSE.ModuleName _ prefix) (HSE.Ident _ string)
      | Just uterm <- Map.lookup (prefix ++ "." ++ string) supportedLits ->
        pure uterm
    HSE.UnQual _ (HSE.Symbol _ string)
      | Just uterm <- Map.lookup string supportedLits ->
        pure uterm
    _ -> Left $ InvalidVariable $ show qname
desugarQName globals qname treps =
  case qname of
    HSE.Qual _ (HSE.ModuleName _ prefix) (HSE.Ident _ string)
      | Just forall' <- Map.lookup (prefix ++ "." ++ string) polyLits ->
        pure (UForall treps forall')
    HSE.UnQual _ (HSE.Symbol _ string)
      | Just forall' <- Map.lookup string polyLits ->
        pure (UForall treps forall')
    _ -> Left $ InvalidVariable $ show qname

desugarArg :: HSE.Pat HSE.SrcSpanInfo -> Either DesugarError (Binding, SomeStarType)
desugarArg (HSE.PatTypeSig _ (HSE.PVar _ (HSE.Ident _ i)) typ) = fmap (Singleton i,) (desugarType typ)
desugarArg (HSE.PatTypeSig _ (HSE.PTuple _ HSE.Boxed idents) typ)
  | Just idents <- traverse desugarIdent idents = fmap (Tuple idents,) (desugarType typ)
desugarArg (HSE.PParen _ p) = desugarArg p
desugarArg p = Left $ BadParameterSyntax $ show p

desugarIdent :: HSE.Pat HSE.SrcSpanInfo -> Maybe String
desugarIdent (HSE.PVar _ (HSE.Ident _ s)) = Just s
desugarIdent _ = Nothing

--------------------------------------------------------------------------------
-- Desugar types

desugarType :: HSE.Type HSE.SrcSpanInfo -> Either DesugarError SomeStarType
desugarType t = do
  someRep <- go t
  case someRep of
    StarTypeRep t -> pure (SomeStarType t)
    _ -> Left KindError

  where
  go :: HSE.Type HSE.SrcSpanInfo -> Either DesugarError SomeTypeRep
  go = \case
    HSE.TyTuple _ HSE.Boxed types -> do
      tys <- traverse go types
      case tys of
        [StarTypeRep a,StarTypeRep b] ->
          pure $ StarTypeRep (Type.App (Type.App (typeRep @(,)) a) b)
        [StarTypeRep a,StarTypeRep b, StarTypeRep c] ->
          pure $ StarTypeRep (Type.App (Type.App (Type.App (typeRep @(,,)) a) b) c)
        [StarTypeRep a,StarTypeRep b, StarTypeRep c, StarTypeRep d] ->
          pure $ StarTypeRep (Type.App (Type.App (Type.App (Type.App (typeRep @(,,,)) a) b) c) d)
    HSE.TyParen _ x -> go x
    HSE.TyCon _ (HSE.UnQual _ (HSE.Ident _ name))
      | Just rep <- Map.lookup name supportedTypeConstructors -> pure rep
    HSE.TyCon _ (HSE.Special _ HSE.UnitCon{}) -> pure $ StarTypeRep $ typeRep @()
    HSE.TyList _ inner -> do
      rep <- go inner
      case rep of
        StarTypeRep t -> pure $ StarTypeRep $ Type.App (typeRep @[]) t
        _ -> Left KindError
    HSE.TyFun l a b -> do
      a' <- go a
      b' <- go b
      case (a', b') of
        (StarTypeRep aRep, StarTypeRep bRep) ->
          pure $ StarTypeRep (Type.Fun aRep bRep)
        _ -> Left KindError
    HSE.TyApp l f a -> do
      f' <- go f
      a' <- go a
      case applyTypes f' a' of
        Just someTypeRep -> pure someTypeRep
        _ -> Left KindError
    t -> Left $ UnknownType $ show t

-- | Supports up to 3-ary type functions, but not more.
applyTypes :: SomeTypeRep -> SomeTypeRep -> Maybe SomeTypeRep
applyTypes (SomeTypeRep f) (SomeTypeRep a) = do
  Type.HRefl <- Type.eqTypeRep (typeRepKind a) (typeRep @Type)
  if
   | Just Type.HRefl <- Type.eqTypeRep (typeRepKind f) (typeRep @(Type -> Type)) ->
     pure $ SomeTypeRep $ Type.App f a
   | Just Type.HRefl <- Type.eqTypeRep (typeRepKind f) (typeRep @(Type -> Type -> Type)) ->
     pure $ SomeTypeRep $ Type.App f a
   | Just Type.HRefl <- Type.eqTypeRep (typeRepKind f) (typeRep @(Type -> Type -> Type -> Type)) ->
     pure $ SomeTypeRep $ Type.App f a
   | otherwise -> Nothing

desugarTypeSpec :: Spec
desugarTypeSpec = do
  it "desugarType" $ do
    shouldBe (try "Bool") (Right (SomeStarType $ typeRep @Bool))
    shouldBe (try "Int") (Right (SomeStarType $ typeRep @Int))
    shouldBe (try "Bool -> Int") (Right (SomeStarType $ typeRep @(Bool -> Int)))
    shouldBe (try "()") (Right (SomeStarType $ typeRep @()))
    shouldBe (try "[Int]") (Right (SomeStarType $ typeRep @[Int]))
  where try e = case fmap desugarType $ HSE.parseType e of
           HSE.ParseOk r -> r
           _ -> error "Parse failed."

--------------------------------------------------------------------------------
-- Desugar all bindings

desugarAll :: [(String, HSE.Exp HSE.SrcSpanInfo)] -> Either DesugarError [(String, UTerm)]
desugarAll = flip evalStateT Map.empty . traverse go . Graph.flattenSCCs . stronglyConnected where
  go :: (String, HSE.Exp HSE.SrcSpanInfo) -> StateT (Map String UTerm) (Either DesugarError) (String, UTerm)
  go (name, expr) = do
    globals <- get
    uterm <- lift $ desugarExp globals expr
    modify' $ Map.insert name uterm
    pure (name, uterm)

--------------------------------------------------------------------------------
-- Occurs check

anyCycles :: [(String, HSE.Exp HSE.SrcSpanInfo)] -> Bool
anyCycles =
  any isCycle .
  stronglyConnected
  where
    isCycle = \case
      Graph.CyclicSCC{} -> True
      _ -> False

stronglyConnected :: [(String, HSE.Exp HSE.SrcSpanInfo)] -> [Graph.SCC (String, HSE.Exp HSE.SrcSpanInfo)]
stronglyConnected =
  Graph.stronglyConnComp .
  map \thing@(name, e) -> (thing, name, freeVariables e)

anyCyclesSpec :: Spec
anyCyclesSpec = do
 it "anyCycles" do
   shouldBe (try [("foo","\\z -> x * Z.y"), ("bar","\\z -> Main.bar * Z.y")]) True
   shouldBe (try [("foo","\\z -> Main.bar * Z.y"), ("bar","\\z -> Main.foo * Z.y")]) True
   shouldBe (try [("foo","\\z -> x * Z.y"), ("bar","\\z -> Main.mu * Z.y")]) False
   shouldBe (try [("foo","\\z -> x * Z.y"), ("bar","\\z -> Main.foo * Z.y")]) False

  where
   try named =
    case traverse (\(n, e) -> (n, ) <$> HSE.parseExp e) named of
      HSE.ParseOk decls -> anyCycles decls
      _ -> error "Parse failed."

--------------------------------------------------------------------------------
-- Get free variables of an HSE expression

freeVariables :: HSE.Exp HSE.SrcSpanInfo -> [String]
freeVariables =
  Maybe.mapMaybe unpack .
  SYB.listify (const True :: HSE.QName HSE.SrcSpanInfo -> Bool)
  where
    unpack = \case
      HSE.Qual _ (HSE.ModuleName _ "Main") (HSE.Ident _ name) -> pure name
      _ -> Nothing

freeVariablesSpec :: Spec
freeVariablesSpec = do
 it "freeVariables" $ shouldBe (try "\\z -> Main.x * Z.y") ["x"]
  where try e = case fmap freeVariables $ HSE.parseExp e of
           HSE.ParseOk names -> names
           _ -> error "Parse failed."

--------------------------------------------------------------------------------
-- Supported type constructors

supportedTypeConstructors :: Map String SomeTypeRep
supportedTypeConstructors = Map.fromList [
  ("Bool", SomeTypeRep $ typeRep @Bool),
  ("Int", SomeTypeRep $ typeRep @Int),
  ("Char", SomeTypeRep $ typeRep @Char),
  ("Text", SomeTypeRep $ typeRep @Text),
  ("ByteString", SomeTypeRep $ typeRep @ByteString),
  ("ExitCode", SomeTypeRep $ typeRep @ExitCode),
  ("Maybe", SomeTypeRep $ typeRep @Maybe),
  ("Either", SomeTypeRep $ typeRep @Either),
  ("IO", SomeTypeRep $ typeRep @IO),
  ("ProcessConfig", SomeTypeRep $ typeRep @ProcessConfig)
  ]

--------------------------------------------------------------------------------
-- Support primitives

supportedLits :: Map String UTerm
supportedLits = Map.fromList [
   -- Text I/O
   ("Text.putStrLn", lit t_putStrLn),
   ("Text.hPutStr", lit t_hPutStr),
   ("Text.putStr", lit t_putStr),
   ("Text.getLine", lit t_getLine),
   ("Text.writeFile", lit t_writeFile),
   ("Text.readFile", lit t_readFile),
   ("Text.appendFile", lit t_appendFile),
   ("Text.readProcess", lit t_readProcess),
   ("Text.readProcess_", lit t_readProcess_),
   ("Text.readProcessStdout_", lit t_readProcessStdout_),
   ("Text.setStdin", lit t_setStdin),
   -- Text operations
   ("Text.eq", lit ((==) @Text)),
   ("Text.length", lit Text.length),
   ("Text.concat", lit Text.concat),
   ("Text.breakOn", lit Text.breakOn),
   ("Text.lines", lit Text.lines),
   ("Text.words", lit Text.words),
   ("Text.unlines", lit Text.unlines),
   ("Text.unwords", lit Text.unwords),
   ("Text.intercalate", lit Text.intercalate),
   ("Text.reverse", lit Text.reverse),
   ("Text.toLower", lit Text.toLower),
   ("Text.toUpper", lit Text.toUpper),
   -- Needs Char operations.
   -- ("Text.any", lit Text.any),
   -- ("Text.all", lit Text.all),
   -- ("Text.filter", lit Text.filter),
   ("Text.take", lit Text.take),
   ("Text.splitOn", lit Text.splitOn),
   ("Text.takeEnd", lit Text.takeEnd),
   ("Text.drop", lit Text.drop),
   ("Text.stripPrefix", lit Text.stripPrefix),
   ("Text.stripSuffix", lit Text.stripSuffix),
   ("Text.isSuffixOf", lit Text.isSuffixOf),
   ("Text.isPrefixOf", lit Text.isPrefixOf),
   ("Text.dropEnd", lit Text.dropEnd),
   ("Text.strip", lit Text.strip),
   ("Text.isPrefixOf", lit Text.isPrefixOf),
   ("Text.isSuffixOf", lit Text.isSuffixOf),
   ("Text.isInfixOf", lit Text.isInfixOf),
   -- Int operations
   ("Int.show", lit (Text.pack . show @Int)),
   ("Int.eq", lit ((==) @Int)),
   ("Int.plus", lit ((+) @Int)),
   ("Int.subtract", lit (subtract @Int)),
   -- Bytes I/O
   ("ByteString.hGet", lit ByteString.hGet),
   ("ByteString.hPutStr", lit ByteString.hPutStr),
   ("ByteString.readProcess", lit b_readProcess),
   ("ByteString.readProcess_", lit b_readProcess_),
   ("ByteString.readProcessStdout_", lit b_readProcessStdout_),
   -- Handles, buffering
   ("IO.stdout", lit IO.stdout),
   ("IO.stderr", lit IO.stderr),
   ("IO.stdin", lit IO.stdin),
   ("IO.hSetBuffering", lit IO.hSetBuffering),
   ("IO.NoBuffering", lit IO.NoBuffering),
   ("IO.LineBuffering", lit IO.LineBuffering),
   ("IO.BlockBuffering", lit IO.BlockBuffering),
   -- Errors
   ("Error.userError", lit Error.userError),
   -- Bool
   ("Bool.True", lit Bool.True),
   ("Bool.False", lit Bool.False),
   ("Bool.not", lit Bool.not),
   -- Get arguments
   ("Environment.getArgs", lit $ fmap (map Text.pack) getArgs),
   ("Environment.getEnvironment", lit $ fmap (map (bimap Text.pack Text.pack)) getEnvironment),
   ("Environment.getEnv", lit $ fmap Text.pack . getEnv . Text.unpack),
   -- Current directory
   ("Directory.getCurrentDirectory", lit (fmap Text.pack Dir.getCurrentDirectory)),
   ("Directory.listDirectory", lit (fmap (fmap Text.pack) . Dir.listDirectory . Text.unpack)),
   ("Directory.setCurrentDirectory", lit (Dir.setCurrentDirectory . Text.unpack)),
   -- Process
   ("Process.proc", lit $ \n xs -> proc (Text.unpack n) (map Text.unpack xs)),
   ("Process.setEnv", lit $ Process.setEnv @() @() @() . map (bimap Text.unpack Text.unpack)),
   ("Process.runProcess", lit $ runProcess @IO @() @() @()),
   ("Process.runProcess_", lit $ runProcess_ @IO @() @() @()),
   -- Lists
   ("List.and", lit (List.and @[])),
   ("List.or", lit (List.or @[])),
   -- Misc
   (">>", then')
  ]

then' :: UTerm
then' = lit ((Prelude.>>) :: IO () -> IO () -> IO ())

--------------------------------------------------------------------------------
-- Polymorphic primitives

polyLits :: Map String Forall
polyLits = Map.fromList [
  ("Error.ioError", Unconstrained \(TypeRep @a) ->
    Final (Typed (typeRep @(IOError -> IO a)) (Lit Error.ioError))),
  ("IO.pure", Unconstrained \(TypeRep @a) ->
    Final (Typed (typeRep @(a -> IO a)) (Lit pure))),
  -- Bool
   ("Bool.bool", Unconstrained \a ->
     Final (Typed (Type.Fun a (Type.Fun a (Type.Fun (typeRep @Bool) a))) (Lit Bool.bool))
   ),
  -- Data.Function
  ("Function.id", Unconstrained \a -> Final (Typed (Type.Fun a a) (Lit id))),
  ("Function.fix", Unconstrained \(TypeRep @a) ->
      Final $ typed (Fun.fix :: (a -> a) -> a)),
  -- Data.List
  ("List.cons", Unconstrained \(TypeRep @a) -> Final $
    typed ((:) :: a -> [a] -> [a])),
  ("List.concat", Unconstrained \(TypeRep @a) -> Final $
    typed (List.concat :: [[a]] -> [a])),
  ("List.drop", Unconstrained \(TypeRep @a) -> Final $
    typed (List.drop :: Int -> [a] -> [a])),
  ("List.take", Unconstrained \(TypeRep @a) -> Final $
    typed (List.take :: Int -> [a] -> [a])),
  ("List.map", Unconstrained \(TypeRep @a) -> Unconstrained \(TypeRep @b) -> Final $
      typed (map :: (a -> b) -> [a] -> [b])
  ) ,
  ("List.lookup", Constrained \(TypeRep @a) -> Unconstrained \(TypeRep @b) -> Final $
      typed (List.lookup :: a -> [(a,b)] -> Maybe b)
  ) ,
  ("IO.mapM_", Unconstrained \(TypeRep @a) -> Final $
      typed (mapM_ :: (a -> IO ()) -> [a] -> IO ())
  ),
  ("IO.forM_", Unconstrained \(TypeRep @a) -> Final $
      typed (forM_ :: [a] -> (a -> IO ()) -> IO ())
  ),
  -- Maybe
  ("Maybe.maybe", Unconstrained \(TypeRep @a) -> Unconstrained \(TypeRep @b) -> Final $
    typed (maybe :: b -> (a -> b) -> Maybe a -> b)
  ),
  ("Maybe.Nothing", Unconstrained \(TypeRep @a) -> Final $
    typed (Nothing :: Maybe a)
  ),
  ("Maybe.Just", Unconstrained \(TypeRep @a) -> Final $
    typed (Just :: a -> Maybe a)
  ),
  ("Maybe.listToMaybe", Unconstrained \(TypeRep @a) -> Final $
    typed (Maybe.listToMaybe :: [a] -> Maybe a)
  ),
  -- Either
  ("Either.either", Unconstrained \(TypeRep @a) -> Unconstrained \(TypeRep @b) -> Unconstrained \(TypeRep @x) -> Final $
    typed (either :: (a -> x) -> (b -> x) -> Either a b -> x)
  ),
  ("Either.Left", Unconstrained \(TypeRep @a) -> Unconstrained \(TypeRep @b) -> Final $
    typed (Left :: a -> Either a b)
  ),
  ("Either.Right", Unconstrained \(TypeRep @a) -> Unconstrained \(TypeRep @b) -> Final $
    typed (Right :: b -> Either a b)
  ),
  -- Async
  ("Async.concurrently", Unconstrained \(TypeRep @a) -> Unconstrained \(TypeRep @b) -> Final $
    typed (Async.concurrently :: IO a -> IO b -> IO (a,b))
  ),
  ("Async.race", Unconstrained \(TypeRep @a) -> Unconstrained \(TypeRep @b) -> Final $
    typed (Async.race :: IO a -> IO b -> IO (Either a b))
  ),
  -- Type-class constrained functions
  ("Text.show", Constrained \(TypeRep @a) -> Final $
    typed (Text.pack . Show.show :: a -> Text)),
  ("Text.print", Constrained \(TypeRep @a) -> Final $
    typed (t_putStrLn . Text.pack . Show.show :: a -> IO ())),
  ("Eq.eq", Constrained \(TypeRep @a) -> Final $
     typed ((Eq.==) :: a -> a -> Bool)),
  ("Ord.lt", Constrained \(TypeRep @a) -> Final $
     typed ((Ord.<) :: a -> a -> Bool)),
  ("Ord.gt", Constrained \(TypeRep @a) -> Final $
     typed ((Ord.>) :: a -> a -> Bool))
 ]

--------------------------------------------------------------------------------
-- UTF-8 specific operations without all the environment gubbins
--
-- Much better than what Data.Text.IO provides

t_setStdin :: Text -> ProcessConfig () () () -> ProcessConfig () () ()
t_setStdin text = setStdin (byteStringInput (L.fromStrict (Text.encodeUtf8 text)))

t_readProcess :: ProcessConfig () () () -> IO (ExitCode, Text, Text)
t_readProcess c = do
  (code, out, err) <- b_readProcess c
  pure (code, Text.decodeUtf8 out, Text.decodeUtf8 err)

t_readProcess_ :: ProcessConfig () () () -> IO (Text, Text)
t_readProcess_ c = do
  (out, err) <- b_readProcess_ c
  pure (Text.decodeUtf8 out, Text.decodeUtf8 err)

t_readProcessStdout_ :: ProcessConfig () () () -> IO Text
t_readProcessStdout_ c = do
  out <- b_readProcessStdout_ c
  pure (Text.decodeUtf8 out)

t_putStrLn :: Text -> IO ()
t_putStrLn = ByteString.hPutBuilder IO.stdout . (<>"\n") . ByteString.byteString . Text.encodeUtf8

t_hPutStr :: IO.Handle -> Text -> IO ()
t_hPutStr h = ByteString.hPutBuilder h . ByteString.byteString . Text.encodeUtf8

t_putStr :: Text -> IO ()
t_putStr = t_hPutStr IO.stdout

t_getLine :: IO Text
t_getLine = fmap Text.decodeUtf8 ByteString.getLine

t_writeFile :: Text -> Text -> IO ()
t_writeFile fp t = ByteString.writeFile (Text.unpack fp) (Text.encodeUtf8 t)

t_appendFile :: Text -> Text -> IO ()
t_appendFile fp t = ByteString.appendFile (Text.unpack fp) (Text.encodeUtf8 t)

t_readFile :: Text -> IO Text
t_readFile fp = fmap Text.decodeUtf8 (ByteString.readFile (Text.unpack fp))

--------------------------------------------------------------------------------
-- ByteString operations

b_readProcess :: ProcessConfig () () () -> IO (ExitCode, ByteString, ByteString)
b_readProcess c = do
  (code, out, err) <- readProcess c
  pure (code, L.toStrict out, L.toStrict err)

b_readProcess_ :: ProcessConfig () () () -> IO (ByteString, ByteString)
b_readProcess_ c = do
  (out, err) <- readProcess_ c
  pure (L.toStrict out, L.toStrict err)

b_readProcessStdout_ :: ProcessConfig () () () -> IO ByteString
b_readProcessStdout_ c = do
  out <- readProcessStdout_ c
  pure (L.toStrict out)
