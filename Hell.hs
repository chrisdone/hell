{-# LANGUAGE ExistentialQuantification, TypeApplications, BlockArguments #-}
{-# LANGUAGE GADTs, PolyKinds, TupleSections, StandaloneDeriving, Rank2Types #-}
{-# LANGUAGE LambdaCase, ScopedTypeVariables, PatternSynonyms, OverloadedStrings #-}

-- * Original type checker code by Stephanie Weirich at Dagstuhl (Sept 04)
-- * Modernized with Type.Reflection, also by Stephanie
-- * Polytyped prims added
-- * Type-class dictionary passing added
-- * Dropped UType in favor of TypeRep

import qualified Data.Graph as Graph
import qualified Data.Bool as Bool
import qualified Data.Map as Map
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

import System.Process.Typed
import Control.Monad.State
import System.Environment
import Data.Map (Map)
import Data.Text (Text)
import Data.ByteString (ByteString)
import Data.Constraint
import GHC.Types
import Type.Reflection (TypeRep, typeRepKind, typeRep)
import Test.Hspec

--------------------------------------------------------------------------------
-- Untyped AST

data UTerm
  = UVar String
  | ULam Binding SomeTRep UTerm
  | UApp UTerm UTerm
  | UForall [SomeTRep] Forall
  | ULit (forall g. Typed (Term g))
  | UBind UTerm UTerm
  | UList [UTerm] (Maybe SomeTRep)

data Binding = Singleton String | Tuple [String]

data Forall
  = More (forall (a :: Type) g. TypeRep a -> Forall)
  | Final (forall g. Typed (Term g))

lit :: Type.Typeable a => a -> UTerm
lit l = ULit (Typed (Type.typeOf l) (Lit l))

typed :: Type.Typeable a => a -> Typed (Term g)
typed l = Typed (Type.typeOf l) (Lit l)

--------------------------------------------------------------------------------
-- Typed AST

data Term g t where
  Var :: Var g t -> Term g t
  Lam :: TypeRep (a :: Type) -> Term (g, a) b -> Term g (a -> b)
  App :: Term g (s -> t) -> Term g s -> Term g t
  Lit :: a -> Term g a

data Var g t where
  ZVar :: (t -> a) -> Var (h, t) a
  SVar :: Var h t -> Var (h, s) t

data Typed (thing :: Type -> Type) = forall ty. Typed (TypeRep (ty :: Type)) (thing ty)

--------------------------------------------------------------------------------
-- Type checker helpers

data SomeTRep = forall (a :: Type). SomeTRep (TypeRep a)
deriving instance Show SomeTRep
instance Eq SomeTRep where
  SomeTRep x == SomeTRep y = Type.SomeTypeRep x == Type.SomeTypeRep y

-- The type environment and lookup
data TyEnv g where
  Nil :: TyEnv g
  Cons :: Binding -> TypeRep (t :: Type) -> TyEnv h -> TyEnv (h, t)

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
-- Type checker

tc :: UTerm -> TyEnv g -> Typed (Term g)
tc (UVar v) env = case lookupVar v env of
  Typed ty v -> Typed ty (Var v)
tc (ULam s (SomeTRep bndr_ty') body) env =
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
  go :: [SomeTRep] -> Forall -> Typed (Term g)
  go [] (Final typed) = typed
  go (SomeTRep rep:reps) (More f) = go reps (f rep)
  go _ _ = error "forall type arguments mismatch."


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
tc (UList [] (Just (SomeTRep (t :: TypeRep t)))) env =
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

--------------------------------------------------------------------------------
-- Evaluator

eval :: env -> Term env t -> t
eval env (Var v) = lookp v env
eval env (Lam _ e) = \x -> eval (env, x) e
eval env (App e1 e2) = (eval env e1) (eval env e2)
eval _env (Lit a) = a

lookp :: Var env t -> env -> t
lookp (ZVar slot) (_, x) = slot x
lookp (SVar v) (env, x) = lookp v env

--------------------------------------------------------------------------------
-- Top-level example

check :: UTerm -> TyEnv () -> Typed (Term ())
check = tc

--------------------------------------------------------------------------------
-- Desugar expressions

data DesugarError = InvalidConstructor String | InvalidVariable String | UnknownType String | UnsupportedSyntax String | BadParameterSyntax String
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

desugarQName :: Map String UTerm -> HSE.QName HSE.SrcSpanInfo -> [SomeTRep] -> Either DesugarError UTerm
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
      | Just forall <- Map.lookup (prefix ++ "." ++ string) polyLits ->
        pure (UForall treps forall)
    HSE.UnQual _ (HSE.Symbol _ string)
      | Just forall <- Map.lookup string polyLits ->
        pure (UForall treps forall)
    _ -> Left $ InvalidVariable $ show qname

desugarArg :: HSE.Pat HSE.SrcSpanInfo -> Either DesugarError (Binding, SomeTRep)
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

desugarType :: HSE.Type HSE.SrcSpanInfo -> Either DesugarError SomeTRep
desugarType = go where
  go :: HSE.Type HSE.SrcSpanInfo -> Either DesugarError SomeTRep
  go = \case
    HSE.TyTuple _ HSE.Boxed types -> do
      tys <- traverse go types
      case tys of
        [SomeTRep a,SomeTRep b] ->
          pure $ SomeTRep (Type.App (Type.App (typeRep @(,)) a) b)
        [SomeTRep a,SomeTRep b, SomeTRep c] ->
          pure $ SomeTRep (Type.App (Type.App (Type.App (typeRep @(,,)) a) b) c)
        [SomeTRep a,SomeTRep b, SomeTRep c, SomeTRep d] ->
          pure $ SomeTRep (Type.App (Type.App (Type.App (Type.App (typeRep @(,,,)) a) b) c) d)
    HSE.TyParen _ x -> go x
    HSE.TyCon _ (HSE.UnQual _ (HSE.Ident _ name))
      | Just rep <- Map.lookup name supportedTypeConstructors -> pure rep
    HSE.TyCon _ (HSE.Special _ HSE.UnitCon{}) -> pure $ SomeTRep $ typeRep @()
    HSE.TyList _ inner -> do
      SomeTRep t <- go inner
      pure $ SomeTRep $ Type.App (typeRep @[]) t
    HSE.TyFun l a b -> do
      SomeTRep aRep <- go a
      SomeTRep bRep <- go b
      pure $ SomeTRep (Type.Fun aRep bRep)
    HSE.TyApp l (HSE.TyCon _ (HSE.UnQual _ (HSE.Ident _ "IO"))) a -> do
      SomeTRep aRep <- go a
      pure $ SomeTRep (Type.App (typeRep @IO) aRep)
    t -> Left $ UnknownType $ show t

desugarTypeSpec :: Spec
desugarTypeSpec = do
  it "desugarType" $ do
    shouldBe (try "Bool") (Right (SomeTRep $ typeRep @Bool))
    shouldBe (try "Int") (Right (SomeTRep $ typeRep @Int))
    shouldBe (try "Bool -> Int") (Right (SomeTRep $ typeRep @(Bool -> Int)))
    shouldBe (try "()") (Right (SomeTRep $ typeRep @()))
    shouldBe (try "[Int]") (Right (SomeTRep $ typeRep @[Int]))
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
-- Test everything

spec :: Spec
spec = do
  anyCyclesSpec
  freeVariablesSpec
  desugarTypeSpec

--------------------------------------------------------------------------------
-- Supported type constructors

supportedTypeConstructors :: Map String SomeTRep
supportedTypeConstructors = Map.fromList [
  ("Bool", SomeTRep $ typeRep @Bool),
  ("Int", SomeTRep $ typeRep @Int),
  ("Char", SomeTRep $ typeRep @Char),
  ("Text", SomeTRep $ typeRep @Text),
  ("ByteString", SomeTRep $ typeRep @ByteString),
  ("ExitCode", SomeTRep $ typeRep @ExitCode)
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
   -- Text operations
   ("Text.length", lit Text.length),
   -- Int operations
   ("Int.show", lit (Text.pack . show @Int)),
   -- Bytes I/O
   ("ByteString.hGet", lit ByteString.hGet),
   ("ByteString.hPutStr", lit ByteString.hPutStr),
   ("ByteString.readProcess", lit b_readProcess),
   ("ByteString.readProcess_", lit b_readProcess_),
   -- Handles, buffering
   ("IO.stdout", lit IO.stdout),
   ("IO.stderr", lit IO.stderr),
   ("IO.stdin", lit IO.stdin),
   ("IO.hSetBuffering", lit IO.hSetBuffering),
   ("IO.NoBuffering", lit IO.NoBuffering),
   ("IO.LineBuffering", lit IO.LineBuffering),
   ("IO.BlockBuffering", lit IO.BlockBuffering),
   -- Get arguments
   ("Env.getArgs", lit getArgs),
   -- Process
   ("Proc.proc", lit $ \n xs -> proc (Text.unpack n) (map Text.unpack xs)),
   ("Proc.runProcess", lit $ runProcess @IO @() @() @()),
   ("Proc.runProcess_", lit $ runProcess_ @IO @() @() @()),

   -- Misc
   (">>", then')
  ]

then' :: UTerm
then' = lit ((Prelude.>>) :: IO () -> IO () -> IO ())

--------------------------------------------------------------------------------
-- Polymorphic primitives

polyLits :: Map String Forall
polyLits = Map.fromList [
  -- Data.Function
  ("Fun.id", More \a -> Final (Typed (Type.Fun a a) (Lit id))),
  ("Fun.fix", More \(a :: TypeRep a) -> Type.withTypeable a $
      Final $ typed (Fun.fix :: (a -> a) -> a)),
  -- Data.List
  ("List.mapM_", More \(a :: TypeRep a) -> Final $
      Type.withTypeable a $
      typed (mapM_ :: (a -> IO ()) -> [a] -> IO ())
  ) ,
  ("List.map", More \(a :: TypeRep a) -> More \(b :: TypeRep b) -> Final $
      Type.withTypeable a $ Type.withTypeable b $
      typed (Prelude.map :: (a -> b) -> [a] -> [b])
  )
 ]

--------------------------------------------------------------------------------
-- UTF-8 specific operations without all the environment gubbins
--
-- Much better than what Data.Text.IO provides

t_readProcess :: ProcessConfig () () () -> IO (ExitCode, Text, Text)
t_readProcess c = do
  (code, out, err) <- b_readProcess c
  pure (code, Text.decodeUtf8 out, Text.decodeUtf8 err)

t_readProcess_ :: ProcessConfig () () () -> IO (Text, Text)
t_readProcess_ c = do
  (out, err) <- b_readProcess_ c
  pure (Text.decodeUtf8 out, Text.decodeUtf8 err)

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

------------------------------------------------------------------------------
-- Main entry point

main :: IO ()
main = do
  (filePath:_) <- getArgs
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

--------------------------------------------------------------------------------
-- Get declarations from the module

parseModule :: HSE.Module HSE.SrcSpanInfo -> HSE.ParseResult [(String, HSE.Exp HSE.SrcSpanInfo)]
parseModule (HSE.Module _ Nothing [] [] decls) =
  traverse parseDecl decls
  where
    parseDecl (HSE.PatBind _ (HSE.PVar _ (HSE.Ident _ string)) (HSE.UnGuardedRhs _ exp') Nothing) =
          pure (string, exp')
    parseDecl _ = error "Can't parse that!"
