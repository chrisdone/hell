{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
--
-- Welcome to Hell
--
-- Haskell as a scripting language!
--
-- Special thanks to Stephanie Weirich, whose type-safe typechecker
-- this is built upon, and for the Type.Reflection module, which has
-- made some of this more ergonomic.
{-# OPTIONS_GHC -Wno-unused-foralls #-}

module Main (main) where

-- All modules tend to be imported qualified by their last component,
-- e.g. 'Data.Graph' becomes 'Graph', and are then exposed to the Hell
-- guest language as such.

#if __GLASGOW_HASKELL__ >= 906
import Control.Monad
#endif
import Control.Exception (evaluate)
import qualified Control.Concurrent as Concurrent
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Aeson (Value)
import qualified Data.Aeson as Json
import qualified Data.Aeson.KeyMap as KeyMap
import Data.Bifunctor
import qualified Data.Bool as Bool
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Builder as ByteString hiding (writeFile)
import qualified Data.ByteString.Lazy as L
import Data.Containers.ListUtils
import qualified Data.Either as Either
import qualified Data.Eq as Eq
import Data.Foldable
import qualified Data.Function as Function
import qualified Data.Generics as SYB
import qualified Data.Graph as Graph
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map.Strict (Map)
import qualified Data.Maybe as Maybe
import qualified Data.Ord as Ord
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Tree (Tree)
import qualified Data.Tree as Tree
import qualified Data.Text.Encoding as Text
import qualified Data.Text.IO as Text
import Data.Traversable
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void
import GHC.TypeLits
import GHC.Types (Type)
import qualified Language.Haskell.Exts as HSE
import Language.Haskell.TH (Q)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Instances ()
import qualified Language.Haskell.TH.Syntax as TH
import Lucid hiding (Term, for_, term)
import qualified Options.Applicative as Options
import Options.Applicative (Parser)
import qualified System.Directory as Dir
import System.Environment
import qualified System.Exit as Exit
import qualified System.IO as IO
import qualified System.IO.Temp as Temp
import System.Process.Typed as Process
import qualified System.Timeout as Timeout
import Test.Hspec
import qualified Text.Read as Read
import qualified Text.Show as Show
import Type.Reflection (SomeTypeRep (..), TypeRep, typeRep, typeRepKind, pattern TypeRep)
import qualified Type.Reflection as Type
import qualified UnliftIO.Async as Async

------------------------------------------------------------------------------
-- Main entry point

-- | Commands available.
data Command
  = Run FilePath
  | Check FilePath
  | Version

-- | Main entry point.
main :: IO ()
main = do
  args <- getArgs
  case args of
    (x : ys)
      | not (List.isPrefixOf "-" x) -> withArgs ys $ dispatch (Run x)
    _ -> dispatch =<< Options.execParser opts
  where
    opts =
      Options.info
        (commandParser Options.<**> Options.helper)
        ( Options.fullDesc
            <> Options.progDesc "Runs and typechecks Hell scripts"
            <> Options.header "hell - A Haskell-driven scripting language"
        )

-- | Command options.
commandParser :: Options.Parser Command
commandParser =
  Options.asum
    [ Run <$> Options.strArgument (Options.metavar "FILE" <> Options.help "Run the given .hell file"),
      Check <$> Options.strOption (Options.long "check" <> Options.metavar "FILE" <> Options.help "Typecheck the given .hell file"),
      Version <$ Options.flag () () (Options.long "version" <> Options.help "Print the version")
    ]

-- | Version of Hell.
hellVersion :: Text
hellVersion = "2025-01-13"

-- | Dispatch on the command.
dispatch :: Command -> IO ()
dispatch Version = Text.putStrLn hellVersion
dispatch (Run filePath) = do
  action <- compileFile filePath
  eval () action
dispatch (Check filePath) = do
  compileFile filePath >>= void . evaluate

--------------------------------------------------------------------------------
-- Compiler

-- | Parses the file with HSE, desugars it, infers it, checks it,
-- returns it. Or throws an error.
compileFile :: FilePath -> IO (Term () (IO ()))
compileFile filePath = do
  result <- parseFile filePath
  case result of
    Left e -> error $ e
    Right File{terms,types}
      | anyCycles terms -> error "Cyclic bindings are not supported!"
      | anyCycles types -> error "Cyclic types are not supported!"
      | otherwise ->
          case desugarAll types terms of
            Left err -> error $ prettyString err
            Right dterms ->
              case lookup "main" dterms of
                Nothing -> error "No main declaration!"
                Just main' ->
                  case inferExp mempty main' of
                    Left err -> error $ prettyString err
                    Right uterm ->
                      case check uterm Nil of
                        Left err -> error $ prettyString err
                        Right (Typed t ex) ->
                          case Type.eqTypeRep (typeRepKind t) (typeRep @Type) of
                            Nothing -> error $ "Kind error, that's nowhere near an IO ()!"
                            Just Type.HRefl ->
                              case Type.eqTypeRep t (typeRep @(IO ())) of
                                Just Type.HRefl ->
                                  pure ex
                                Nothing -> error $ "Type isn't IO (), but: " ++ show t

--------------------------------------------------------------------------------
-- Get declarations from the module

parseModule :: HSE.Module HSE.SrcSpanInfo -> HSE.ParseResult File
parseModule (HSE.Module _ Nothing [] [] decls) = do
  termsAndTypes <- traverse parseDecl decls
  let terms = concatMap fst termsAndTypes
      types = concatMap snd termsAndTypes
  let names = map fst terms
      tyNames = map fst types
  if Set.size (Set.fromList names) == length names &&
     Set.size (Set.fromList tyNames) == length tyNames
    then pure File{terms,types}
    else fail "Duplicate names!"
  where
    parseDecl (HSE.PatBind _ (HSE.PVar _ (HSE.Ident _ string)) (HSE.UnGuardedRhs _ exp') Nothing) =
      pure ([(string, exp')], types)
        where types = []
    parseDecl (HSE.DataDecl _ HSE.DataType {} Nothing (HSE.DHead _ name) [qualConDecl] []) =
      do (termName,termExpr,typeName,typ) <- parseDataDecl name qualConDecl
         pure ([(termName,termExpr)], [(typeName,typ)])
    parseDecl (HSE.DataDecl _ HSE.DataType {} Nothing (HSE.DHead _ name) qualConDecls []) =
      do (terms, tyname, typ) <- parseSumDecl name qualConDecls
         pure (terms, [(tyname,typ)])
    parseDecl _ = fail "Can't parse that!"
parseModule _ = fail "Module headers aren't supported."

-- data Value = Text Text | Number Int
-- \ x ->
--   hell:Hell.Tagged @"Main.Value"
--     @(Variant (ConsL "Number" Int (ConsL "Text" Text NilL)))
--     (Variant.left @"Number" x)
-- \ x ->
--   hell:Hell.Tagged @"Main.Value"
--     @(Variant (ConsL "Number" Int (ConsL "Text" Text NilL)))
--     (Variant.right (Variant.left @"Text" x))
parseSumDecl :: (l ~ HSE.SrcSpanInfo) => HSE.Name l -> [HSE.QualConDecl l] -> HSE.ParseResult ([(String, HSE.Exp HSE.SrcSpanInfo)],
          -- ^^^^^ constructor and term
             String, HSE.Type HSE.SrcSpanInfo)
          -- ^^^^^ type name and type
parseSumDecl (HSE.Ident _ tyname) conDecls0 = do
  conDecls <- fmap Map.fromList $ traverse parseConDecl conDecls0
  let variantType = desugarVariantType $ Map.toList conDecls
  let taggedVariantType =
        -- Example:              Tagged  "Main.Person"  (Variant ..)
        --                       vvvvvv  vvvvvvvv       vvvvvvvvvvv
        HSE.TyApp l (HSE.TyApp l (hellTaggedTyCon l) (tySym qualifiedName)) variantType
  -- Note: the constructors are sorted by name, to provide a canonical ordering.
  let terms = map (makeCons conDecls variantType) $ Map.toList conDecls
  pure (terms, tyname, taggedVariantType)
  where
    l = HSE.noSrcSpan
    makeCons conDecls variantType (conName, typ)
      | HSE.TyCon _ (HSE.Qual _ (HSE.ModuleName _ "hell:Hell") (HSE.Ident _ "Nullary")) <- typ =
          ( conName,
            appTagged variantType $
              desugarVariantCon True (Map.keys conDecls) conName
          )
      | otherwise = (conName, expr)
      where
        expr =
          HSE.Lambda l [HSE.PVar l (HSE.Ident l "x")] $
            appTagged variantType $
              desugarVariantCon False (Map.keys conDecls) conName
    qualifiedName = "Main." ++ tyname
    appTagged ty =
      HSE.App l $
        HSE.App
          l
          ( HSE.App
              l
              (hellTaggedCon l)
              (HSE.TypeApp l (tySym qualifiedName))
          )
          (HSE.TypeApp l ty)
    tySym s = HSE.TyPromoted l (HSE.PromotedString l s s)
parseSumDecl _ _ =
  fail "Sum type declaration not in supported format."

desugarVariantCon :: Bool -> [String] -> String -> HSE.Exp HSE.SrcSpanInfo
desugarVariantCon nullary cons thisCon = rights $ left
  where
    right _ = HSE.Var l (hellQName l "RightV")
    rights e = foldr (HSE.App l) e $ map right $ takeWhile (/= thisCon) cons
    left =
      if nullary
        then
          HSE.App
            l
            left0
            (HSE.Con l (hellQName l "Nullary"))
        else
          HSE.App
            l
            left0
            (HSE.Var l (HSE.UnQual l (HSE.Ident l "x")))
      where
        left0 =
          ( HSE.App
              l
              (HSE.Var l (hellQName l "LeftV"))
              (HSE.TypeApp l (tySym thisCon))
          )
    tySym s = HSE.TyPromoted l (HSE.PromotedString l s s)
    l = HSE.noSrcSpan

desugarVariantType :: [(String, HSE.Type HSE.SrcSpanInfo)] -> HSE.Type HSE.SrcSpanInfo
desugarVariantType = appRecord . foldr appCons nilL
  where
    appCons (name, typ) rest =
      HSE.TyApp l (HSE.TyApp l (HSE.TyApp l consL (tySym name)) typ) rest
    appRecord x =
      HSE.TyParen l (HSE.TyApp l (hellVariantTyCon l) x)
    tySym s = HSE.TyPromoted l (HSE.PromotedString l s s)
    nilL = hellNilTyCon l
    consL = hellConsTyCon l
    l = HSE.noSrcSpan

parseConDecl :: (MonadFail f) => HSE.QualConDecl l -> f (String, HSE.Type l)
parseConDecl (HSE.QualConDecl _ Nothing Nothing (HSE.ConDecl _ (HSE.Ident _ consName) [slot])) =
  pure (consName, slot)
parseConDecl (HSE.QualConDecl l Nothing Nothing (HSE.ConDecl _ (HSE.Ident _ consName) [])) =
  pure ( consName, hellTyCon l "Nullary")
parseConDecl _ = fail "Unsupported constructor declaration format."

parseDataDecl :: (l ~ HSE.SrcSpanInfo) =>
   HSE.Name l ->
   HSE.QualConDecl l ->
   HSE.ParseResult (String,    HSE.Exp HSE.SrcSpanInfo,
   --               ^^^^^^     ^^^^^^^^^^^^^^^^^^^^^^^
   -- Term constructor name... and its expr.

                    String, HSE.Type HSE.SrcSpanInfo)
   --               ^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^
   --          Type name... type content.
parseDataDecl (HSE.Ident _ tyname) (HSE.QualConDecl _ Nothing Nothing (HSE.RecDecl _ (HSE.Ident _ consName) fields)) = do
  -- Note: the fields are sorted by name.
  fields' <- fmap (List.sortBy (Ord.comparing fst) . concat) $ traverse getField fields
  let names = map fst fields'
  -- Technically the type checker is quite capable of handling this in
  -- a sound manner, but it's weird and Haskell disallows it, so we
  -- turn it off.
  when (List.nub names /= names) $
    fail "Field names cannot be repeated."
  let ( consExpr , typ ) = makeConstructor tyname fields'
  pure (consName, consExpr, tyname, typ)
  where
    getField (HSE.FieldDecl _ names typ) = do
      names' <- for names \case
        (HSE.Ident _ n) -> pure n
        _ -> fail "Invalid field name."
      pure $ map (,typ) names'
parseDataDecl _ _ =
  fail "Record declaration not in supported format."

makeConstructor :: String -> [(String, HSE.Type HSE.SrcSpanInfo)] ->
  (HSE.Exp HSE.SrcSpanInfo, HSE.Type HSE.SrcSpanInfo)
makeConstructor name fields = (appTagged recordType, taggedRecordType)
  where
    recordType = desugarRecordType fields
    taggedRecordType =
      -- Example:              Tagged  "Main.Person"  (Record ..)
      --                       vvvvvv  vvvvvvvv       vvvvvvvvvvv
      HSE.TyApp l (HSE.TyApp l (hellTaggedTyCon l) (tySym qualifiedName)) recordType
    qualifiedName = "Main." ++ name
    appTagged ty =
      HSE.App
        l
        ( HSE.App
            l
            (hellTaggedCon l)
            (HSE.TypeApp l (tySym qualifiedName))
        )
        (HSE.TypeApp l ty)
    tySym s = HSE.TyPromoted l (HSE.PromotedString l s s)
    l = HSE.noSrcSpan

makeConstructRecord :: HSE.QName HSE.SrcSpanInfo -> [HSE.FieldUpdate HSE.SrcSpanInfo] -> HSE.Exp HSE.SrcSpanInfo
makeConstructRecord qname fields =
  HSE.App l (HSE.Con l qname)
    $ foldr
      ( \(name, expr) rest ->
          let tySym s = HSE.TyPromoted l (HSE.PromotedString l s s)
           in HSE.App
                l
                ( HSE.App
                    l
                    ( HSE.App
                        l
                        (HSE.Var l (hellQName l "ConsR"))
                        (HSE.TypeApp l (tySym name))
                    )
                    expr
                )
                rest
      )
      (HSE.Var l (hellQName l "NilR"))
    $ List.sortBy (Ord.comparing fst)
    $ map
      ( \case
          HSE.FieldUpdate _ (HSE.UnQual _ (HSE.Ident _ i)) expr -> (i, expr)
          f -> error $ "Invalid field: " ++ show f
      )
      fields
  where
    l = HSE.noSrcSpan

desugarRecordType :: [(String, HSE.Type HSE.SrcSpanInfo)] -> HSE.Type HSE.SrcSpanInfo
desugarRecordType = appRecord . foldr appCons nilL
  where
    appCons (name, typ) rest =
      HSE.TyApp l (HSE.TyApp l (HSE.TyApp l consL (tySym name)) typ) rest
    appRecord x =
      HSE.TyApp l (hellRecordTyCon l) x
    tySym s = HSE.TyPromoted l (HSE.PromotedString l s s)
    nilL = hellNilTyCon l
    consL = hellConsTyCon l
    l = HSE.noSrcSpan

--------------------------------------------------------------------------------
-- Typed AST support
--
-- We define a well-typed, well-indexed GADT AST which can be evaluated directly.

data Term g t where
  Var :: Var g t -> Term g t
  Lam :: Term (g, a) b -> Term g (a -> b)
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
eval env (Lam e) = \x -> eval (env, x) e
eval env (App e1 e2) = (eval env e1) (eval env e2)
eval _env (Lit a) = a

-- Type-safe, total lookup. The final @slot@ determines which slot of
-- a given tuple to pick out.
lookp :: Var env t -> env -> t
lookp (ZVar slot) (_, x) = slot x
lookp (SVar v) (env, _) = lookp v env

--------------------------------------------------------------------------------
-- The "untyped" AST
--
-- This is the AST that is not interpreted, and is just
-- type-checked. The HSE AST is desugared into this one.

data UTerm t
  = UVar HSE.SrcSpanInfo t String
  | ULam HSE.SrcSpanInfo t Binding (Maybe SomeStarType) (UTerm t)
  | UApp HSE.SrcSpanInfo t (UTerm t) (UTerm t)
  | -- IRep below: The variables are poly types, they aren't metavars,
    -- and need to be instantiated.
    UForall Prim HSE.SrcSpanInfo t [SomeTypeRep] Forall [TH.Uniq] (IRep TH.Uniq) [t]
  deriving (Traversable, Functor, Foldable)

typeOf :: UTerm t -> t
typeOf = \case
  UVar _ t _ -> t
  ULam _ t _ _ _ -> t
  UApp _ t _ _ -> t
  UForall _ _ t _ _ _ _ _ -> t

data Binding = Singleton String | Tuple [String]

data Forall where
  NoClass :: (forall (a :: Type). TypeRep a -> Forall) -> Forall
  SymbolOf :: (forall (a :: Symbol). TypeRep a -> Forall) -> Forall
  StreamTypeOf :: (forall (a :: StreamType). TypeRep a -> Forall) -> Forall
  ListOf :: (forall (a :: List). TypeRep a -> Forall) -> Forall
  OrdEqShow :: (forall (a :: Type). (Ord a, Eq a, Show a) => TypeRep a -> Forall) -> Forall
  Monoidal :: (forall m. (Monoid m) => TypeRep m -> Forall) -> Forall
  Applicable :: (forall (m :: Type -> Type). (Applicative m) => TypeRep m -> Forall) -> Forall
  Monadic :: (forall (m :: Type -> Type). (Monad m) => TypeRep m -> Forall) -> Forall
  GetOf ::
    TypeRep (k :: Symbol) ->
    TypeRep (a :: Type) ->
    TypeRep (t :: Symbol) ->
    TypeRep (r :: List) ->
    ((Tagged t (Record r) -> a) -> Forall) ->
    Forall
  SetOf ::
    TypeRep (k :: Symbol) ->
    TypeRep (a :: Type) ->
    TypeRep (t :: Symbol) ->
    TypeRep (r :: List) ->
    ((a -> Tagged t (Record r) -> Tagged t (Record r)) -> Forall) ->
    Forall
  ModifyOf ::
    TypeRep (k :: Symbol) ->
    TypeRep (a :: Type) ->
    TypeRep (t :: Symbol) ->
    TypeRep (r :: List) ->
    (((a -> a) -> Tagged t (Record r) -> Tagged t (Record r)) -> Forall) ->
    Forall
  Final :: (forall g. Typed (Term g)) -> Forall

lit :: Type.Typeable a => Prim -> a -> UTerm ()
lit name = litWithSpan name HSE.noSrcSpan

litWithSpan :: Type.Typeable a => Prim -> HSE.SrcSpanInfo -> a -> UTerm ()
litWithSpan name srcSpanInfo l = UForall name srcSpanInfo () [] (Final (Typed (Type.typeOf l) (Lit l))) [] (fromSomeStarType (SomeStarType (Type.typeOf l))) []

data Prim = LitP (HSE.Literal HSE.SrcSpanInfo) | NameP String | UnitP

data SomeStarType = forall (a :: Type). SomeStarType (TypeRep a)

deriving instance Show SomeStarType

instance Eq SomeStarType where
  SomeStarType x == SomeStarType y = Type.SomeTypeRep x == Type.SomeTypeRep y

pattern StarTypeRep t <- (toStarType -> Just (SomeStarType t))
  where
    StarTypeRep t = SomeTypeRep t

toStarType :: SomeTypeRep -> Maybe SomeStarType
toStarType (SomeTypeRep t) = do
  Type.HRefl <- Type.eqTypeRep (typeRepKind t) (typeRep @Type)
  pure $ SomeStarType t

--------------------------------------------------------------------------------
-- The type checker

data Typed (thing :: Type -> Type) = forall ty. Typed (TypeRep (ty :: Type)) (thing ty)

data TypeCheckError
  = NotInScope String
  | TupleTypeMismatch
  | TypeCheckMismatch
  | TupleTypeTooBig
  | TypeOfApplicandIsNotFunction
  | LambdaIsNotAFunBug
  | InferredCheckedDisagreeBug
  | LambdaMustBeStarBug
  | ConstraintResolutionProblem HSE.SrcSpanInfo Forall String
  deriving (Show)

instance Show Forall where show = showR

typed :: (Type.Typeable a) => a -> Typed (Term g)
typed l = Typed (Type.typeOf l) (Lit l)

-- The type environment and lookup
data TyEnv g where
  Nil :: TyEnv g
  Cons :: Binding -> TypeRep (t :: Type) -> TyEnv h -> TyEnv (h, t)

-- The top-level checker used by the main function.
check :: (UTerm SomeTypeRep) -> TyEnv () -> Either TypeCheckError (Typed (Term ()))
check = tc

-- Type check a term given an environment of names.
tc :: (UTerm SomeTypeRep) -> TyEnv g -> Either TypeCheckError (Typed (Term g))
tc (UVar _ _ v) env = do
  Typed ty v' <- lookupVar v env
  pure $ Typed ty (Var v')
tc (ULam _ (StarTypeRep lam_ty) s _ body) env =
  case lam_ty of
    Type.Fun bndr_ty' _
      | Just Type.HRefl <- Type.eqTypeRep (typeRepKind bndr_ty') (typeRep @Type) ->
          case tc body (Cons s bndr_ty' env) of
            Left e -> Left e
            Right (Typed body_ty' body') ->
              let checked_ty = Type.Fun bndr_ty' body_ty'
               in case Type.eqTypeRep checked_ty lam_ty of
                    Just Type.HRefl -> Right $ Typed lam_ty (Lam body')
                    Nothing -> Left InferredCheckedDisagreeBug
    _ -> Left LambdaIsNotAFunBug
tc (ULam _ (SomeTypeRep {}) _ _ _) _ =
  Left LambdaMustBeStarBug
tc (UApp _ _ e1 e2) env =
  case tc e1 env of
    Left e -> Left e
    Right (Typed (Type.Fun bndr_ty body_ty) e1') ->
      case tc e2 env of
        Left e -> Left e
        Right (Typed arg_ty e2') ->
          case Type.eqTypeRep arg_ty bndr_ty of
            Nothing ->
              -- error $ "Type error: " ++ show arg_ty ++ " vs " ++ show bndr_ty
              Left TypeCheckMismatch
            Just (Type.HRefl) ->
              let kind = typeRepKind body_ty
               in case Type.eqTypeRep kind (typeRep @Type) of
                    Just Type.HRefl -> Right $ Typed body_ty (App e1' e2')
                    _ -> Left TypeCheckMismatch
    Right {} -> Left TypeOfApplicandIsNotFunction
-- Polytyped terms, must be, syntactically, fully-saturated
tc (UForall _ forallLoc _ _ fall _ _ reps0) _env = go reps0 fall
  where
    go :: [SomeTypeRep] -> Forall -> Either TypeCheckError (Typed (Term g))
    go [] (Final typed') = pure typed'
    go (StarTypeRep rep : reps) (NoClass f) = go reps (f rep)
    go (SomeTypeRep rep : reps) (ListOf f)
      | Just Type.HRefl <- Type.eqTypeRep (typeRepKind rep) (typeRep @List) = go reps (f rep)
    go (SomeTypeRep rep : reps) (SymbolOf f)
      | Just Type.HRefl <- Type.eqTypeRep (typeRepKind rep) (typeRep @Symbol) = go reps (f rep)
    go (SomeTypeRep rep : reps) (StreamTypeOf f)
      | Just Type.HRefl <- Type.eqTypeRep (typeRepKind rep) (typeRep @StreamType) = go reps (f rep)
    go (StarTypeRep rep : reps) fa@(OrdEqShow f) =
      if
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Int) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Double) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Bool) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Char) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Text) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @ByteString) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @ExitCode) -> go reps (f rep)
          | otherwise -> problem fa $ "type doesn't have enough instances " ++ show rep

    go (SomeTypeRep rep : reps) fa@(Monadic f) =
      if
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @IO) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Maybe) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @[]) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Tree) -> go reps (f rep)
          | Type.App either' _ <- rep,
            Just Type.HRefl <- Type.eqTypeRep either' (typeRep @Either) ->
              go reps (f rep)
          | otherwise -> problem fa $ "type doesn't have enough instances " ++ show rep
    go (SomeTypeRep rep : reps) fa@(Applicable f) =
      if
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @IO) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Options.Parser) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Maybe) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @[]) -> go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Tree) -> go reps (f rep)
          | Type.App either' _ <- rep,
            Just Type.HRefl <- Type.eqTypeRep either' (typeRep @Either) ->
              go reps (f rep)
          | otherwise -> problem fa $ "type doesn't have enough instances " ++ show rep
    go (SomeTypeRep rep : reps) fa@(Monoidal f) =
      if
          | Type.App either' _ <- rep,
            Just Type.HRefl <- Type.eqTypeRep either' (typeRep @Vector) ->
              go reps (f rep)
          | Type.App (Type.App either' _) _ <- rep,
            Just Type.HRefl <- Type.eqTypeRep either' (typeRep @Options.Mod) ->
              go reps (f rep)
          | Type.App either' _ <- rep,
            Just Type.HRefl <- Type.eqTypeRep either' (typeRep @[]) ->
              go reps (f rep)
          | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Text) -> go reps (f rep)
          | otherwise -> problem fa $ "type doesn't have enough instances " ++ show rep
    go reps fa@(GetOf k0 a0 t0 r0 f) =
      case makeAccessor k0 r0 a0 t0 of
        Just accessor -> go reps (f accessor)
        Nothing -> problem fa $ "missing field for field access"
    go reps fa@(SetOf k0 a0 t0 r0 f) =
      case makeSetter k0 r0 a0 t0 of
        Just accessor -> go reps (f accessor)
        Nothing -> problem fa $ "missing field for field set"
    go reps fa@(ModifyOf k0 a0 t0 r0 f) =
      case makeModify k0 r0 a0 t0 of
        Just accessor -> go reps (f accessor)
        Nothing -> problem fa $ "missing field for field modify"
    go tys r = problem r $ "forall type arguments mismatch: " ++ show tys ++ " for " ++ showR r

    problem :: Forall -> String -> Either TypeCheckError a
    problem fa = Left . ConstraintResolutionProblem forallLoc fa

showR :: Forall -> String
showR = \case
  NoClass {} -> "forall a."
  SymbolOf {} -> "forall s. s :: Symbol"
  StreamTypeOf {} -> "forall s. s :: StreamType"
  ListOf {} -> "forall l. l :: List"
  OrdEqShow {} -> "forall a. (Ord a, Eq a, Show a)"
  Monadic {} -> "forall a. Monad a"
  Applicable {} -> "forall a. Applicative a"
  Monoidal {} -> "forall a. Monoid a"
  GetOf {} -> "<record getter>"
  SetOf {} -> "<record setter>"
  ModifyOf {} -> "<record modifier>"
  Final {} -> "<final>"

-- Make a well-typed literal - e.g. @lit Text.length@ - which can be
-- embedded in the untyped AST.
lookupVar :: String -> TyEnv g -> Either TypeCheckError (Typed (Var g))
lookupVar str Nil = Left $ NotInScope str
lookupVar v (Cons (Singleton s) ty e)
  | v == s = pure $ Typed ty (ZVar id)
  | otherwise = do
      Typed ty' v' <- lookupVar v e
      pure $ Typed ty' (SVar v')
lookupVar v (Cons (Tuple ss) ty e)
  | Just i <- lookup v $ zip ss [0 :: Int ..] =
      case ty of
        Type.App (Type.App tup x) y
          | Just Type.HRefl <- Type.eqTypeRep tup (typeRep @(,)) ->
              case i of
                0 -> pure $ Typed x $ ZVar \(a, _) -> a
                1 -> pure $ Typed y $ ZVar \(_, b) -> b
                _ -> Left TupleTypeMismatch
        Type.App (Type.App (Type.App tup x) y) z
          | Just Type.HRefl <- Type.eqTypeRep tup (typeRep @(,,)) ->
              case i of
                0 -> pure $ Typed x $ ZVar \(a, _, _) -> a
                1 -> pure $ Typed y $ ZVar \(_, b, _) -> b
                2 -> pure $ Typed z $ ZVar \(_, _, c) -> c
                _ -> Left TupleTypeMismatch
        Type.App (Type.App (Type.App (Type.App tup x) y) z) z'
          | Just Type.HRefl <- Type.eqTypeRep tup (typeRep @(,,,)) ->
              case i of
                0 -> pure $ Typed x $ ZVar \(a, _, _, _) -> a
                1 -> pure $ Typed y $ ZVar \(_, b, _, _) -> b
                2 -> pure $ Typed z $ ZVar \(_, _, c, _) -> c
                3 -> pure $ Typed z' $ ZVar \(_, _, _, d) -> d
                _ -> Left TupleTypeMismatch
        _ -> Left TupleTypeTooBig
  | otherwise = do
      Typed ty' v' <- lookupVar v e
      pure $ Typed ty' (SVar v')

--------------------------------------------------------------------------------
-- Desugar expressions

data DesugarError
  = InvalidConstructor String
  | InvalidVariable String
  | UnknownType String
  | UnsupportedSyntax String
  | BadParameterSyntax String
  | KindError
  | BadDoNotation
  | TupleTooBig
  | UnsupportedLiteral
  deriving (Show, Eq)

nestedTyApps :: HSE.Exp HSE.SrcSpanInfo -> Maybe (HSE.QName HSE.SrcSpanInfo, [HSE.Type HSE.SrcSpanInfo])
nestedTyApps = go []
  where
    go acc (HSE.App _ (HSE.Var _ qname) (HSE.TypeApp _ ty)) = pure (qname, ty : acc)
    go acc (HSE.App _ (HSE.Con _ qname) (HSE.TypeApp _ ty)) = pure (qname, ty : acc)
    go acc (HSE.App _ e (HSE.TypeApp _ ty)) = go (ty : acc) e
    go _ _ = Nothing

desugarExp ::
  Map String SomeTypeRep ->
  Map String (UTerm ()) ->
  HSE.Exp HSE.SrcSpanInfo ->
  Either DesugarError (UTerm ())
desugarExp userDefinedTypeAliases globals = go mempty
  where
    go scope = \case
      HSE.Case l e alts -> do
        e' <- desugarCase l e alts
        go scope e'
      HSE.Paren _ x -> go scope x
      HSE.If l i t e ->
        (\e' t' i' -> UApp l () (UApp l () (UApp l () (bool' l) e') t') i')
          <$> go scope e
          <*> go scope t
          <*> go scope i
      HSE.Tuple l HSE.Boxed xs -> do
        xs' <- traverse (go scope) xs
        pure $ foldl (UApp l ()) (tuple' (length xs) l) xs'
      HSE.List l xs -> do
        xs' <- traverse (go scope) xs
        pure $ foldr (\x y -> UApp l () (UApp l () (cons' l) x) y) (nil' l) xs'
      HSE.Lit _ lit' -> case lit' of
        HSE.Char _ char _ -> pure $ lit (LitP lit') char
        HSE.String _ string _ -> pure $ lit (LitP lit') $ Text.pack string
        HSE.Int _ int _ -> pure $ lit (LitP lit') (fromIntegral int :: Int)
        HSE.Frac _ _ str
          | Just dub <- Read.readMaybe str ->
              pure $ lit (LitP lit') (dub :: Double)
        _ -> Left $ UnsupportedLiteral
      app@HSE.App {} | Just (qname, tys) <- nestedTyApps app -> do
        reps <- traverse (desugarSomeType userDefinedTypeAliases) tys
        desugarQName scope globals qname reps
      HSE.Var _ qname ->
        desugarQName scope globals qname []
      HSE.App l f x -> UApp l () <$> go scope f <*> go scope x
      HSE.InfixApp l x (HSE.QVarOp l'op f) y -> UApp l () <$> (UApp l'op () <$> go scope (HSE.Var l'op f) <*> go scope x) <*> go scope y
      HSE.Lambda l pats e -> do
        args <- traverse (desugarArg userDefinedTypeAliases) pats
        let stringArgs = concatMap (bindingStrings . fst) args
        e' <- go (foldr Set.insert scope stringArgs) e
        pure $ foldr (\(name, ty) inner -> ULam l () name ty inner) e' args
      HSE.Con _ qname ->
        desugarQName scope globals qname []
      HSE.Do _ stmts -> do
        let squash [HSE.Qualifier _ e] = pure e
            squash (s : ss) = do
              case s of
                HSE.Generator l pat e -> do
                  inner <- squash ss
                  let (.>>=) = HSE.Var l (HSE.Qual l (HSE.ModuleName l "Monad") (HSE.Ident l "bind"))
                  pure $
                    HSE.App
                      l
                      (HSE.App l (.>>=) e)
                      (HSE.Lambda l [pat] inner)
                HSE.Qualifier l e -> do
                  inner <- squash ss
                  let (.>>) = HSE.Var l (HSE.Qual l (HSE.ModuleName l "Monad") (HSE.Ident l "then"))
                  pure $
                    HSE.App
                      l
                      (HSE.App l (.>>) e)
                      inner
                HSE.LetStmt l (HSE.BDecls _ [HSE.PatBind _ pat (HSE.UnGuardedRhs _ e) Nothing]) -> do
                  inner <- squash ss
                  pure $ HSE.App l (HSE.Lambda l [pat] inner) e
                _ -> Left BadDoNotation
            squash _ = Left BadDoNotation
        squash stmts >>= go scope
      HSE.RecConstr _ qname fields -> go scope $ makeConstructRecord qname fields
      e -> Left $ UnsupportedSyntax $ show e

-- Generates this:
--
-- Variant.run
--           x
--           $ Variant.cons @"Main.Number" (\i -> Show.show i) $
--              Variant.cons @"Main.Text" (\t -> t) $
--                Variant.nil
desugarCase :: HSE.SrcSpanInfo -> HSE.Exp HSE.SrcSpanInfo -> [HSE.Alt HSE.SrcSpanInfo] -> Either DesugarError (HSE.Exp HSE.SrcSpanInfo)
desugarCase _ _ [] = Left $ UnsupportedSyntax "empty case"
desugarCase l scrutinee xs = do
  alts <- fmap (List.sortBy (Ord.comparing fst)) $ traverse desugarAlt xs
  pure $
    HSE.App l (HSE.App l run scrutinee) $
      foldr (HSE.App l) nil $
        map snd alts
  where
    tySym s = HSE.TyPromoted l (HSE.PromotedString l s s)
    nil =
      ( HSE.Var
          l
          ( hellQName l "NilA"
          )
      )
    run =
      ( HSE.Var
          l
          ( hellQName l "runAccessor")
      )
    desugarAlt
      ( HSE.Alt
          l'
          ( HSE.PApp
              _
              (HSE.UnQual _ (HSE.Ident _ name))
              [HSE.PVar _ (HSE.Ident _ x)]
            )
          (HSE.UnGuardedRhs _ e)
          _
        ) =
        -- Variant.cons @name (\x -> e)
        pure $
          (name,) $
            HSE.App
              l'
              ( HSE.App
                  l'
                  ( HSE.Var
                      l'
                      ( hellQName l' "ConsA")
                  )
                  (HSE.TypeApp l' (tySym name))
              )
              (HSE.Lambda l' [HSE.PVar l' (HSE.Ident l' x)] e)
    -- Nullary constructor
    desugarAlt
      ( HSE.Alt
          l'
          ( HSE.PApp
              _
              (HSE.UnQual _ (HSE.Ident _ name))
              []
            )
          (HSE.UnGuardedRhs _ e)
          _
        ) =
        -- Variant.cons @name (\_ -> e)
        pure $
          (name,) $
            HSE.App
              l'
              ( HSE.App
                  l'
                  ( HSE.Var
                      l'
                      ( hellQName l' "ConsA")
                  )
                  (HSE.TypeApp l' (tySym name))
              )
              (HSE.Lambda l' [HSE.PVar l' (HSE.Ident l' "_")] e)
    desugarAlt _ = Left $ UnsupportedSyntax "case alternative syntax"

bindingStrings :: Binding -> [String]
bindingStrings (Singleton string) = [string]
bindingStrings (Tuple tups) = tups

desugarQName :: Set String -> Map String (UTerm ()) -> HSE.QName HSE.SrcSpanInfo -> [SomeTypeRep] -> Either DesugarError (UTerm ())
desugarQName scope globals qname [] =
  case qname of
    HSE.UnQual _ (HSE.Ident l string) | Set.member string scope -> pure $ UVar l () string
    HSE.Qual _ (HSE.ModuleName _ "Main") (HSE.Ident _ string)
      | Just uterm <- Map.lookup string globals ->
          pure uterm
    HSE.Qual _ (HSE.ModuleName _ prefix) (HSE.Ident _ string)
      | Just (uterm, _) <- Map.lookup (prefix ++ "." ++ string) supportedLits ->
          pure $ uterm
    HSE.UnQual _ (HSE.Symbol _ string)
      | Just (uterm, _) <- Map.lookup string supportedLits ->
          pure $ uterm
    _ -> desugarPolyQName qname []
desugarQName _ _ qname treps = desugarPolyQName qname treps

desugarPolyQName :: HSE.QName HSE.SrcSpanInfo -> [SomeTypeRep] -> Either DesugarError (UTerm ())
desugarPolyQName qname treps =
  case qname of
    HSE.Qual l (HSE.ModuleName _ prefix) (HSE.Ident _ string)
      | let namep = (prefix ++ "." ++ string),
        Just (forall', vars, irep, _) <- Map.lookup namep polyLits -> do
          pure (UForall (NameP namep) l () treps forall' vars irep [])
    HSE.UnQual l (HSE.Symbol _ string)
      | let namep = string,
        Just (forall', vars, irep, _) <- Map.lookup string polyLits -> do
          pure (UForall (NameP namep) l () treps forall' vars irep [])
    HSE.Special l (HSE.UnitCon {}) ->
      pure $ litWithSpan UnitP l ()
    _ -> Left $ InvalidVariable $ show qname

desugarArg :: Map String SomeTypeRep -> HSE.Pat HSE.SrcSpanInfo -> Either DesugarError (Binding, Maybe SomeStarType)
desugarArg userDefinedTypeAliases (HSE.PatTypeSig _ (HSE.PVar _ (HSE.Ident _ i)) typ) =
  fmap (Singleton i,) (fmap Just (desugarStarType userDefinedTypeAliases typ))
desugarArg userDefinedTypeAliases (HSE.PatTypeSig _ (HSE.PTuple _ HSE.Boxed idents) typ)
  | Just idents' <- traverse desugarIdent idents =
      fmap (Tuple idents',) (fmap Just (desugarStarType userDefinedTypeAliases typ))
desugarArg _ (HSE.PVar _ (HSE.Ident _ i)) =
  pure (Singleton i, Nothing)
desugarArg _ (HSE.PTuple _ HSE.Boxed idents)
  | Just idents' <- traverse desugarIdent idents =
      pure (Tuple idents', Nothing)
desugarArg userDefinedTypeAliases (HSE.PParen _ p) = desugarArg userDefinedTypeAliases p
desugarArg _ p = Left $ BadParameterSyntax $ HSE.prettyPrint p

desugarIdent :: HSE.Pat HSE.SrcSpanInfo -> Maybe String
desugarIdent (HSE.PVar _ (HSE.Ident _ s)) = Just s
desugarIdent _ = Nothing

--------------------------------------------------------------------------------
-- Desugar types

desugarStarType :: Map String SomeTypeRep -> HSE.Type HSE.SrcSpanInfo -> Either DesugarError SomeStarType
desugarStarType userDefinedTypeAliases t = do
  someRep <- desugarSomeType userDefinedTypeAliases t
  case someRep of
    StarTypeRep t' -> pure (SomeStarType t')
    _ -> Left KindError

desugarSomeType ::
  Map String SomeTypeRep ->
  HSE.Type HSE.SrcSpanInfo -> Either DesugarError SomeTypeRep
desugarSomeType userDefinedTypeAliases = go
  where
    go :: HSE.Type HSE.SrcSpanInfo -> Either DesugarError SomeTypeRep
    go = \case
      HSE.TyTuple _ HSE.Boxed types -> do
        tys <- traverse go types
        case tys of
          [StarTypeRep a, StarTypeRep b] ->
            pure $ StarTypeRep (Type.App (Type.App (typeRep @(,)) a) b)
          [StarTypeRep a, StarTypeRep b, StarTypeRep c] ->
            pure $ StarTypeRep (Type.App (Type.App (Type.App (typeRep @(,,)) a) b) c)
          [StarTypeRep a, StarTypeRep b, StarTypeRep c, StarTypeRep d] ->
            pure $ StarTypeRep (Type.App (Type.App (Type.App (Type.App (typeRep @(,,,)) a) b) c) d)
          _ -> Left TupleTooBig
      HSE.TyParen _ x -> go x
      HSE.TyCon _ (HSE.UnQual _ (HSE.Ident _ name))
        | Just rep <- Map.lookup name supportedTypeConstructors -> pure rep
      HSE.TyCon _ (HSE.Qual _ (HSE.ModuleName _ m) (HSE.Ident _ name))
        | Just rep <- Map.lookup (m <> "." <> name) (supportedTypeConstructors <> userDefinedTypeAliases) ->
            pure rep
      HSE.TyCon _ (HSE.Special _ HSE.UnitCon {}) -> pure $ StarTypeRep $ typeRep @()
      HSE.TyList _ inner -> do
        rep <- go inner
        case rep of
          StarTypeRep t' -> pure $ StarTypeRep $ Type.App (typeRep @[]) t'
          _ -> Left KindError
      HSE.TyFun _ a b -> do
        a' <- go a
        b' <- go b
        case (a', b') of
          (StarTypeRep aRep, StarTypeRep bRep) ->
            pure $ StarTypeRep (Type.Fun aRep bRep)
          _ -> Left KindError
      HSE.TyApp _ f a -> do
        f' <- go f
        a' <- go a
        case applyTypes f' a' of
          Just someTypeRep -> pure someTypeRep
          _ -> Left KindError
      HSE.TyPromoted _ (HSE.PromotedString _ string _) ->
        case someSymbolVal string of
          SomeSymbol p ->
            pure $ Type.someTypeRep p
      -- TODO: Remove later.
      HSE.TyPromoted _ (HSE.PromotedCon _ _bool (HSE.UnQual _ (HSE.Ident _ name)))
        | Just rep <- Map.lookup name supportedTypeConstructors -> pure rep
      t' -> Left $ UnknownType $ show t'

-- | Apply a type `f' with an argument `x', if it is a type function,
-- and the input is the right kind.
applyTypes :: SomeTypeRep -> SomeTypeRep -> Maybe SomeTypeRep
applyTypes (SomeTypeRep f) (SomeTypeRep x) =
  case Type.typeRepKind f of
    Type.App (Type.App (-->) a) _b
      | Just Type.HRefl <- Type.eqTypeRep (-->) (TypeRep @(->)) ->
          case Type.eqTypeRep (Type.typeRepKind x) a of
            Just Type.HRefl ->
              Just $ SomeTypeRep $ Type.App f x
            _ -> Nothing
    _ -> Nothing

desugarTypeSpec :: Spec
desugarTypeSpec = do
  it "desugarType" $ do
    shouldBe (try "Bool") (Right (SomeStarType $ typeRep @Bool))
    shouldBe (try "Int") (Right (SomeStarType $ typeRep @Int))
    shouldBe (try "Bool -> Int") (Right (SomeStarType $ typeRep @(Bool -> Int)))
    shouldBe (try "()") (Right (SomeStarType $ typeRep @()))
    shouldBe (try "[Int]") (Right (SomeStarType $ typeRep @[Int]))
  where
    try e = case fmap (desugarStarType mempty) $ HSE.parseType e of
      HSE.ParseOk r -> r
      _ -> error "Parse failed."

--------------------------------------------------------------------------------
-- Desugar all bindings

desugarAll ::
  [(String, HSE.Type HSE.SrcSpanInfo)] ->
  [(String, HSE.Exp HSE.SrcSpanInfo)]
   -> Either DesugarError [(String, UTerm ())]
desugarAll types0 terms0 = do
  types <- flip execStateT Map.empty $
    traverse goType $ Graph.flattenSCCs $ stronglyConnected $ types0
  terms <- flip evalStateT Map.empty $
    traverse (goTerm types) $ Graph.flattenSCCs $ stronglyConnected $ terms0
  pure terms
  where
    goTerm ::
      Map String SomeTypeRep
      -> (String, HSE.Exp HSE.SrcSpanInfo)
      -> StateT (Map String (UTerm ())) (Either DesugarError) (String, UTerm ())
    goTerm userDefinedTypeAliases (name, expr) = do
      globals <- get
      uterm <- lift $ desugarExp userDefinedTypeAliases globals expr
      modify' $ Map.insert name uterm
      pure (name, uterm)

    goType ::
      (String, HSE.Type HSE.SrcSpanInfo)
      -> StateT (Map String SomeTypeRep) (Either DesugarError) ()
    goType (name, typ) = do
      types <- get
      SomeStarType someTypeRep <- lift $ desugarStarType types typ
      modify' $ Map.insert ("Main." ++ name) $ SomeTypeRep someTypeRep

--------------------------------------------------------------------------------
-- Infer

data InferError
  = UnifyError UnifyError
  | ZonkError ZonkError
  | ElabError ElaborateError
  deriving (Show)

-- | Note: All types in the input are free of metavars. There is an
-- intermediate phase in which there are metavars, but then they're
-- all eliminated. By the type system, the output contains only
-- determinate types.
inferExp ::
  Map String (UTerm SomeTypeRep) ->
  UTerm () ->
  Either InferError (UTerm SomeTypeRep)
inferExp _ uterm =
  case elaborate uterm of
    Left elabError -> Left $ ElabError elabError
    Right (iterm, equalities) ->
      case unify equalities of
        Left unifyError -> Left $ UnifyError unifyError
        Right subs ->
          case traverse (zonkToStarType subs) iterm of
            Left zonkError -> Left $ ZonkError $ zonkError
            Right sterm -> pure sterm

-- | Zonk a type and then convert it to a type: t :: *
zonkToStarType :: Map IMetaVar (IRep IMetaVar) -> IRep IMetaVar -> Either ZonkError SomeTypeRep
zonkToStarType subs irep = do
  zonked <- zonk (substitute subs irep)
  toSomeTypeRep zonked

--------------------------------------------------------------------------------
-- Occurs check

anyCycles :: SYB.Data a => [(String, a)] -> Bool
anyCycles =
  any isCycle
    . stronglyConnected
  where
    isCycle = \case
      Graph.CyclicSCC {} -> True
      _ -> False

stronglyConnected :: SYB.Data a => [(String, a)] -> [Graph.SCC (String, a)]
stronglyConnected =
  Graph.stronglyConnComp
    . map \thing@(name, e) -> (thing, name, freeVariables e)

anyCyclesSpec :: Spec
anyCyclesSpec = do
  it "anyCycles" do
    shouldBe (try [("foo", "\\z -> x * Z.y"), ("bar", "\\z -> Main.bar * Z.y")]) True
    shouldBe (try [("foo", "\\z -> Main.bar * Z.y"), ("bar", "\\z -> Main.foo * Z.y")]) True
    shouldBe (try [("foo", "\\z -> x * Z.y"), ("bar", "\\z -> Main.mu * Z.y")]) False
    shouldBe (try [("foo", "\\z -> x * Z.y"), ("bar", "\\z -> Main.foo * Z.y")]) False
  where
    try named =
      case traverse (\(n, e) -> (n,) <$> HSE.parseExp e) named of
        HSE.ParseOk decls -> anyCycles decls
        _ -> error "Parse failed."

--------------------------------------------------------------------------------
-- Get free variables of an HSE expression

freeVariables :: SYB.Data a => a -> [String]
freeVariables =
  Maybe.mapMaybe unpack
    . SYB.listify (const True :: HSE.QName HSE.SrcSpanInfo -> Bool)
  where
    unpack = \case
      HSE.Qual _ (HSE.ModuleName _ "Main") (HSE.Ident _ name) -> pure name
      _ -> Nothing

freeVariablesSpec :: Spec
freeVariablesSpec = do
  it "freeVariables" $ shouldBe (try "\\z -> Main.x * Z.y / Main.P") ["x", "P"]
  where
    try e = case fmap freeVariables $ HSE.parseExp e of
      HSE.ParseOk names -> names
      _ -> error "Parse failed."

--------------------------------------------------------------------------------
-- Supported type constructors

supportedTypeConstructors :: Map String SomeTypeRep
supportedTypeConstructors =
  Map.fromList
    [
      -- Standard Haskell types
      ("Bool", SomeTypeRep $ typeRep @Bool),
      ("Int", SomeTypeRep $ typeRep @Int),
      ("Double", SomeTypeRep $ typeRep @Double),
      ("Char", SomeTypeRep $ typeRep @Char),
      ("Text", SomeTypeRep $ typeRep @Text),
      ("Map", SomeTypeRep $ typeRep @Map),
      ("ByteString", SomeTypeRep $ typeRep @ByteString),
      ("ExitCode", SomeTypeRep $ typeRep @ExitCode),
      ("Maybe", SomeTypeRep $ typeRep @Maybe),
      ("Either", SomeTypeRep $ typeRep @Either),
      ("IO", SomeTypeRep $ typeRep @IO),
      ("Vector", SomeTypeRep $ typeRep @Vector),
      ("Set", SomeTypeRep $ typeRep @Set),
      ("Tree", SomeTypeRep $ typeRep @Tree),
      ("Value", SomeTypeRep $ typeRep @Value),
      ("()", SomeTypeRep $ typeRep @()),
      ("Handle", SomeTypeRep $ typeRep @IO.Handle),

      -- Internal, hidden types
      ("hell:Hell.NilL", SomeTypeRep $ typeRep @('NilL)),
      ("hell:Hell.ConsL", SomeTypeRep $ typeRep @('ConsL)),
      ("hell:Hell.Variant", SomeTypeRep $ typeRep @Variant),
      ("hell:Hell.Record", SomeTypeRep $ typeRep @Record),
      ("hell:Hell.Tagged", SomeTypeRep $ typeRep @Tagged),
      ("hell:Hell.Nullary", SomeTypeRep $ typeRep @Nullary)
    ]

-- | Used for constructors with no slot. E.g. True :: Nullary -> Bool
data Nullary = Nullary

--------------------------------------------------------------------------------
-- Support primitives

supportedLits :: Map String (UTerm (), SomeTypeRep)
supportedLits =
  Map.fromList
    [ -- Text I/O
      lit' "Text.putStrLn" t_putStrLn,
      lit' "Text.hPutStr" t_hPutStr,
      lit' "Text.putStr" t_putStr,
      lit' "Text.getLine" t_getLine,
      lit' "Text.writeFile" t_writeFile,
      lit' "Text.readFile" t_readFile,
      lit' "Text.appendFile" t_appendFile,
      lit' "Text.readProcess" t_readProcess,
      lit' "Text.readProcess_" t_readProcess_,
      lit' "Text.readProcessStdout_" t_readProcessStdout_,
      lit' "Text.getContents" (fmap Text.decodeUtf8 ByteString.getContents),
      lit' "Text.setStdin" t_setStdin,
      -- Text operations
      lit' "Text.decodeUtf8" Text.decodeUtf8,
      lit' "Text.encodeUtf8" Text.encodeUtf8,
      lit' "Text.eq" ((==) @Text),
      lit' "Text.length" Text.length,
      lit' "Text.concat" Text.concat,
      lit' "Text.breakOn" Text.breakOn,
      lit' "Text.lines" Text.lines,
      lit' "Text.words" Text.words,
      lit' "Text.unlines" Text.unlines,
      lit' "Text.unwords" Text.unwords,
      lit' "Text.intercalate" Text.intercalate,
      lit' "Text.reverse" Text.reverse,
      lit' "Text.toLower" Text.toLower,
      lit' "Text.toUpper" Text.toUpper,
      -- Needs Char operations.
      -- ("Text.any", lit' Text.any),
      -- ("Text.all", lit' Text.all),
      -- ("Text.filter", lit' Text.filter),
      lit' "Text.take" Text.take,
      lit' "Text.splitOn" Text.splitOn,
      lit' "Text.takeEnd" Text.takeEnd,
      lit' "Text.drop" Text.drop,
      lit' "Text.stripPrefix" Text.stripPrefix,
      lit' "Text.stripSuffix" Text.stripSuffix,
      lit' "Text.isSuffixOf" Text.isSuffixOf,
      lit' "Text.isPrefixOf" Text.isPrefixOf,
      lit' "Text.dropEnd" Text.dropEnd,
      lit' "Text.strip" Text.strip,
      lit' "Text.replace" Text.replace,
      lit' "Text.isPrefixOf" Text.isPrefixOf,
      lit' "Text.isSuffixOf" Text.isSuffixOf,
      lit' "Text.isInfixOf" Text.isInfixOf,
      lit' "Text.interact" (\f -> ByteString.interact (Text.encodeUtf8 . f . Text.decodeUtf8)),
      -- Int operations
      lit' "Int.show" (Text.pack . show @Int),
      lit' "Int.eq" ((==) @Int),
      lit' "Int.plus" ((+) @Int),
      lit' "Int.mult" ((*) @Int),
      lit' "Int.subtract" (subtract @Int),
      -- Double operations
      lit' "Double.fromInt" (fromIntegral :: Int -> Double),
      lit' "Double.show" (Text.pack . show @Double),
      lit' "Double.eq" ((==) @Double),
      lit' "Double.plus" ((+) @Double),
      lit' "Double.mult" ((*) @Double),
      lit' "Double.subtract" (subtract @Double),
      -- Bytes I/O
      lit' "ByteString.hGet" ByteString.hGet,
      lit' "ByteString.hPutStr" ByteString.hPutStr,
      lit' "ByteString.writeFile" bytestring_writeFile,
      lit' "ByteString.readFile" bytestring_readFile,
      lit' "ByteString.readProcess" b_readProcess,
      lit' "ByteString.readProcess_" b_readProcess_,
      lit' "ByteString.readProcessStdout_" b_readProcessStdout_,
      lit' "ByteString.interact" ByteString.interact,
      lit' "ByteString.getContents" ByteString.getContents,
      -- Handles, buffering
      lit' "IO.stdout" IO.stdout,
      lit' "IO.stderr" IO.stderr,
      lit' "IO.stdin" IO.stdin,
      lit' "IO.hSetBuffering" IO.hSetBuffering,
      lit' "IO.NoBuffering" IO.NoBuffering,
      lit' "IO.LineBuffering" IO.LineBuffering,
      lit' "IO.BlockBuffering" IO.BlockBuffering,
      lit' "IO.hClose" IO.hClose,
      lit' "IO.openFile" (\f m -> IO.openFile (Text.unpack f) m),
      lit' "IO.ReadMode" IO.ReadMode,
      lit' "IO.WriteMode" IO.WriteMode,
      lit' "IO.AppendMode" IO.AppendMode,
      lit' "IO.ReadWriteMode" IO.ReadWriteMode,
      -- Concurrent stuff
      lit' "Concurrent.threadDelay" Concurrent.threadDelay,
      -- Bool
      lit' "Bool.True" Bool.True,
      lit' "Bool.False" Bool.False,
      lit' "Bool.not" Bool.not,
      -- Get arguments
      lit' "Environment.getArgs" $ fmap (map Text.pack) getArgs,
      lit' "Environment.getEnvironment" $ fmap (map (bimap Text.pack Text.pack)) getEnvironment,
      lit' "Environment.getEnv" $ fmap Text.pack . getEnv . Text.unpack,
      -- Current directory
      lit' "Directory.createDirectoryIfMissing" (\b f -> Dir.createDirectoryIfMissing b (Text.unpack f)),
      lit' "Directory.createDirectory" (Dir.createDirectory . Text.unpack),
      lit' "Directory.getCurrentDirectory" (fmap Text.pack Dir.getCurrentDirectory),
      lit' "Directory.listDirectory" (fmap (fmap Text.pack) . Dir.listDirectory . Text.unpack),
      lit' "Directory.setCurrentDirectory" (Dir.setCurrentDirectory . Text.unpack),
      lit' "Directory.renameFile" (\x y -> Dir.renameFile (Text.unpack x) (Text.unpack y)),
      lit' "Directory.copyFile" (\x y -> Dir.copyFile (Text.unpack x) (Text.unpack y)),
      lit' "Directory.removeFile" (\x -> Dir.removeFile (Text.unpack x)),
      -- Process
      lit' "Process.proc" $ \n xs -> proc (Text.unpack n) (map Text.unpack xs),
      lit' "Process.setEnv" $ Process.setEnv @() @() @() . map (bimap Text.unpack Text.unpack),
      -- Exit
      lit' "Exit.ExitSuccess" Exit.ExitSuccess,
      lit' "Exit.ExitFailure" Exit.ExitFailure,
      -- Lists
      lit' "List.and" (List.and @[]),
      lit' "List.or" (List.or @[]),
      -- Json
      lit' "Json.decode" (Json.decode . L.fromStrict :: ByteString -> Maybe Value),
      lit' "Json.encode" (L.toStrict . Json.encode :: Value -> ByteString),
      lit' "Json.Number" (Json.toJSON :: Double -> Value),
      lit' "Json.String" (Json.toJSON :: Text -> Value),
      lit' "Json.Bool" (Json.toJSON :: Bool -> Value),
      lit' "Json.Null" Json.Null,
      lit' "Json.Array" (Json.toJSON :: Vector Value -> Value),
      lit' "Json.Object" (Json.toJSON :: Map Text Value -> Value),
      -- Records
      lit' "hell:Hell.NilR" NilR,
      -- Nullary
      lit' "hell:Hell.Nullary" Nullary,
      -- Options
      lit' "Options.switch" Options.switch,
      lit' "Options.strOption" (Options.strOption @Text),
      lit' "Options.strArgument" (Options.strArgument @Text)
    ]
  where
    lit' :: forall a. (Type.Typeable a) => String -> a -> (String, (UTerm (), SomeTypeRep))
    lit' str x = ( str, (lit (NameP str) x, SomeTypeRep $ Type.typeOf x) )

--------------------------------------------------------------------------------
-- Derive prims TH

polyLits :: Map String (Forall, [TH.Uniq], IRep TH.Uniq, TH.Type)
polyLits =
  Map.fromList
    $( let -- Derive well-typed primitive forms.
           derivePrims :: Q TH.Exp -> Q TH.Exp
           derivePrims m = do
             e <- m
             case e of
               TH.DoE Nothing binds -> do
                 TH.listE $ map makePrim binds
               _ -> error $ "Expected plain do-notation, but got: " ++ show e

           nameUnique (TH.Name _ (TH.NameU i)) = i
           nameUnique _ = error "Bad TH problem in nameUnique."

           toTy :: TH.Type -> Q TH.Exp
           toTy = \case
             TH.AppT (TH.AppT TH.ArrowT f) x -> [|IFun $(toTy f) $(toTy x)|]
             TH.AppT f x -> [|IApp $(toTy f) $(toTy x)|]
             TH.ConT name -> [|ICon (SomeTypeRep $(TH.appTypeE (TH.varE 'typeRep) (TH.conT name)))|]
             TH.VarT a -> [|IVar $(TH.litE $ TH.IntegerL $ nameUnique a)|]
             TH.ListT -> [|ICon (SomeTypeRep (typeRep @[]))|]
             TH.TupleT 2 -> [|ICon (SomeTypeRep (typeRep @(,)))|]
             TH.TupleT 3 -> [|ICon (SomeTypeRep (typeRep @(,,)))|]
             TH.TupleT 4 -> [|ICon (SomeTypeRep (typeRep @(,,,)))|]
             TH.TupleT 0 -> [|ICon (SomeTypeRep (typeRep @()))|]
             ty@TH.PromotedT {} -> [|ICon (SomeTypeRep $(TH.appTypeE (TH.varE 'typeRep) (pure ty)))|]
             t -> error $ "Unexpected type shape: " ++ show t

           -- Make a well-typed primitive form. Expects a very strict format.
           makePrim :: TH.Stmt -> Q TH.Exp
           makePrim
             ( TH.NoBindS
                 ( TH.SigE
                     (TH.AppE (TH.LitE (TH.StringL string)) expr0)
                     thtype@(TH.ForallT vars constraints typ)
                   )
               ) =
               let constrained = foldl getConstraint mempty constraints
                   vars0 =
                     map
                       ( \case
                           (TH.PlainTV v TH.SpecifiedSpec) -> TH.litE $ TH.IntegerL $ nameUnique v
                           (TH.KindedTV v TH.SpecifiedSpec _k) -> TH.litE $ TH.IntegerL $ nameUnique v
                           _ -> error "The type variable isn't what I expected."
                       )
                       vars
                   vars0T =
                     map
                       ( \case
                           (TH.PlainTV v TH.SpecifiedSpec) -> TH.varT v
                           (TH.KindedTV v TH.SpecifiedSpec _k) -> TH.varT v
                           _ -> error "The type variable isn't what I expected."
                       )
                       vars
                   ordEqShow = Set.fromList [''Ord, ''Eq, ''Show]
                   monadics = Set.fromList [''Monad]
                   -- When we add a type that is a Functor but not an
                   -- Applicative, we should add a Functor class or
                   -- this will try to raise it to an Applicative.
                   applicables = Set.fromList [''Functor, ''Applicative]
                   monoidals = Set.fromList [''Semigroup, ''Monoid]
                   finalExpr =
                     if
                         | string == "Record.get" ->
                             [|
                               GetOf
                                 (TypeRep @($(vars0T !! 0)))
                                 (TypeRep @($(vars0T !! 1)))
                                 (TypeRep @($(vars0T !! 2)))
                                 (TypeRep @($(vars0T !! 3)))
                                 \getter -> Final $ typed $(TH.sigE (TH.varE 'getter) (pure typ))
                               |]
                         | string == "Record.set" ->
                             [|
                               SetOf
                                 (TypeRep @($(vars0T !! 0)))
                                 (TypeRep @($(vars0T !! 1)))
                                 (TypeRep @($(vars0T !! 2)))
                                 (TypeRep @($(vars0T !! 3)))
                                 \setter -> Final $ typed $(TH.sigE (TH.varE 'setter) (pure typ))
                               |]
                         | string == "Record.modify" ->
                             [|
                               ModifyOf
                                 (TypeRep @($(vars0T !! 0)))
                                 (TypeRep @($(vars0T !! 1)))
                                 (TypeRep @($(vars0T !! 2)))
                                 (TypeRep @($(vars0T !! 3)))
                                 \modif -> Final $ typed $(TH.sigE (TH.varE 'modif) (pure typ))
                               |]
                         | otherwise -> [|Final $ typed $(TH.sigE (pure expr0) (pure typ))|]
                   builder =
                     foldr
                       ( \case
                           (TH.PlainTV v TH.SpecifiedSpec) -> \rest ->
                             TH.appE
                               ( TH.conE
                                   ( case Map.lookup v constrained of
                                       Nothing -> 'NoClass
                                       Just constraints'
                                         | Set.isSubsetOf constraints' ordEqShow -> 'OrdEqShow
                                         | Set.isSubsetOf constraints' monadics -> 'Monadic
                                         | Set.isSubsetOf constraints' applicables -> 'Applicable
                                         | Set.isSubsetOf constraints' monoidals -> 'Monoidal
                                       _ -> error "I'm not sure what to do with this variable."
                                   )
                               )
                               ( TH.lamE
                                   [pure $ TH.ConP 'TypeRep [TH.VarT v] []]
                                   rest
                               )
                           (TH.KindedTV v TH.SpecifiedSpec (TH.ConT v_k)) | v_k == ''Symbol -> \rest ->
                             TH.appE
                               (TH.conE 'SymbolOf)
                               ( TH.lamE
                                   [pure $ TH.ConP 'TypeRep [TH.SigT (TH.VarT v) (TH.ConT v_k)] []]
                                   rest
                               )
                           (TH.KindedTV v TH.SpecifiedSpec (TH.ConT v_k)) | v_k == ''List -> \rest ->
                             TH.appE
                               (TH.conE 'ListOf)
                               ( TH.lamE
                                   [pure $ TH.ConP 'TypeRep [TH.SigT (TH.VarT v) (TH.ConT v_k)] []]
                                   rest
                               )
                           (TH.KindedTV v TH.SpecifiedSpec (TH.ConT v_k)) | v_k == ''StreamType -> \rest ->
                             TH.appE
                               (TH.conE 'StreamTypeOf)
                               ( TH.lamE
                                   [pure $ TH.ConP 'TypeRep [TH.SigT (TH.VarT v) (TH.ConT v_k)] []]
                                   rest
                               )
                           t -> error $ "Did not expect this type of variable! " ++ show t
                       )
                       finalExpr
                       vars
                in [|(string, ($builder, $(TH.listE vars0), $(toTy typ), thtype))|]
           makePrim e = error $ "Should be of the form \"Some.name\" The.name :: T\ngot: " ++ show e

           -- Just tells us whether a given variable is constrained by a
           -- type-class or not.
           getConstraint m (TH.AppT (TH.ConT cls') (TH.VarT v)) =
             Map.insertWith Set.union v (Set.singleton cls') m
           getConstraint _ _ = error "Bad constraint!"
        in derivePrims
             [|
               do
                 -- Records
                 "hell:Hell.ConsR" ConsR :: forall (k :: Symbol) a (xs :: List). a -> Record xs -> Record (ConsL k a xs)
                 "Record.get" _ :: forall (k :: Symbol) a (t :: Symbol) (xs :: List). Tagged t (Record xs) -> a
                 "Record.set" _ :: forall (k :: Symbol) a (t :: Symbol) (xs :: List). a -> Tagged t (Record xs) -> Tagged t (Record xs)
                 "Record.modify" _ :: forall (k :: Symbol) a (t :: Symbol) (xs :: List). (a -> a) -> Tagged t (Record xs) -> Tagged t (Record xs)
                 -- Variants
                 "hell:Hell.LeftV" LeftV :: forall (k :: Symbol) a (xs :: List). a -> Variant (ConsL k a xs)
                 "hell:Hell.RightV" RightV :: forall (k :: Symbol) a (xs :: List) (k'' :: Symbol) a''. Variant (ConsL k'' a'' xs) -> Variant (ConsL k a (ConsL k'' a'' xs))
                 "hell:Hell.NilA" NilA :: forall r. Accessor 'NilL r
                 "hell:Hell.ConsA" ConsA :: forall (k :: Symbol) a r (xs :: List). (a -> r) -> Accessor xs r -> Accessor (ConsL k a xs) r
                 "hell:Hell.runAccessor" runAccessor :: forall (t :: Symbol) r (xs :: List). Tagged t (Variant xs) -> Accessor xs r -> r
                 -- Tagged
                 "hell:Hell.Tagged" Tagged :: forall (t :: Symbol) a. a -> Tagged t a
                 -- Functor
                 "Functor.fmap" fmap :: forall f a b. Functor f => (a -> b) -> f a -> f b
                 -- Operators
                 "$" (Function.$) :: forall a b. (a -> b) -> a -> b
                 "." (Function..) :: forall a b c. (b -> c) -> (a -> b) -> a -> c
                 "<>" (<>) :: forall m. Semigroup m => m -> m -> m
                 -- Monad
                 "Monad.bind" (Prelude.>>=) :: forall m a b. (Monad m) => m a -> (a -> m b) -> m b
                 "Monad.then" (Prelude.>>) :: forall m a b. (Monad m) => m a -> m b -> m b
                 "Monad.return" return :: forall a m. (Monad m) => a -> m a
                 -- Applicative operations
                 "Applicative.pure" pure :: forall f a. Applicative f => a -> f a
                 "<*>" (<*>) :: forall f a b. Applicative f => f (a -> b) -> f a -> f b
                 "<$>" (<$>) :: forall f a b. Functor f => (a -> b) -> f a -> f b
                 "<**>" (Options.<**>) :: forall f a b. Applicative f => f a -> f (a -> b) -> f b
                 -- Monadic operations
                 "Monad.mapM_" mapM_ :: forall a m. (Monad m) => (a -> m ()) -> [a] -> m ()
                 "Monad.forM_" forM_ :: forall a m. (Monad m) => [a] -> (a -> m ()) -> m ()
                 "Monad.mapM" mapM :: forall a b m. (Monad m) => (a -> m b) -> [a] -> m [b]
                 "Monad.forM" forM :: forall a b m. (Monad m) => [a] -> (a -> m b) -> m [b]
                 "Monad.when" when :: forall m. (Monad m) => Bool -> m () -> m ()
                 -- IO
                 "IO.mapM_" mapM_ :: forall a. (a -> IO ()) -> [a] -> IO ()
                 "IO.forM_" forM_ :: forall a. [a] -> (a -> IO ()) -> IO ()
                 "IO.pure" pure :: forall a. a -> IO a
                 "IO.print" (t_putStrLn . Text.pack . Show.show) :: forall a. (Show a) => a -> IO ()
                 "Timeout.timeout" Timeout.timeout :: forall a. Int -> IO a -> IO (Maybe a)
                 -- Show
                 "Show.show" (Text.pack . Show.show) :: forall a. (Show a) => a -> Text
                 -- Eq/Ord
                 "Eq.eq" (Eq.==) :: forall a. (Eq a) => a -> a -> Bool
                 "Ord.lt" (Ord.<) :: forall a. (Ord a) => a -> a -> Bool
                 "Ord.gt" (Ord.>) :: forall a. (Ord a) => a -> a -> Bool
                 -- Tuples
                 "Tuple.(,)" (,) :: forall a b. a -> b -> (a, b)
                 "Tuple.(,)" (,) :: forall a b. a -> b -> (a, b)
                 "Tuple.(,,)" (,,) :: forall a b c. a -> b -> c -> (a, b, c)
                 "Tuple.(,,,)" (,,,) :: forall a b c d. a -> b -> c -> d -> (a, b, c, d)
                 -- Exit
                 "Exit.die" (Exit.die . Text.unpack) :: forall a. Text -> IO a
                 "Exit.exitWith" Exit.exitWith :: forall a. ExitCode -> IO a
                 "Exit.exitCode" exit_exitCode :: forall a. a -> (Int -> a) -> ExitCode -> a
                 -- Exceptions
                 "Error.error" (error . Text.unpack) :: forall a. Text -> a
                 -- Bool
                 "Bool.bool" Bool.bool :: forall a. a -> a -> Bool -> a
                 -- Function
                 "Function.id" Function.id :: forall a. a -> a
                 "Function.fix" Function.fix :: forall a. (a -> a) -> a
                 -- Set
                 "Set.fromList" Set.fromList :: forall a. (Ord a) => [a] -> Set a
                 "Set.insert" Set.insert :: forall a. (Ord a) => a -> Set a -> Set a
                 "Set.member" Set.member :: forall a. (Ord a) => a -> Set a -> Bool
                 "Set.delete" Set.delete :: forall a. (Ord a) => a -> Set a -> Set a
                 "Set.union" Set.union :: forall a. (Ord a) => Set a -> Set a -> Set a
                 "Set.difference" Set.difference :: forall a. (Ord a) => Set a -> Set a -> Set a
                 "Set.intersection" Set.intersection :: forall a. (Ord a) => Set a -> Set a -> Set a
                 "Set.toList" Set.toList :: forall a. Set a -> [a]
                 "Set.size" Set.size :: forall a. Set a -> Int
                 "Set.singleton" Set.singleton :: forall a. (Ord a) => a -> Set a
                 -- Trees
                 "Tree.Node" Tree.Node :: forall a. a -> [Tree a] -> Tree a
                 "Tree.unfoldTree" Tree.unfoldTree :: forall a b. (b -> (a, [b])) -> b -> Tree a
                 "Tree.foldTree" Tree.foldTree :: forall a b. (a -> [b] -> b) -> Tree a -> b
                 "Tree.flatten" Tree.flatten :: forall a. Tree a -> [a]
                 "Tree.levels" Tree.levels :: forall a. Tree a -> [[a]]
                 "Tree.map" fmap :: forall a b. (a -> b) -> Tree a -> Tree b
                 -- Lists
                 "List.cons" (:) :: forall a. a -> [a] -> [a]
                 "List.nil" [] :: forall a. [a]
                 "List.length" List.length :: forall a. [a] -> Int
                 "List.scanl'" List.scanl' :: forall a b. (b -> a -> b) -> b -> [a] -> [b]
                 "List.scanr" List.scanr :: forall a b. (a -> b -> b) -> b -> [a] -> [b]
                 "List.concat" List.concat :: forall a. [[a]] -> [a]
                 "List.concatMap" List.concatMap :: forall a b. (a -> [b]) -> [a] -> [b]
                 "List.drop" List.drop :: forall a. Int -> [a] -> [a]
                 "List.take" List.take :: forall a. Int -> [a] -> [a]
                 "List.splitAt" List.splitAt :: forall a. Int -> [a] -> ([a], [a])
                 "List.break" List.break :: forall a. (a -> Bool) -> [a] -> ([a], [a])
                 "List.span" List.span :: forall a. (a -> Bool) -> [a] -> ([a], [a])
                 "List.partition" List.partition :: forall a. (a -> Bool) -> [a] -> ([a], [a])
                 "List.takeWhile" List.takeWhile :: forall a. (a -> Bool) -> [a] -> [a]
                 "List.dropWhile" List.dropWhile :: forall a. (a -> Bool) -> [a] -> [a]
                 "List.dropWhileEnd" List.dropWhileEnd :: forall a. (a -> Bool) -> [a] -> [a]
                 "List.map" List.map :: forall a b. (a -> b) -> [a] -> [b]
                 "List.any" List.any :: forall a. (a -> Bool) -> [a] -> Bool
                 "List.all" List.all :: forall a. (a -> Bool) -> [a] -> Bool
                 "List.iterate'" List.iterate' :: forall a. (a -> a) -> a -> [a]
                 "List.repeat" List.repeat :: forall a. a -> [a]
                 "List.cycle" List.cycle :: forall a. [a] -> [a]
                 "List.filter" List.filter :: forall a. (a -> Bool) -> [a] -> [a]
                 "List.foldl'" List.foldl' :: forall a b. (b -> a -> b) -> b -> [a] -> b
                 "List.foldr" List.foldr :: forall a b. (a -> b -> b) -> b -> [a] -> b
                 "List.unfoldr" List.unfoldr :: forall a b. (b -> Maybe (a, b)) -> b -> [a]
                 "List.zip" List.zip :: forall a b. [a] -> [b] -> [(a, b)]
                 "List.mapAccumL" List.mapAccumL :: forall s a b. (s -> a -> (s, b)) -> s -> [a] -> (s, [b])
                 "List.mapAccumR" List.mapAccumL :: forall s a b. (s -> a -> (s, b)) -> s -> [a] -> (s, [b])
                 "List.zipWith" List.zipWith :: forall a b c. (a -> b -> c) -> [a] -> [b] -> [c]
                 "List.lookup" List.lookup :: forall a b. (Eq a) => a -> [(a, b)] -> Maybe b
                 "List.find" List.find :: forall a. (a -> Bool) -> [a] -> Maybe a
                 "List.sort" List.sort :: forall a. (Ord a) => [a] -> [a]
                 "List.group" List.group :: forall a. (Eq a) => [a] -> [[a]]
                 "List.isPrefixOf" List.isPrefixOf :: forall a. (Eq a) => [a] -> [a] -> Bool
                 "List.isSuffixOf" List.isSuffixOf :: forall a. (Eq a) => [a] -> [a] -> Bool
                 "List.isInfixOf" List.isInfixOf :: forall a. (Eq a) => [a] -> [a] -> Bool
                 "List.isSubsequenceOf" List.isSubsequenceOf :: forall a. (Eq a) => [a] -> [a] -> Bool
                 "List.groupBy" List.groupBy :: forall a. (a -> a -> Bool) -> [a] -> [[a]]
                 "List.reverse" List.reverse :: forall a. [a] -> [a]
                 "List.nubOrd" nubOrd :: forall a. (Ord a) => [a] -> [a]
                 "List.inits" List.inits :: forall a. [a] -> [[a]]
                 "List.tails" List.tails :: forall a. [a] -> [[a]]
                 "List.deleteBy" List.deleteBy :: forall a. (a -> a -> Bool) -> a -> [a] -> [a]
                 "List.elem" List.elem :: forall a. (Eq a) => a -> [a] -> Bool
                 "List.notElem" List.notElem :: forall a. (Eq a) => a -> [a] -> Bool
                 "List.sortOn" List.sortOn :: forall a b. (Ord b) => (a -> b) -> [a] -> [a]
                 "List.null" List.null :: forall a. [a] -> Bool
                 "List.elemIndex" List.elemIndex :: forall a. (Eq a) => a -> [a] -> Maybe Int
                 "List.elemIndices" List.elemIndices :: forall a. (Eq a) => a -> [a] -> [Int]
                 "List.findIndex" List.findIndex :: forall a. (a -> Bool) -> [a] -> Maybe Int
                 "List.findIndices" List.findIndices :: forall a. (a -> Bool) -> [a] -> [Int]
                 "List.uncons" List.uncons :: forall a. [a] -> Maybe (a, [a])
                 "List.intersperse" List.intersperse :: forall a. a -> [a] -> [a]
                 "List.intercalate" List.intercalate :: forall a. [a] -> [[a]] -> [a]
                 "List.transpose" List.transpose :: forall a. [[a]] -> [[a]]
                 "List.subsequences" List.subsequences :: forall a. [a] -> [[a]]
                 "List.permutations" List.permutations :: forall a. [a] -> [[a]]
                 -- Vector
                 "Vector.fromList" Vector.fromList :: forall a. [a] -> Vector a
                 "Vector.toList" Vector.toList :: forall a. Vector a -> [a]
                 -- Map
                 "Map.fromList" Map.fromList :: forall k a. (Ord k) => [(k, a)] -> Map k a
                 "Map.lookup" Map.lookup :: forall k a. (Ord k) => k -> Map k a -> Maybe a
                 "Map.insert" Map.insert :: forall k a. (Ord k) => k -> a -> Map k a -> Map k a
                 "Map.delete" Map.delete :: forall k a. (Ord k) => k -> Map k a -> Map k a
                 "Map.singleton" Map.singleton :: forall k a. (Ord k) => k -> a -> Map k a
                 "Map.size" Map.size :: forall k a. Map k a -> Int
                 "Map.filter" Map.filter :: forall k a. (a -> Bool) -> Map k a -> Map k a
                 "Map.filterWithKey" Map.filterWithKey :: forall k a. (k -> a -> Bool) -> Map k a -> Map k a
                 "Map.any" any :: forall k a. (a -> Bool) -> Map k a -> Bool
                 "Map.all" all :: forall k a. (a -> Bool) -> Map k a -> Bool
                 "Map.insertWith" Map.insertWith :: forall k a. (Ord k) => (a -> a -> a) -> k -> a -> Map k a -> Map k a
                 "Map.adjust" Map.adjust :: forall k a. (Ord k) => (a -> a) -> k -> Map k a -> Map k a
                 "Map.unionWith" Map.unionWith :: forall k a. (Ord k) => (a -> a -> a) -> Map k a -> Map k a -> Map k a
                 "Map.map" Map.map :: forall a b k. (a -> b) -> Map k a -> Map k b
                 "Map.toList" Map.toList :: forall k a. Map k a -> [(k, a)]
                 "Map.keys" Map.keys :: forall k a. Map k a -> [k]
                 "Map.elems" Map.elems :: forall k a. Map k a -> [a]
                 -- Maybe
                 "Maybe.maybe" Maybe.maybe :: forall a b. b -> (a -> b) -> Maybe a -> b
                 "Maybe.Nothing" Maybe.Nothing :: forall a. Maybe a
                 "Maybe.Just" Maybe.Just :: forall a. a -> Maybe a
                 "Maybe.listToMaybe" Maybe.listToMaybe :: forall a. [a] -> Maybe a
                 "Maybe.mapMaybe" Maybe.mapMaybe :: forall a b. (a -> Maybe b) -> [a] -> [b]
                 -- Either
                 "Either.either" Either.either :: forall a b x. (a -> x) -> (b -> x) -> Either a b -> x
                 "Either.Left" Either.Left :: forall a b. a -> Either a b
                 "Either.Right" Either.Right :: forall a b. b -> Either a b
                 -- Async
                 "Async.concurrently" Async.concurrently :: forall a b. IO a -> IO b -> IO (a, b)
                 "Async.race" Async.race :: forall a b. IO a -> IO b -> IO (Either a b)
                 "Async.pooledMapConcurrently_" Async.pooledMapConcurrently_ :: forall a. (a -> IO ()) -> [a] -> IO ()
                 "Async.pooledForConcurrently_" Async.pooledForConcurrently_ :: forall a. [a] -> (a -> IO ()) -> IO ()
                 "Async.pooledMapConcurrently" Async.pooledMapConcurrently :: forall a b. (a -> IO b) -> [a] -> IO [b]
                 "Async.pooledForConcurrently" Async.pooledForConcurrently :: forall a b. [a] -> (a -> IO b) -> IO [b]
                 -- JSON
                 "Json.value" json_value :: forall a. a -> (Bool -> a) -> (Text -> a) -> (Double -> a) -> (Vector Value -> a) -> (Map Text Value -> a) -> Value -> a
                 -- Temp
                 "Temp.withSystemTempFile" temp_withSystemTempFile :: forall a. Text -> (Text -> IO.Handle -> IO a) -> IO a
                 "Temp.withSystemTempDirectory" temp_withSystemTempDirectory :: forall a. Text -> (Text -> IO a) -> IO a
                 -- Process
                 "Process.runProcess" runProcess :: forall a b c. ProcessConfig a b c -> IO ExitCode
                 "Process.runProcess_" runProcess_ :: forall a b c. ProcessConfig a b c -> IO ()
                 "Process.setStdin" setStdin :: forall stdin stdin' stdout stderr. StreamSpec 'STInput stdin' -> ProcessConfig stdin stdout stderr -> ProcessConfig stdin' stdout stderr
                 "Process.setStdout" setStdout :: forall stdin stdout stdout' stderr. StreamSpec 'STOutput stdout' -> ProcessConfig stdin stdout stderr -> ProcessConfig stdin stdout' stderr
                 "Process.setStderr" setStderr :: forall stdin stdout stderr stderr'. StreamSpec 'STOutput stderr' -> ProcessConfig stdin stdout stderr -> ProcessConfig stdin stdout stderr'
                 "Process.nullStream" Process.nullStream :: forall (a :: StreamType). StreamSpec a ()
                 "Process.useHandleClose" useHandleClose :: forall (a :: StreamType). IO.Handle -> StreamSpec a ()
                 "Process.useHandleOpen" useHandleOpen :: forall (a :: StreamType). IO.Handle -> StreamSpec a ()
                 "Process.setWorkingDir" process_setWorkingDir :: forall a b c. Text -> ProcessConfig a b c -> ProcessConfig a b c
                 -- Options
                 "Options.execParser" Options.execParser :: forall a. Options.ParserInfo a -> IO a
                 "Options.info" Options.info :: forall a. Options.Parser a -> Options.InfoMod a -> Options.ParserInfo a
                 "Options.helper" Options.helper :: forall a. Options.Parser (a -> a)
                 "Options.fullDesc" Options.fullDesc :: forall a. Options.InfoMod a
                 "Options.flag" Options.flag :: forall a. a -> a -> Options.Mod Options.FlagFields a -> Parser a
                 "Options.flag'" Options.flag' :: forall a. a -> Options.Mod Options.FlagFields a -> Parser a
                 "Option.long" option_long :: forall a. Text -> Options.Mod Options.OptionFields a
                 "Option.help" options_help :: forall a. Text -> Options.Mod Options.OptionFields a
                 "Flag.help" options_help :: forall a. Text -> Options.Mod Options.FlagFields a
                 "Flag.long" flag_long :: forall a. Text -> Options.Mod Options.FlagFields a
                 "Option.value" option_value :: forall a. a -> Options.Mod Options.OptionFields a
                 "Argument.value" argument_value :: forall a. a -> Options.Mod Options.ArgumentFields a
                 "Argument.metavar" argument_metavar :: forall a. Text -> Options.Mod Options.ArgumentFields a
                 "Argument.help" options_help :: forall a. Text -> Options.Mod Options.ArgumentFields a
               |]
     )

--------------------------------------------------------------------------------
-- Internal-use only, used by the desugarer

argument_metavar :: forall a. Text -> Options.Mod Options.ArgumentFields a
argument_metavar = Options.metavar . Text.unpack

option_value :: forall a. a -> Options.Mod Options.OptionFields a
option_value = Options.value

argument_value :: forall a. a -> Options.Mod Options.ArgumentFields a
argument_value = Options.value

options_help :: forall f a. Text -> Options.Mod f a
options_help = Options.help . Text.unpack

option_long :: forall a. Text -> Options.Mod Options.OptionFields a
option_long = Options.long . Text.unpack

flag_long :: forall a. Text -> Options.Mod Options.FlagFields a
flag_long = Options.long . Text.unpack

cons' :: HSE.SrcSpanInfo -> UTerm ()
cons' = unsafeGetForall "List.cons"

nil' :: HSE.SrcSpanInfo -> UTerm ()
nil' = unsafeGetForall "List.nil"

bool' :: HSE.SrcSpanInfo -> UTerm ()
bool' = unsafeGetForall "Bool.bool"

tuple' :: Int -> HSE.SrcSpanInfo -> UTerm ()
tuple' 0 = unsafeGetForall "Tuple.()"
tuple' 2 = unsafeGetForall "Tuple.(,)"
tuple' 3 = unsafeGetForall "Tuple.(,,)"
tuple' 4 = unsafeGetForall "Tuple.(,,,)"
tuple' _ = error "Bad compile-time lookup for tuple'."

unsafeGetForall :: String -> HSE.SrcSpanInfo -> UTerm ()
unsafeGetForall key l = Maybe.fromMaybe (error $ "Bad compile-time lookup for " ++ key) $ do
  (forall', vars, irep, _) <- Map.lookup key polyLits
  pure (UForall (NameP key) l () [] forall' vars irep [])

--------------------------------------------------------------------------------
-- Hidden terms and types, implementation-detail, used by Hell

hellModule :: l -> HSE.ModuleName l
hellModule l = HSE.ModuleName l "hell:Hell"

hellQName :: l -> String -> HSE.QName l
hellQName l string = HSE.Qual l (hellModule l) (HSE.Ident l string)

hellTyCon :: l -> String -> HSE.Type l
hellTyCon l string = HSE.TyCon l $ hellQName l string

hellCon :: l -> String -> HSE.Exp l
hellCon l string = HSE.Con l $ hellQName l string

hellTaggedTyCon :: l -> HSE.Type l
hellTaggedTyCon l = hellTyCon l "Tagged"

hellRecordTyCon :: l -> HSE.Type l
hellRecordTyCon l = hellTyCon l "Record"

hellVariantTyCon :: l -> HSE.Type l
hellVariantTyCon l = hellTyCon l "Variant"

hellNilTyCon :: l -> HSE.Type l
hellNilTyCon l = hellTyCon l "NilL"

hellConsTyCon :: l -> HSE.Type l
hellConsTyCon l = hellTyCon l "ConsL"

hellTaggedCon :: l -> HSE.Exp l
hellTaggedCon l = hellCon l "Tagged"

--------------------------------------------------------------------------------
-- Accessor for ExitCode

exit_exitCode :: a -> (Int -> a) -> ExitCode -> a
exit_exitCode ok fail' = \case
  ExitSuccess -> ok
  ExitFailure i -> fail' i

--------------------------------------------------------------------------------
-- UTF-8 specific operations without all the environment gubbins
--
-- Much better than what Data.Text.IO provides

bytestring_readFile :: Text -> IO ByteString
bytestring_readFile = ByteString.readFile . Text.unpack

bytestring_writeFile :: Text -> ByteString -> IO ()
bytestring_writeFile = ByteString.writeFile . Text.unpack

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
t_putStrLn = ByteString.hPutBuilder IO.stdout . (<> "\n") . ByteString.byteString . Text.encodeUtf8

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
-- JSON operations

-- Accessor for JSON.
json_value ::
  forall a.
  a -> -- Null
  (Bool -> a) -> -- Bool
  (Text -> a) -> -- String
  (Double -> a) -> -- Number
  (Vector Value -> a) -> -- Array
  (Map Text Value -> a) -> -- Object
  Value ->
  a
json_value null' bool string number array object =
  \case
    Json.Null -> null'
    Json.Bool s -> bool s
    Json.String s -> string s
    Json.Number s -> number (realToFrac s)
    Json.Array s -> array s
    Json.Object s -> object $ KeyMap.toMapText $ s

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

--------------------------------------------------------------------------------
-- Temp file operations

temp_withSystemTempFile :: forall a. Text -> (Text -> IO.Handle -> IO a) -> IO a
temp_withSystemTempFile template action = Temp.withSystemTempFile (Text.unpack template) $ \fp h -> action (Text.pack fp) h

temp_withSystemTempDirectory :: forall a. Text -> (Text -> IO a) -> IO a
temp_withSystemTempDirectory template action = Temp.withSystemTempDirectory (Text.unpack template) $ \fp -> action (Text.pack fp)

--------------------------------------------------------------------------------
-- Process operations

process_setWorkingDir :: forall a b c. Text -> ProcessConfig a b c -> ProcessConfig a b c
process_setWorkingDir filepath = Process.setWorkingDir (Text.unpack filepath)

--------------------------------------------------------------------------------
-- Inference type representation

data IRep v
  = IVar v
  | IApp (IRep v) (IRep v)
  | IFun (IRep v) (IRep v)
  | ICon SomeTypeRep
  deriving (Functor, Traversable, Foldable, Eq, Ord, Show)

data ZonkError
  = ZonkKindError
  | AmbiguousMetavar IMetaVar
  deriving (Show)

-- | A complete implementation of conversion from the inferer's type
-- rep to some star type, ready for the type checker.
toSomeTypeRep :: IRep Void -> Either ZonkError SomeTypeRep
toSomeTypeRep t = do
  go t
  where
    go :: IRep Void -> Either ZonkError SomeTypeRep
    go = \case
      IVar v -> pure (absurd v)
      ICon someTypeRep -> pure someTypeRep
      IFun a b -> do
        a' <- go a
        b' <- go b
        case (a', b') of
          (StarTypeRep aRep, StarTypeRep bRep) ->
            pure $ StarTypeRep (Type.Fun aRep bRep)
          _ -> Left ZonkKindError
      IApp f a -> do
        f' <- go f
        a' <- go a
        case applyTypes f' a' of
          Just someTypeRep -> pure someTypeRep
          _ -> Left ZonkKindError

-- | Convert from a type-indexed type to an untyped type.
fromSomeStarType :: forall void. SomeStarType -> IRep void
fromSomeStarType (SomeStarType r) = fromSomeType (SomeTypeRep r)

fromSomeType :: forall void. SomeTypeRep -> IRep void
fromSomeType (SomeTypeRep r) = go r
  where
    go :: forall a. TypeRep a -> IRep void
    go = \case
      Type.Fun a b -> IFun (go a) (go b)
      Type.App a b -> IApp (go a) (go b)
      rep@Type.Con {} -> ICon (SomeTypeRep rep)

--------------------------------------------------------------------------------
-- Inference elaboration phase

data IMetaVar = IMetaVar0 {index :: Int, srcSpanInfo :: HSE.SrcSpanInfo}
  deriving (Ord, Eq, Show)

data Elaborate = Elaborate
  { counter :: Int,
    equalities :: Set (Equality (IRep IMetaVar))
  }

data Equality a = Equality HSE.SrcSpanInfo a a
  deriving (Show, Functor)

-- Equality/ordering that is symmetric.
instance (Ord a) => Eq (Equality a) where
  Equality _ a b == Equality _ c d = Set.fromList [a, b] == Set.fromList [c, d]

instance (Ord a) => Ord (Equality a) where
  Equality _ a b `compare` Equality _ c d = Set.fromList [a, b] `compare` Set.fromList [c, d]

data ElaborateError = UnsupportedTupleSize | BadInstantiationBug | VariableNotInScope String
  deriving (Show)

-- | Elaboration phase.
--
-- Note: The input term contains no metavars. There are just some
-- UForalls, which have poly types, and those are instantiated into
-- metavars.
--
-- Output type /does/ contain meta vars.
elaborate :: UTerm () -> Either ElaborateError (UTerm (IRep IMetaVar), Set (Equality (IRep IMetaVar)))
elaborate = fmap getEqualities . flip runStateT empty . flip runReaderT mempty . go
  where
    empty = Elaborate {counter = 0, equalities = mempty}
    getEqualities (term, Elaborate {equalities}) = (term, equalities)
    go :: UTerm () -> ReaderT (Map String (IRep IMetaVar)) (StateT Elaborate (Either ElaborateError)) (UTerm (IRep IMetaVar))
    go = \case
      UVar l () string -> do
        env <- ask
        ty <- case Map.lookup string env of
          Just typ -> pure typ
          Nothing -> lift $ lift $ Left $ VariableNotInScope string
        pure $ UVar l ty string
      UApp l () f x -> do
        f' <- go f
        x' <- go x
        b <- fmap IVar $ freshIMetaVar l
        equal l (typeOf f') (IFun (typeOf x') b)
        pure $ UApp l b f' x'
      ULam l () binding mstarType body -> do
        a <- case mstarType of
          Just ty -> pure $ fromSomeStarType ty
          Nothing -> fmap IVar $ freshIMetaVar l
        vars <- lift $ bindingVars l a binding
        body' <- local (Map.union vars) $ go body
        let ty = IFun a (typeOf body')
        pure $ ULam l ty binding mstarType body'
      UForall prim l () types forall' uniqs polyRep _ -> do
        -- Generate variables for each unique.
        vars <- for uniqs \uniq -> do
          v <- freshIMetaVar l
          pure (uniq, v)
        -- Fill in the polyRep with the metavars.
        monoType <- for polyRep \uniq ->
          case List.lookup uniq vars of
            Nothing -> lift $ lift $ Left $ BadInstantiationBug
            Just var -> pure var
        -- Order of types is position-dependent, apply the ones we have.
        for_ (zip vars types) \((_uniq, var), someTypeRep) ->
          equal l (fromSomeType someTypeRep) (IVar var)
        -- Done!
        pure $ UForall prim l monoType types forall' uniqs polyRep (map (IVar . snd) vars)

bindingVars :: HSE.SrcSpanInfo -> IRep IMetaVar -> Binding -> StateT Elaborate (Either ElaborateError) (Map String (IRep IMetaVar))
bindingVars _ irep (Singleton name) = pure $ Map.singleton name irep
bindingVars l tupleVar (Tuple names) = do
  varsTypes <- for names \name -> fmap (name,) (fmap IVar (freshIMetaVar l))
  -- it's a left-fold:
  -- IApp (IApp (ICon (,)) x) y
  cons <- makeCons
  equal l tupleVar $ foldl IApp (ICon cons) (map snd varsTypes)
  pure $ Map.fromList varsTypes
  where
    makeCons = case length names of
      2 -> pure $ SomeTypeRep (typeRep @(,))
      3 -> pure $ SomeTypeRep (typeRep @(,,))
      4 -> pure $ SomeTypeRep (typeRep @(,,,))
      _ -> lift $ Left $ UnsupportedTupleSize

equal :: (MonadState Elaborate m) => HSE.SrcSpanInfo -> IRep IMetaVar -> IRep IMetaVar -> m ()
equal l x y = modify \elaborate' -> elaborate' {equalities = equalities elaborate' <> Set.singleton (Equality l x y)}

freshIMetaVar :: (MonadState Elaborate m) => HSE.SrcSpanInfo -> m IMetaVar
freshIMetaVar srcSpanInfo = do
  Elaborate {counter} <- get
  modify \elaborate' -> elaborate' {counter = counter + 1}
  pure $ IMetaVar0 counter srcSpanInfo

--------------------------------------------------------------------------------
-- Unification

data UnifyError
  = OccursCheck
  | TypeMismatch HSE.SrcSpanInfo (IRep IMetaVar) (IRep IMetaVar)
  deriving (Show)

-- | Unification of equality constraints, a ~ b, to substitutions.
unify :: Set (Equality (IRep IMetaVar)) -> Either UnifyError (Map IMetaVar (IRep IMetaVar))
unify = foldM update mempty
  where
    update existing equality =
      fmap
        (`extends` existing)
        (examine (fmap (substitute existing) equality))
    examine (Equality l a b)
      | a == b = pure mempty
      | IVar ivar <- a = bindMetaVar ivar b
      | IVar ivar <- b = bindMetaVar ivar a
      | IFun a1 b1 <- a,
        IFun a2 b2 <- b =
          unify (Set.fromList [Equality l a1 a2, Equality l b1 b2])
      | IApp a1 b1 <- a,
        IApp a2 b2 <- b =
          unify (Set.fromList [Equality l a1 a2, Equality l b1 b2])
      | ICon x <- a,
        ICon y <- b =
          if x == y
            then pure mempty
            else Left $ TypeMismatch l a b
      | otherwise = Left $ TypeMismatch l a b

-- | Apply new substitutions to the old ones, and expand the set to old+new.
extends :: Map IMetaVar (IRep IMetaVar) -> Map IMetaVar (IRep IMetaVar) -> Map IMetaVar (IRep IMetaVar)
extends new old = fmap (substitute new) old <> new

-- | Apply any substitutions to the type, where there are metavars.
substitute :: Map IMetaVar (IRep IMetaVar) -> IRep IMetaVar -> IRep IMetaVar
substitute subs = go
  where
    go = \case
      IVar v -> case Map.lookup v subs of
        Nothing -> IVar v
        Just ty -> ty
      ICon c -> ICon c
      IFun a b -> IFun (go a) (go b)
      IApp a b -> IApp (go a) (go b)

-- | Do an occurrs check, if all good, return a binding.
bindMetaVar ::
  IMetaVar ->
  IRep IMetaVar ->
  Either UnifyError (Map IMetaVar (IRep IMetaVar))
bindMetaVar var typ
  | occurs var typ = Left OccursCheck
  | otherwise = pure $ Map.singleton var typ

-- | Occurs check.
occurs :: IMetaVar -> IRep IMetaVar -> Bool
occurs ivar = any (== ivar)

-- | Remove any metavars from the type.
--
-- <https://stackoverflow.com/questions/31889048/what-does-the-ghc-source-mean-by-zonk>
zonk :: IRep IMetaVar -> Either ZonkError (IRep Void)
zonk = \case
  IVar var -> Left $ AmbiguousMetavar var
  ICon c -> pure $ ICon c
  IFun a b -> IFun <$> zonk a <*> zonk b
  IApp a b -> IApp <$> zonk a <*> zonk b

--------------------------------------------------------------------------------
-- Parse with #!/shebangs

data File = File {
  terms :: [(String, HSE.Exp HSE.SrcSpanInfo)],
  types :: [(String, HSE.Type HSE.SrcSpanInfo)]
  }

-- Parse a file into a list of decls, but strip shebangs.
parseFile :: String -> IO (Either String File)
parseFile filePath = do
  string <- ByteString.readFile filePath
  pure $ case HSE.parseModuleWithMode HSE.defaultParseMode {HSE.parseFilename = filePath, HSE.extensions = HSE.extensions HSE.defaultParseMode ++ [HSE.EnableExtension HSE.PatternSignatures, HSE.EnableExtension HSE.DataKinds, HSE.EnableExtension HSE.BlockArguments, HSE.EnableExtension HSE.TypeApplications]} (Text.unpack (dropShebang (Text.decodeUtf8 string))) >>= parseModule of
    HSE.ParseFailed l e -> Left $ "Parse error: " <> HSE.prettyPrint l <> ": " <> e
    HSE.ParseOk file -> Right file

-- This should be quite efficient because it's essentially a pointer
-- increase. It leaves the \n so that line numbers are intact.
dropShebang :: Text -> Text
dropShebang t = Maybe.fromMaybe t do
  rest <- Text.stripPrefix "#!" t
  pure $ Text.dropWhile (/= '\n') rest

--------------------------------------------------------------------------------
-- Spec

_spec :: Spec
_spec = do
  freeVariablesSpec
  anyCyclesSpec
  desugarTypeSpec

--------------------------------------------------------------------------------
-- Records

data Tagged (s :: Symbol) a = Tagged a

data List = NilL | ConsL Symbol Type List

data Record (xs :: List) where
  NilR :: Record 'NilL
  ConsR :: forall k a xs. a -> Record xs -> Record (ConsL k a xs)

-- | Build up a type-safe getter.
makeAccessor ::
  forall k r0 a t.
  TypeRep (k :: Symbol) ->
  TypeRep (r0 :: List) ->
  TypeRep a ->
  TypeRep t ->
  Maybe (Tagged t (Record (r0 :: List)) -> a)
makeAccessor k r0 a _ = do
  accessor <- go r0
  pure \(Tagged r) -> accessor r
  where
    go :: TypeRep (r :: List) -> Maybe (Record (r :: List) -> a)
    go r =
      case Type.eqTypeRep r (Type.TypeRep @NilL) of
        Just {} -> Nothing
        Nothing ->
          case r of
            Type.App (Type.App (Type.App _ sym) typ) r'
              | Just Type.HRefl <- Type.eqTypeRep (typeRepKind typ) (typeRep @Type),
                Just Type.HRefl <- Type.eqTypeRep (typeRepKind sym) (typeRep @Symbol),
                Just Type.HRefl <- Type.eqTypeRep (typeRepKind r') (typeRep @List) ->
                  case (Type.eqTypeRep k sym, Type.eqTypeRep a typ) of
                    (Just Type.HRefl, Just Type.HRefl) ->
                      pure \(ConsR v _xs) -> v
                    _ -> do
                      accessor <- go r'
                      pure \case
                        ConsR _a xs -> accessor xs
            _ -> Nothing

-- | Build up a type-safe setter.
makeSetter ::
  forall k r0 a t.
  TypeRep (k :: Symbol) ->
  TypeRep (r0 :: List) ->
  TypeRep a ->
  TypeRep t ->
  Maybe (a -> Tagged t (Record (r0 :: List)) -> Tagged t (Record (r0 :: List)))
makeSetter k r0 a _ = do
  setter <- go r0
  pure \a' (Tagged r) -> Tagged (setter a' r)
  where
    go :: TypeRep (r :: List) -> Maybe (a -> Record (r :: List) -> Record (r :: List))
    go r =
      case Type.eqTypeRep r (Type.TypeRep @NilL) of
        Just {} -> Nothing
        Nothing ->
          case r of
            Type.App (Type.App (Type.App _ sym) typ) r'
              | Just Type.HRefl <- Type.eqTypeRep (typeRepKind typ) (typeRep @Type),
                Just Type.HRefl <- Type.eqTypeRep (typeRepKind sym) (typeRep @Symbol),
                Just Type.HRefl <- Type.eqTypeRep (typeRepKind r') (typeRep @List) ->
                  case (Type.eqTypeRep k sym, Type.eqTypeRep a typ) of
                    (Just Type.HRefl, Just Type.HRefl) ->
                      pure \a' (ConsR _a xs) -> ConsR a' xs
                    _ -> do
                      setter <- go r'
                      pure \a' (ConsR a0 xs) -> ConsR a0 (setter a' xs)
            _ -> Nothing

-- | Simply re-uses makeAccessor and makeSetter.
makeModify ::
  forall k r0 a t.
  TypeRep (k :: Symbol) ->
  TypeRep (r0 :: List) ->
  TypeRep a ->
  TypeRep t ->
  Maybe ((a -> a) -> Tagged t (Record (r0 :: List)) -> Tagged t (Record (r0 :: List)))
makeModify k0 r0 a0 t0 = do
  getter <- makeAccessor k0 r0 a0 t0
  setter <- makeSetter k0 r0 a0 t0
  pure \f record -> setter (f (getter record)) record

--------------------------------------------------------------------------------
-- Variants

-- | A variant; one of the given choices.
data Variant (xs :: List) where
  LeftV :: forall k a xs. a -> Variant (ConsL k a xs)
  RightV :: forall k a xs k'' a''. Variant (ConsL k'' a'' xs) -> Variant (ConsL k a (ConsL k'' a'' xs))

-- | Accessor of a given variant. A record whose fields all correspond
-- to the constructors of a sum type, and whose types are all `a ->
-- r` instead of `a`.
data Accessor (xs :: List) r where
  NilA :: Accessor 'NilL r
  ConsA :: forall k a r xs. (a -> r) -> Accessor xs r -> Accessor (ConsL k a xs) r

-- | Run a total case-analysis against a variant, given an accessor
-- record.
runAccessor :: Tagged s (Variant xs) -> Accessor xs r -> r
runAccessor (Tagged (LeftV a)) (ConsA f _) = f a
runAccessor (Tagged (RightV xs)) (ConsA _ ys) = runAccessor (Tagged xs) ys

--------------------------------------------------------------------------------
-- Pretty printing

-- | Convenience.
prettyString :: (Pretty a) => a -> String
prettyString =
  Text.unpack . Text.decodeUtf8 . L.toStrict . ByteString.toLazyByteString . pretty

class Pretty a where
  pretty :: a -> ByteString.Builder

instance Pretty String where
  pretty r =
    ByteString.byteString (Text.encodeUtf8 $ Text.pack r)

instance Pretty SomeTypeRep where
  pretty r =
    ByteString.byteString (Text.encodeUtf8 $ Text.pack $ show r)

instance Pretty (TypeRep t) where
  pretty r =
    ByteString.byteString (Text.encodeUtf8 $ Text.pack $ show r)

instance Pretty IMetaVar where
  pretty (IMetaVar0 i _) =
    "t"
      <> ByteString.byteString (Text.encodeUtf8 $ Text.pack $ show i)

instance Pretty (UTerm t) where
  pretty = \case
    UVar _ _ v -> pretty v
    UApp _ _ f x -> "(" <> pretty f <> " " <> pretty x <> ")"
    UForall prim _ _ _ _ _ _ _ -> pretty prim
    ULam _ _ binding _ t ->
      "(\\" <> pretty binding <> " -> " <> pretty t <> ")"

instance Pretty Prim where
  pretty = \case
    LitP p -> pretty $ HSE.prettyPrint p
    NameP s -> pretty s
    UnitP -> "()"

instance Pretty Binding where
  pretty = \case
    Singleton v -> pretty v
    Tuple xs -> "(" <> mconcat (List.intersperse ", " (map pretty xs)) <> ")"

instance (Pretty a) => Pretty (IRep a) where
  pretty = \case
    IVar a -> pretty a
    ICon a -> pretty a
    IApp f x -> "(" <> pretty f <> " " <> pretty x <> ")"
    IFun a b -> "(" <> pretty a <> " -> " <> pretty b <> ")"

instance Pretty ZonkError where
  pretty = \case
    ZonkKindError -> "Kind error."
    AmbiguousMetavar imetavar ->
      "Ambiguous meta variable: "
        <> pretty imetavar
        <> "\n"
        <> "arising from "
        <> pretty imetavar.srcSpanInfo

instance Pretty ElaborateError where
  pretty = \case
    UnsupportedTupleSize -> "That tuple size is not supported."
    BadInstantiationBug -> "BUG: BadInstantiationBug. Please report."
    VariableNotInScope s -> "Variable not in scope: " <> pretty s

instance Pretty UnifyError where
  pretty = \case
    OccursCheck -> "Occurs check failed: Infinite type."
    TypeMismatch l a b ->
      mconcat $
        List.intersperse
          "\n\n"
          [ "Couldn't match type",
            "  " <> pretty a,
            "against type",
            "  " <> pretty b,
            "arising from " <> pretty l
          ]

instance Pretty HSE.SrcSpanInfo where
  pretty l =
    mconcat
      [ pretty (HSE.fileName l),
        ":",
        pretty $ show $ HSE.startLine l,
        ":",
        pretty $ show $ HSE.startColumn l
      ]

instance Pretty TypeCheckError where
  pretty = \case
    NotInScope s -> "Not in scope: " <> pretty s
    TupleTypeMismatch -> "Tuple type mismatch!"
    TypeCheckMismatch -> "Type check mismatch."
    TupleTypeTooBig -> "Tuple type is too big."
    TypeOfApplicandIsNotFunction -> "Type of application is not a function."
    LambdaIsNotAFunBug -> "BUG: LambdaIsNotAFunBug. Please report."
    InferredCheckedDisagreeBug -> "BUG: Inferred type disagrees with checked type. Please report."
    LambdaMustBeStarBug -> "BUG: Lambda should be of kind *, but isn't. Please report."
    ConstraintResolutionProblem loc forall' msg ->
      mconcat $
        List.intersperse
          "\n\n"
          [ "Couldn't resolve constraint",
            "  " <> pretty (showR forall'),
            "due to problem",
            "  " <> pretty msg,
            "arising from " <> pretty loc
          ]

instance Pretty DesugarError where
  pretty = \case
    InvalidConstructor c -> "Invalid constructor: " <> pretty c
    InvalidVariable c -> "Invalid variable: " <> pretty c
    UnknownType t -> "Unknown type: " <> pretty t
    UnsupportedSyntax s -> "Unsupported syntax: " <> pretty s
    BadParameterSyntax s -> "Bad parameter syntax: " <> pretty s
    KindError -> "Kind error."
    BadDoNotation -> "Bad do notation."
    TupleTooBig -> "That tuple size is not supported."
    UnsupportedLiteral -> "That literal type is not supported."

instance Pretty InferError where
  pretty = \case
    UnifyError e -> "Unification error: " <> pretty e
    ZonkError e -> "Zonk error: " <> pretty e
    ElabError e -> "Elaboration error: " <> pretty e

--------------------------------------------------------------------------------
-- Generate docs

_generateApiDocs :: IO ()
_generateApiDocs = do
  css <- Text.readFile "docs/style.css"
  js <- Text.readFile "docs/index.js"
  Lucid.renderToFile "docs/api/index.html" do
    doctypehtml_ do
      style_ css
      head_ do
        title_ "Hell's API"
      body_ do
        h1_ "Hell's API"
        h2_ $ do "Version: "; toHtml hellVersion
        p_ $ a_ [href_ "../"] $ "Back to homepage"
        input_ [type_ "text", id_ "search", placeholder_ "Filter..."]
        h2_ "Types"
        let excludeHidden = filter (not . List.isPrefixOf "hell:Hell." . fst)
        ul_ do
          for_ (excludeHidden $ Map.toList supportedTypeConstructors) typeConsToHtml
        h2_ "Terms"
        let groups =
              excludeHidden $
                Map.toList $
                  fmap (Left . snd) $
                    supportedLits
        let groups' =
              excludeHidden $
                Map.toList $
                  fmap (\(_, _, _, ty) -> Right ty) polyLits
        for_ (List.groupBy (Function.on (==) (takeWhile (/= '.') . fst)) $ List.sortOn fst $ groups <> groups') \group -> do
          h3_ [class_ "searchableHeading"] $ for_ (take 1 group) \(x, _) -> toHtml $ takeWhile (/= '.') x
          ul_ do
            for_ group \(x, a) -> case a of
              Left e -> litToHtml (x, e)
              Right e -> polyToHtml (x, e)
      script_ [id_ "searchIndex"] $ Json.encode makeSearchIndex
      script_ [type_ "text/javascript"] js

makeSearchIndex :: Json.Value
makeSearchIndex = Json.Array $ typeConstructorsIndex <> litsIndex <> polysIndex
  where
    typeConstructorsIndex =
      Vector.fromList $
        map
          ( \(name, _) ->
              Json.object
                [ ("elementId", Json.String $ nameToElementId name),
                  ("text", Json.String $ Text.pack name)
                ]
          )
          (Map.toList supportedTypeConstructors)
    litsIndex =
      Vector.fromList $
        map
          ( \(name, _) ->
              Json.object
                [ ("elementId", Json.String $ nameToElementId name),
                  ("text", Json.String $ Text.pack name)
                ]
          )
          (Map.toList supportedLits)
    polysIndex =
      Vector.fromList $
        map
          ( \(name, _) ->
              Json.object
                [ ("elementId", Json.String $ nameToElementId name),
                  ("text", Json.String $ Text.pack name)
                ]
          )
          (Map.toList polyLits)

nameToElementId :: String -> Text
nameToElementId = Text.pack

typeConsToHtml :: (String, SomeTypeRep) -> Html ()
typeConsToHtml (name, SomeTypeRep rep) =
  li_ [id_ (nameToElementId name), class_ "searchable"] $ do
    code_ do
      em_ "data "
      strong_ $ toHtml name
      em_ " :: "
      toHtml $ prettyString $ typeRepKind rep

litToHtml :: (String, SomeTypeRep) -> Html ()
litToHtml (name, SomeTypeRep rep) =
  li_ [id_ (nameToElementId name), class_ "searchable"] $ do
    code_ do
      strong_ $ toHtml name
      em_ " :: "
      toHtml $ prettyString $ rep

polyToHtml :: (String, TH.Type) -> Html ()
polyToHtml (name, ty) =
  li_ [id_ (nameToElementId name), class_ "searchable"] $ do
    code_ do
      strong_ $ toHtml name
      em_ " :: "
      toHtml $ TH.pprint $ cleanUpTHType ty

cleanUpTHType :: TH.Type -> TH.Type
cleanUpTHType = SYB.everywhere unqualify
  where
    unqualify :: forall a. (Type.Typeable a) => a -> a
    unqualify a =
      case Type.eqTypeRep (Type.typeRep @a) (Type.typeRep @TH.Name) of
        Nothing -> a
        Just Type.HRefl ->
          TH.mkName $ TH.nameBase a
