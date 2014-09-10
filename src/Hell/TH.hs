{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

-- | Macros.

module Hell.TH where

import Control.Monad
import Data.Char
import Data.Conduit.ProcessOld
import Data.List
import Data.List.Split
import Language.Haskell.TH
import System.Directory
import System.Environment
import System.FilePath

generateBinaries :: Q [Dec]
generateBinaries =
  do bins <- runIO getAllBinaries
     return
       (map (\bin ->
               let args = mkName "args"
               in FunD (mkName bin)
                       [Clause [VarP args]
                               (NormalB
                                  (AppE (VarE 'conduitProcess)
                                         (AppE (AppE (VarE 'proc)
                                                     (LitE (StringL bin)))
                                               (VarE args))))
                               []] )
            (nub (filter (not . null) (map normalize bins))))
  where normalize = remap . uncapitalize . go
          where go (c:cs)
                  | c == '-' || c  == '_' =
                    case go cs of
                      (c:cs) -> toUpper c : cs
                      [] -> []
                  | not (elem (toLower c) allowed) = go cs
                  | otherwise = c : go cs
                go [] = []
        uncapitalize (c:cs) | isDigit c = '_' : c : cs
                            | otherwise = toLower c : cs
        uncapitalize [] = []
        allowed = ['a'..'z'] ++ ['0'..'9']

remap name =
  case name of
   "head" -> "_head"
   "seq" -> "_seq"
   "zip" -> "_zip"
   "print" -> "_print"
   "id" -> "_id"
   "unzip" -> "_unzip"
   "join" -> "_join"
   "init" -> "_init"
   "last" -> "_last"
   "tail" -> "_tail"
   "find" -> "_find"
   "sort" -> "_sort"
   "sum" -> "_sum"
   "compare" -> "_compare"
   "truncate" -> "_truncate"
   "lex" -> "_lex"
   "env" -> "_env"
   e -> e

printQ :: (Ppr a) => Q a -> IO ()
printQ f = do
  s <- runQ f
  putStrLn $ pprint s

getAllBinaries :: IO [FilePath]
getAllBinaries =
  do path <- getEnv "PATH"
     fmap concat
          (forM (splitOn ":" path)
                (\dir ->
                   do exists <- doesDirectoryExist dir
                      if exists
                         then do contents <- getDirectoryContents dir
                                 filterM (\file ->
                                            do exists <- doesFileExist (dir </> file)
                                               if exists
                                                  then do perms <- getPermissions (dir </> file)
                                                          return (executable perms)
                                                  else return False)
                                         contents
                         else return []))
