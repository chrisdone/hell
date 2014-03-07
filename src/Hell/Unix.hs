{-# LANGUAGE FlexibleInstances #-}
-- | A set of utilities that are named similarly and behave similarly
-- to the UNIX way of doing shells.

module Hell.Unix
  (R(..)
  ,A(..)
  ,Ls(..)
  ,Cd(..)
  ,Rm(..)
  ,pwd
  ,rmdir
  ,disown
  ,exec)
  where

import Codec.Binary.UTF8.String
import Control.Exception
import Control.Monad
import Data.List
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import System.Posix.IO
import System.Posix.Process (executeFile, forkProcess)
import System.Process

-- | R parameter (e.g. recursive).
data R = R

-- | A parameter (e.g. all).
data A = A

-- | List directory contents.
class Ls a where
  ls :: a

-- | Print recursive directory contents.
instance Ls (R -> IO String) where
  ls R = getCurrentDirectory >>= ls R

-- | Print everything in the directory.
instance Ls (A -> IO String) where
  ls A = getCurrentDirectory >>= ls A

-- | Print the given directory recursively.
instance Ls (R -> FilePath -> IO String) where
  ls R x = recursiveList False x

-- | Print the given directory recursively.
instance Ls (A -> R -> IO String) where
  ls _ _ = getCurrentDirectory >>= ls A R

-- | Print the given directory recursively.
instance Ls (A -> R -> FilePath -> IO String) where
  ls _ _ x = recursiveList True x

-- | Print the given directory recursively.
instance Ls (R -> A -> FilePath -> IO String) where
  ls _ _ x = recursiveList True x

-- | Get directory contents.
instance Ls (A -> FilePath -> IO [FilePath]) where
  ls _ x = getEntries True x

-- | Get directory contents.
instance Ls (FilePath -> IO [FilePath]) where
  ls x = getEntries False x

-- | Get current directory contents.
instance Ls (IO [FilePath]) where
  ls = getCurrentDirectory >>= ls

-- | List the given directory.
instance Ls (FilePath -> IO String) where
  ls x = ls x >>= mapM_ putStrLn >> return ""

-- | List the given directory.
instance Ls (A -> FilePath -> IO String) where
  ls a x = ls a x >>= mapM_ putStrLn >> return ""

-- | List the current directory.
instance Ls (IO String) where
  ls =
    do pwd <- getCurrentDirectory
       ls pwd

-- | Set current directory.
class Cd a where
  cd :: a

-- | Switch to given directory.
instance Cd (FilePath -> IO String) where
  cd x = setCurrentDirectory x >> return ""

-- | Switch to home directory.
instance Cd (IO String) where
  cd =
    getHomeDirectory >>= setCurrentDirectory >> return ""

-- | Remove given file.
class Rm a where
  rm :: a

instance Rm (FilePath -> IO String) where
  rm x = removeFile x >> return ""

instance Rm (R -> FilePath -> IO String) where
  rm R x = removeDirectoryRecursive x >> return ""

-- | Print the present working directory.
pwd :: IO ()
pwd = getCurrentDirectory >>= putStrLn

-- | Remove given file.
rmdir :: FilePath -> IO ()
rmdir = removeDirectory

-- | Get directory listing.
getEntries :: Bool -> FilePath -> IO [String]
getEntries everything x =
  fmap (sort .
        filter (if everything
                   then \x -> not (all (=='.') x)
                   else \x -> not (isPrefixOf "." x)))
       (getDirectoryContents x)

-- | Recursive list.
recursiveList :: Bool -> FilePath -> IO String
recursiveList everything x =
  do xs <- ls x
     forM_ (map (x </>)
                (filter (not . isPrefixOf ".") xs))
           (\x ->
              do putStrLn x
                 isDir <- doesDirectoryExist x
                 when isDir
                      (do "" <- ls R x
                          return ()))
     return ""

-- | Launch an external application through the system shell and
-- return a @Handle@ to its standard input.
disown :: String -> IO Handle
disown x =
  do (rd, wr) <- createPipe
     setFdOption wr CloseOnExec True
     h <- fdToHandle wr
     hSetBuffering h LineBuffering
     _ <- forkProcess
            (do _ <- dupTo rd stdInput
                executeFile "/bin/sh"
                            False
                            ["-c",encodeString x]
                            Nothing)
     closeFd rd
     return h

-- | Execute the shell command.
exec :: String -> IO ()
exec x =
  do code <- system x
     case code of
       ExitSuccess -> return ()
       ExitFailure e -> throw code
