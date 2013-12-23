{-# OPTIONS -fno-warn-orphans #-}
{-# OPTIONS -fno-warn-orphans #-}
{-# OPTIONS -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

-- | A base set of functions for the shell. Once the dust settles on
-- this it can be separated into logical components.

module Hell.Prelude
  (cd
  ,rm
  ,rmdir
  ,pwd
  ,home
  ,tmp
  ,perms
  ,modified
  ,write
  ,append
  ,size
  ,echo
  ,ls
  ,man
  ,run
  ,pdfinfo
  ,PDFInfo(..)
  ,killall
  ,top
  ,cabal
  ,make
  ,ghci
  ,ssh
  ,chrome
  ,firefox
  ,gimp
  ,git
  ,emacs
  ,xmodmap
  ,xset
  ,mplayer
  ,ghc
  ,which
  ,psgrep
  ,aptget
  ,aptcache
  ,xmonad
  ,notify
  ,notifying
  ,sh
  )
  where

import           Control.Exception
import           Data.Monoid
import           Data.String
import           Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import           Data.Typeable
import           System.Directory
import           System.Exit
import           System.IO
import           System.Process
import           Text.PDF.Info

#ifdef USE_OLD_TIME
import           System.Time
#else
import           Data.Time.Clock
#endif

instance IsString [Text] where
  fromString = return . T.pack

instance Exception PDFInfoError
deriving instance Typeable PDFInfoError

-- | setCurrentDirectory
cd :: FilePath -> IO ()
cd = setCurrentDirectory

-- | setCurrentDirectory
rm :: FilePath -> IO ()
rm = removeFile

-- | setCurrentDirectory
rmdir :: FilePath -> IO ()
rmdir = removeDirectory

-- | getCurrentDirectory
pwd :: IO FilePath
pwd = getCurrentDirectory

-- | getHomeDirectory
home :: IO FilePath
home = getHomeDirectory

-- | getTemporaryDirectory
tmp :: IO FilePath
tmp = getTemporaryDirectory

-- | getPermissions
perms :: FilePath -> IO Permissions
perms = getPermissions

-- | getModificationTime
#ifdef USE_OLD_TIME
modified :: FilePath -> IO ClockTime
#else
modified :: FilePath -> IO UTCTime
#endif
modified = getModificationTime

-- | writeFile
write :: FilePath -> String -> IO ()
write = writeFile

-- | appendFile
append :: FilePath -> String -> IO ()
append = appendFile

-- | hFileSize
size :: FilePath -> IO Integer
size fp = do
  h <- openFile fp ReadMode
  s <- hFileSize h
  hClose h
  return s

-- | putStrLn
echo :: String -> IO ()
echo = putStrLn

-- | pdfinfo <file>
pdfinfo :: FilePath -> IO PDFInfo
pdfinfo fp = do
  result <- pdfInfo fp
  case result of
    Left err -> throw err
    Right info -> return info

-- | ls <path>
ls :: IO ()
ls = run "ls" ""

-- | killall <name>
killall :: Text -> IO ()
killall x = sh ("killall " <> x)

-- | top
top :: IO ()
top = run "top" ""

-- | make
make :: IO ()
make = run "make" ""

-- | ghci
ghci :: IO ()
ghci = run "ghci" ""

-- | ssh <path>
ssh :: Text -> IO ()
ssh = run "ssh"

-- | chrome <path>
chrome :: IO ()
chrome = sh "chromium-browser & disown"

-- | firefox <path>
firefox :: IO ()
firefox = sh "firefox & disown"

-- | gimp <path>
gimp :: IO ()
gimp = sh "gimp & disown"

-- | xmonad <path>
xmonad :: IO ()
xmonad = sh "xmonad & disown"

-- | emacs <path>
emacs :: IO ()
emacs = sh "emacs & disown"

-- | xmodmap
xmodmap :: IO ()
xmodmap = sh "xmodmap .xmodmap"

-- | xset
xset :: IO ()
xset = run "xset r rate 150 50" ""

-- | mplayer <path>
mplayer :: Text -> IO ()
mplayer = run "mplayer"

-- | ghc <path>
ghc :: Text -> IO ()
ghc = run "ghc"

-- | git <path>
git :: Text -> IO ()
git = run "git"

-- | which <path>
which :: Text -> IO ()
which = run "which"

-- | psgrep <path>
psgrep :: Text -> IO ()
psgrep = run "ps aux | grep"

-- | man <path>
man :: Text -> IO ()
man = run "man"

-- | cabal <path>
cabal :: Text -> IO ()
cabal = run "cabal"

-- | apt-get <path>
aptget :: Text -> IO ()
aptget = run "apt-get"

-- | apt-cache <path>
aptcache :: Text -> IO ()
aptcache = run "apt-cache"

-- | Call notify-send.
notify :: Text -> IO ()
notify = run "notify-send"

-- | Run the given command, notifying with 'notify' of the complete/error status.
notifying :: IO a -> IO a
notifying m = do
  v <- onException m (notify "Hell: Command failed before completing.")
  notify "Hell: Command completed."
  return v

sh :: Text -> IO ()
sh x = do
  exitcode <- system (T.unpack x)
  case exitcode of
    ExitSuccess -> return ()
    _           -> throw exitcode

-- | Run this stuff.
run :: Text -> Text -> IO ()
run name arg = do
  exitcode <- system (T.unpack name ++ (if T.null arg then "" else " " ++ show (T.unpack arg)))
  case exitcode of
    ExitSuccess -> return ()
    _           -> throw exitcode
