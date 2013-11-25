{-# LANGUAGE ForeignFunctionInterface #-}

-- Provdes Win32-compatible version of some system-level functions
module Hell.Win32(getEffectiveUserName) where
import Foreign
import Foreign.C
import System.Win32.Types
import Control.Monad

foreign import stdcall unsafe "windows.h GetUserNameW" getUserNameWin32 :: LPTSTR -> LPDWORD -> IO Bool

getEffectiveUserName :: IO String
getEffectiveUserName = do
  allocaArray 512 $ \ buf -> do
    with 512 $ \ len -> do
      failIfFalse_ "GetUserName" $ getUserNameWin32 buf len
      peekTString buf
