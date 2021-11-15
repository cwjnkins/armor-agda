{-# OPTIONS --guardedness #-}
open import Data.List
open import Data.String
open import Data.Unit
import      System.Exit

module Aeres.IO where

{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.IO #-}
{-# FOREIGN GHC import qualified Data.Text          #-}

module Primitive where
  open import IO.Primitive
  postulate
    getArgs : IO (List String)
    Handle  : Set
    stderr  : Handle
    hPutStrLn : Handle → String → IO ⊤

{-# COMPILE GHC Primitive.getArgs = fmap Data.Text.pack <$> System.Environment.getArgs #-}
{-# COMPILE GHC Primitive.Handle = System.IO.Handle #-}
{-# COMPILE GHC Primitive.stderr = System.IO.stderr #-}
{-# COMPILE GHC Primitive.hPutStrLn = System.IO.hPutStrLn #-}

open import IO
open System.Exit public using (exitFailure ; exitSuccess)

getArgs : IO (List String)
getArgs = lift Primitive.getArgs

putStrLnErr : String → IO ⊤
putStrLnErr str = lift (Primitive.hPutStrLn Primitive.stderr str)
