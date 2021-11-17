{-# OPTIONS --guardedness #-}

open import Aeres.Prelude
import      System.Exit

module Aeres.IO where

{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.IO #-}
{-# FOREIGN GHC import qualified Data.Text          #-}
{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}

module Primitive where
  open import IO.Primitive
  postulate
    getArgs : IO (List String)
    Handle  : Set
    stderr  : Handle
    hPutStrLn : Handle → String → IO ⊤

{-# COMPILE GHC Primitive.getArgs = fmap Data.Text.pack <$> System.Environment.getArgs #-}
{-# COMPILE GHC Primitive.Handle = type System.IO.Handle #-}
{-# COMPILE GHC Primitive.stderr = System.IO.stderr #-}
{-# COMPILE GHC Primitive.hPutStrLn = TIO.hPutStrLn #-}

open import IO
open System.Exit public using (exitFailure ; exitSuccess)

getArgs : IO (List String)
getArgs = lift Primitive.getArgs

putStrLnErr : String → IO (Level.Lift Level.zero ⊤)
putStrLnErr str = Level.lift IO.<$> (lift (Primitive.hPutStrLn Primitive.stderr str))
