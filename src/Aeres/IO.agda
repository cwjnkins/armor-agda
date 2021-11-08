{-# OPTIONS --guardedness #-}
open import Data.List
open import Data.String

module Aeres.IO where

{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified Data.Text          #-}

module Primitive where
  open import IO.Primitive
  postulate
    getArgs : IO (List String)

{-# COMPILE GHC Primitive.getArgs = fmap Data.Text.pack <$> System.Environment.getArgs #-}

open import IO

getArgs : IO (List String)
getArgs = lift Primitive.getArgs
