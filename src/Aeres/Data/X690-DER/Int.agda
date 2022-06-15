{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Int.TCB
import Aeres.Data.X690-DER.Int.Parser

module Aeres.Data.X690-DER.Int where

module Int where
  open Aeres.Data.X690-DER.Int.TCB public
open Int public
  hiding (getVal)

open Aeres.Data.X690-DER.Int.Parser public
