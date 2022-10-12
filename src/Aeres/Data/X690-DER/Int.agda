{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Int.Parser
import Aeres.Data.X690-DER.Int.Properties
import Aeres.Data.X690-DER.Int.Serializer
import Aeres.Data.X690-DER.Int.TCB

module Aeres.Data.X690-DER.Int where

module Int where
  open Aeres.Data.X690-DER.Int.Properties public
  open Aeres.Data.X690-DER.Int.Serializer public
  open Aeres.Data.X690-DER.Int.TCB        public

open Int public
  hiding (getVal ; serialize ; serializeVal; unambiguous)

open Aeres.Data.X690-DER.Int.Parser public
