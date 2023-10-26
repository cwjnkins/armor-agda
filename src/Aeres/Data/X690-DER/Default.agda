{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Default.Parser
import Aeres.Data.X690-DER.Default.Properties
import Aeres.Data.X690-DER.Default.TCB

module Aeres.Data.X690-DER.Default where

open Aeres.Data.X690-DER.Default.TCB public
  using (Default ; RawDefault ; mkDefault)
  hiding (module Default)

module Default where
  open Aeres.Data.X690-DER.Default.Parser     public
  open Aeres.Data.X690-DER.Default.Properties public
  open Aeres.Data.X690-DER.Default.TCB        public
    hiding (Default ; RawDefault)
  open Aeres.Data.X690-DER.Default.TCB.Default public
