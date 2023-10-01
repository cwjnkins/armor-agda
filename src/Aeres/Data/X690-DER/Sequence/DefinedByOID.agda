{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Sequence.DefinedByOID.Parser
import Aeres.Data.X690-DER.Sequence.DefinedByOID.Properties
import Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB

module Aeres.Data.X690-DER.Sequence.DefinedByOID where

open Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB    public
  hiding (equivalent)

module DefinedByOID where
  open Aeres.Data.X690-DER.Sequence.DefinedByOID.Parser     public
  open Aeres.Data.X690-DER.Sequence.DefinedByOID.Properties public
  open Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB    public
    using (equivalent)
