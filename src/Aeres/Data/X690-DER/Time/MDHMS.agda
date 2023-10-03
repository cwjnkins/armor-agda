{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Time.MDHMS.Parser
import Aeres.Data.X690-DER.Time.MDHMS.Properties
import Aeres.Data.X690-DER.Time.MDHMS.TCB

module Aeres.Data.X690-DER.Time.MDHMS where

open Aeres.Data.X690-DER.Time.MDHMS.TCB public
  hiding (module MDHMS ; equivalent)

module MDHMS where
  open Aeres.Data.X690-DER.Time.MDHMS.Parser     public
  open Aeres.Data.X690-DER.Time.MDHMS.Properties public
  open Aeres.Data.X690-DER.Time.MDHMS.TCB        public
    using (equivalent)
  open Aeres.Data.X690-DER.Time.MDHMS.TCB.MDHMS  public
