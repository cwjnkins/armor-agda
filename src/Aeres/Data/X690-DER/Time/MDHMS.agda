{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Time.MDHMS.Ordering
import Aeres.Data.X690-DER.Time.MDHMS.Parser
import Aeres.Data.X690-DER.Time.MDHMS.Properties
import Aeres.Data.X690-DER.Time.MDHMS.TCB

module Aeres.Data.X690-DER.Time.MDHMS where

open Aeres.Data.X690-DER.Time.MDHMS.TCB public
  hiding (module MDHMS ; equivalent ; _MDHMS<'_ ; _MDHMS<_ ; _MDHMS≤_)

module MDHMS where
  open Aeres.Data.X690-DER.Time.MDHMS.Ordering   public
    renaming (trans-MDHMS<' to trans<' ; compare-MDHMS< to compare ; _MDHMS≤?_ to _≤?_)
  open Aeres.Data.X690-DER.Time.MDHMS.Parser     public
  open Aeres.Data.X690-DER.Time.MDHMS.Properties public
  open Aeres.Data.X690-DER.Time.MDHMS.TCB        public
    using (equivalent)
    renaming (_MDHMS<'_ to _<'_ ; _MDHMS<_ to _<_ ; _MDHMS≤_ to _≤_)
  open Aeres.Data.X690-DER.Time.MDHMS.TCB.MDHMS  public
