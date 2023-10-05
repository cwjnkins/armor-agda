{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Time.GeneralizedTime.Foreign
import Aeres.Data.X690-DER.Time.GeneralizedTime.Ordering
import Aeres.Data.X690-DER.Time.GeneralizedTime.Parser
import Aeres.Data.X690-DER.Time.GeneralizedTime.Properties
import Aeres.Data.X690-DER.Time.GeneralizedTime.TCB

module Aeres.Data.X690-DER.Time.GeneralizedTime where

open Aeres.Data.X690-DER.Time.GeneralizedTime.TCB public
  hiding (equivalent)

module GeneralizedTime where
  open Aeres.Data.X690-DER.Time.GeneralizedTime.Foreign    public
  open Aeres.Data.X690-DER.Time.GeneralizedTime.Ordering   public
    renaming ( compare-GeneralizedTimeFields< to <-compare
             ; _GeneralizedTimeFields≤?_ to _≤?_)
  open Aeres.Data.X690-DER.Time.GeneralizedTime.Parser     public
  open Aeres.Data.X690-DER.Time.GeneralizedTime.Properties public
  open Aeres.Data.X690-DER.Time.GeneralizedTime.TCB        public
    using (equivalent)
