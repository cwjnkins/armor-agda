{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Validity.Time.Ordering
import Aeres.Data.X509.Validity.Time.Parser
import Aeres.Data.X509.Validity.Time.Properties
import Aeres.Data.X509.Validity.Time.TCB

module Aeres.Data.X509.Validity.Time where

open Aeres.Data.X509.Validity.Time.TCB public
  hiding (module Time ; equivalent ; getYear ; getMonth ; getDay ; getHour ; getMinute ; getSec)

module Time where
  open Aeres.Data.X509.Validity.Time.Ordering   public
    renaming (_Time≤_ to _≤_ ; _Time≤?_ to _≤?_)
  open Aeres.Data.X509.Validity.Time.Parser     public
  open Aeres.Data.X509.Validity.Time.Properties public
  open Aeres.Data.X509.Validity.Time.TCB        public
    using (equivalent ; getYear ; getMonth ; getDay ; getHour ; getMinute ; getSec)
