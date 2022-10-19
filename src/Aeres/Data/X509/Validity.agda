{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Validity.Parser
import Aeres.Data.X509.Validity.Properties
import Aeres.Data.X509.Validity.TCB

module Aeres.Data.X509.Validity where

open Aeres.Data.X509.Validity.Parser public

module Validity where
  open Aeres.Data.X509.Validity.Properties public
  open Aeres.Data.X509.Validity.TCB        public

open Validity public using (ValidityFields; Validity)