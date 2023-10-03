{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Time.UTCTime.Parser
import Aeres.Data.X690-DER.Time.UTCTime.Properties
import Aeres.Data.X690-DER.Time.UTCTime.TCB

module Aeres.Data.X690-DER.Time.UTCTime where

open Aeres.Data.X690-DER.Time.UTCTime.TCB public
  hiding (equivalent)

module UTCTime where
  open Aeres.Data.X690-DER.Time.UTCTime.Parser     public
  open Aeres.Data.X690-DER.Time.UTCTime.Properties public
  open Aeres.Data.X690-DER.Time.UTCTime.TCB        public
    using (equivalent)
