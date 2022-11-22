{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.GeneralName.Eq
import Aeres.Data.X509.GeneralName.Parser
import Aeres.Data.X509.GeneralName.Properties
import Aeres.Data.X509.GeneralName.TCB

module Aeres.Data.X509.GeneralName where

open Aeres.Data.X509.GeneralName.Parser public
open Aeres.Data.X509.GeneralName.TCB public
  hiding (module GeneralName)

module GeneralName where
  open Aeres.Data.X509.GeneralName.Eq public
  open Aeres.Data.X509.GeneralName.Properties public

