{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.DisplayText.Parser
import Aeres.Data.X509.DisplayText.Properties
import Aeres.Data.X509.DisplayText.TCB

module Aeres.Data.X509.DisplayText where

open Aeres.Data.X509.DisplayText.Parser public
open Aeres.Data.X509.DisplayText.TCB public
  hiding (module DisplayText)

module DisplayText where
  open Aeres.Data.X509.DisplayText.Properties      public
  open Aeres.Data.X509.DisplayText.TCB.DisplayText public
