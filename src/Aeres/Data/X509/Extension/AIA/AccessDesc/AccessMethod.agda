{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.Eq
import Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.Parser
import Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.Properties
import Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.TCB

module Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod where

open Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.Parser public
open Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.TCB    public

module AccessMethod where
  open Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.Eq         public
  open Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.Properties public
