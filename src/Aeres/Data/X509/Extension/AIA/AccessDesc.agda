{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod
import Aeres.Data.X509.Extension.AIA.AccessDesc.Eq
import Aeres.Data.X509.Extension.AIA.AccessDesc.Parser
import Aeres.Data.X509.Extension.AIA.AccessDesc.Properties
import Aeres.Data.X509.Extension.AIA.AccessDesc.TCB

module Aeres.Data.X509.Extension.AIA.AccessDesc where

open Aeres.Data.X509.Extension.AIA.AccessDesc.Parser public
open Aeres.Data.X509.Extension.AIA.AccessDesc.TCB    public

module AccessDesc where
  open Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod public
  open Aeres.Data.X509.Extension.AIA.AccessDesc.Eq           public
  open Aeres.Data.X509.Extension.AIA.AccessDesc.Properties   public
