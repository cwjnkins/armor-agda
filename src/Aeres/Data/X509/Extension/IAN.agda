{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Extension.IAN.Parser
import Aeres.Data.X509.Extension.IAN.TCB
import Aeres.Data.X509.Extension.IAN.Properties

module Aeres.Data.X509.Extension.IAN where

open Aeres.Data.X509.Extension.IAN.Parser public
open Aeres.Data.X509.Extension.IAN.TCB    public

module IAN where
  open Aeres.Data.X509.Extension.IAN.Properties public
