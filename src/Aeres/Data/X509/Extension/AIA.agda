{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Extension.AIA.AccessDesc
import Aeres.Data.X509.Extension.AIA.Parser
import Aeres.Data.X509.Extension.AIA.TCB
import Aeres.Data.X509.Extension.AIA.Properties

module Aeres.Data.X509.Extension.AIA where

open Aeres.Data.X509.Extension.AIA.Parser public
open Aeres.Data.X509.Extension.AIA.TCB    public

module AIA where
  open Aeres.Data.X509.Extension.AIA.AccessDesc public
  open Aeres.Data.X509.Extension.AIA.Properties public
