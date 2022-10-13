{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.IA5String.Parser
import Aeres.Data.X509.IA5String.Properties
import Aeres.Data.X509.IA5String.TCB

module Aeres.Data.X509.IA5String where

open Aeres.Data.X509.IA5String.Parser public
open Aeres.Data.X509.IA5String.TCB    public

module IA5String where
  open Aeres.Data.X509.IA5String.Properties public
