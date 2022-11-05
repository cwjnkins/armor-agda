{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.AlgorithmIdentifier.Parser
import Aeres.Data.X509.AlgorithmIdentifier.Properties
import Aeres.Data.X509.AlgorithmIdentifier.TCB

module Aeres.Data.X509.AlgorithmIdentifier where

open Aeres.Data.X509.AlgorithmIdentifier.Parser public
open Aeres.Data.X509.AlgorithmIdentifier.TCB    public

module AlgorithmIdentifier where
  open Aeres.Data.X509.AlgorithmIdentifier.Properties public
