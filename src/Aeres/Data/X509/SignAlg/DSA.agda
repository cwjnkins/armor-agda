{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.SignAlg.DSA.Eq
import Aeres.Data.X509.SignAlg.DSA.Parser
import Aeres.Data.X509.SignAlg.DSA.Properties
import Aeres.Data.X509.SignAlg.DSA.TCB

module Aeres.Data.X509.SignAlg.DSA where

module DSA where
  open Aeres.Data.X509.SignAlg.DSA.Eq         public
  open Aeres.Data.X509.SignAlg.DSA.Parser     public
  open Aeres.Data.X509.SignAlg.DSA.Properties public
  open Aeres.Data.X509.SignAlg.DSA.TCB        public
