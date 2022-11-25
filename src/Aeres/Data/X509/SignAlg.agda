{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.SignAlg.DSA
import Aeres.Data.X509.SignAlg.ECDSA
import Aeres.Data.X509.SignAlg.Eq
import Aeres.Data.X509.SignAlg.Parser
import Aeres.Data.X509.SignAlg.Properties
import Aeres.Data.X509.SignAlg.RSA
import Aeres.Data.X509.SignAlg.TCB

module Aeres.Data.X509.SignAlg where

open Aeres.Data.X509.SignAlg.Parser public
open Aeres.Data.X509.SignAlg.TCB    public
  using (SignAlg)
  hiding (module SignAlg)

module SignAlg where
  open Aeres.Data.X509.SignAlg.DSA        public
  open Aeres.Data.X509.SignAlg.ECDSA      public
  open Aeres.Data.X509.SignAlg.Eq         public
  open Aeres.Data.X509.SignAlg.Properties public
  open Aeres.Data.X509.SignAlg.RSA        public
  open Aeres.Data.X509.SignAlg.TCB        public
    hiding (SignAlg)
