{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Basis
import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Parser
import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Properties
import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.TCB

module Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo where

open Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.TCB public
  hiding (equivalent)

module CharTwo where
  open Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Basis      public
  open Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Parser     public
  open Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Properties public
  open Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.TCB        public
    using (equivalent)
