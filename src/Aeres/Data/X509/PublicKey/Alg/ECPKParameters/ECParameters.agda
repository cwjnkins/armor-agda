{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve
import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID
import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Parser
import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Properties
import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.TCB

module Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters where

open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.TCB    public
  hiding (equivalent)

module ECParameters where
  open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Parser public
  open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Properties public
  open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.TCB        public
    using (equivalent)
