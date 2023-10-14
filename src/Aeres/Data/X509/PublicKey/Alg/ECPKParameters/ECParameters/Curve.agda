{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Eq
import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Parser
import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Properties
-- import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Serializer
import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.TCB

module Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve where

open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.TCB    public
  hiding (equivalent)

module Curve where
  open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Eq         public
--   open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Serializer public
  open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Parser public
  open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Properties public
  open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.TCB        public
    using (equivalent)
