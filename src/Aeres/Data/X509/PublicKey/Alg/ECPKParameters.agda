{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters
import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.Parser
import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.Properties
import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.TCB

module Aeres.Data.X509.PublicKey.Alg.ECPKParameters where

open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.TCB    public
  hiding (module ECPKParameters ; equivalent)

module ECPKParameters where
  open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters public
  open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.Parser       public
  open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.Properties   public
  open Aeres.Data.X509.PublicKey.Alg.ECPKParameters.TCB          public
    using (equivalent)
