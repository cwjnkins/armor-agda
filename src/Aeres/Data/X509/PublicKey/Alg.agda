{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.PublicKey.Alg.TCB
import Aeres.Data.X509.PublicKey.Alg.Parser
import Aeres.Data.X509.PublicKey.Alg.Properties

module Aeres.Data.X509.PublicKey.Alg where

open Aeres.Data.X509.PublicKey.Alg.TCB public
  hiding (getOID)
open Aeres.Data.X509.PublicKey.Alg.Parser public

module Alg where
  open Aeres.Data.X509.PublicKey.Alg.TCB public
    using (getOID)
  open Aeres.Data.X509.PublicKey.Alg.Properties public
