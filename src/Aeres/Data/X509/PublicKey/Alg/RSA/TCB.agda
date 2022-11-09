{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.SignAlg.DSA.TCB
  using (DSA-Like)
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs

module Aeres.Data.X509.PublicKey.Alg.RSA.TCB where

RSA = DSA-Like OIDs.RSA
