{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X509.SignAlg.DSA.Parser
  using (parseDSA-Like)

module Aeres.Data.X509.PublicKey.Alg.RSA.Parser where

parseRSA = parseDSA-Like OIDs.RSA "X509: PublicKeyAlg: RSA"
