{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.SignAlg.DSA.TCB
  using (DSA-Like)
open import Aeres.Data.X690-DER.Null.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.ECDSA.TCB where

open Aeres.Grammar.Definitions UInt8

SHA1   = DSA-Like OIDs.ECDSA.SHA1
SHA224 = DSA-Like OIDs.ECDSA.SHA224
SHA256 = DSA-Like OIDs.ECDSA.SHA256
SHA384 = DSA-Like OIDs.ECDSA.SHA384
SHA512 = DSA-Like OIDs.ECDSA.SHA512
