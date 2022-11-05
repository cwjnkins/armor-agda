{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
import      Aeres.Data.X509.HashAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.HashAlg.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

SHA1 = AlgorithmIdentifier
         λ o →    const (_≋_{A = OIDValue} (TLV.val o) OIDs.SHA1)
               ×ₚ Option Null

SHA224 =
  AlgorithmIdentifier
    λ o →    const (_≋_{A = OIDValue} (TLV.val o) OIDs.SHA224)
          ×ₚ Option Null

SHA256 =
  AlgorithmIdentifier
    λ o →    const (_≋_{A = OIDValue} (TLV.val o) OIDs.SHA256)
          ×ₚ Option Null

SHA384 =
  AlgorithmIdentifier
    λ o →    const (_≋_{A = OIDValue} (TLV.val o) OIDs.SHA384)
          ×ₚ Option Null

SHA512 =
  AlgorithmIdentifier
    λ o →    const (_≋_{A = OIDValue} (TLV.val o) OIDs.SHA512)
          ×ₚ Option Null
