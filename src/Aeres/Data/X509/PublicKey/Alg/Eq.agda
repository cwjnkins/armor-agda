{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.TCB
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey.Alg.ECPKParameters
open import Aeres.Data.X509.PublicKey.Alg.RSAPKParameters
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋ : Eq≋ (DefinedByOIDFields PKParameters)
  eq≋ =
    DefinedByOID.eq≋ PKParameters
      λ {bs} o →
        case (-, TLV.val o) ∈? OIDs.Supported
        ret (λ o∈? → Eq≋ (PKParameters' o o∈?))
        of λ where
          (no ¬p) → it
          (yes (here px)) → it
          (yes (there (here px))) → it
