{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey.Alg.EC.TCB
open import Aeres.Data.X509.PublicKey.Alg.RSA.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

supportedPublicKeyAlgs : List (Exists─ _ OIDValue)
supportedPublicKeyAlgs =
  (-, OIDs.RSA) ∷ [ -, OIDs.EC ]

UnsupportedPublicKeyAlg =
  TLV Tag.Sequence
    (&ₚ (Σₚ OID (λ _ o → False ((-, TLV.val o) ∈? supportedPublicKeyAlgs)))
        OctetStringValue)

PublicKeyAlg : @0 List UInt8 → Set
PublicKeyAlg =
   Sum RSA
  (Sum EC
       UnsupportedPublicKeyAlg)
