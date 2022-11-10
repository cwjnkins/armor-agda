{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.PublicKey.Alg.TCB as Alg
open import Aeres.Data.X509.PublicKey.Alg.TCB.OIDs
open import Aeres.Data.X509.PublicKey.Val.TCB
open import Aeres.Data.X509.PublicKey.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Properties where

open Aeres.Grammar.Definitions UInt8
open Alg using (PublicKeyAlg)

Rep : @0 List UInt8 → Set
Rep = &ₚᵈ PublicKeyAlg λ _ a → PublicKeyVal (proj₂ (Alg.getOID a))

postulate
  equiv : Equivalent PublicKeyFields Rep
