{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.EC.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.EC.Properties where

open Aeres.Grammar.Definitions UInt8

@0 nonnesting : NonNesting ECBitString
nonnesting = nonnesting×ₚ₁ TLV.nonnesting

@0 unambiguous : Unambiguous ECBitString
unambiguous =
  unambiguous×ₚ
    (TLV.unambiguous BitString.unambiguous)
    λ where
      (─ a₁) (─ a₂) →
        cong ─_
          (‼ TLV.unambiguous
            (unambiguous&ₚ
              (λ where refl refl → refl)
              (λ where _ refl refl → refl)
              OctetString.unambiguous)
            a₁ a₂)
