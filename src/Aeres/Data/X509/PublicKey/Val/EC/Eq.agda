{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.EC.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.EC.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ ECBitString
  Eq≋._≋?_ eq≋ (mk×ₚ bits₁ (─ os₁)) (mk×ₚ bits₂ (─ os₂)) =
    case bits₁ ≋? bits₂ ret (const _) of λ where
      (yes ≋-refl) →
        case (‼ TLV.unambiguous
               (Seq.unambiguous
                 (λ where refl refl → refl)
                 (λ where _ refl refl → refl)
                 OctetString.unambiguous)
               os₁ os₂)
        ret (const _) of λ where
          refl → yes ≋-refl
      (no ¬≋) →
        no λ where ≋-refl → contradiction ≋-refl ¬≋
