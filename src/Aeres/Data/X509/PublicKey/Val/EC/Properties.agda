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

module Aeres.Data.X509.PublicKey.Val.EC.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Seq         UInt8

@0 nosubstrings : NoSubstrings ECBitString
nosubstrings = Parallel.nosubstrings₁ TLV.nosubstrings

@0 unambiguous : Unambiguous ECBitString
unambiguous =
  Parallel.unambiguous×ₚ
    (TLV.unambiguous BitString.unambiguous)
    λ where
      (─ a₁) (─ a₂) →
        cong ─_
          (‼ TLV.unambiguous
            (Seq.unambiguous
              (λ where refl refl → refl)
              (λ where _ refl refl → refl)
              OctetString.unambiguous)
            a₁ a₂)
