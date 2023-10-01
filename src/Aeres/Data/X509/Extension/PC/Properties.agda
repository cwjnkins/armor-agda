{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.PC.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.PC.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

Rep = &ₚ (Option RequireExplicitPolicy) (Option InhibitPolicyMapping)

equivalent : Equivalent Rep PCFieldsSeqFields
proj₁ equivalent (mk&ₚ v₁ v₂ refl) = mkPCFieldsSeqFields v₁ v₂ refl
proj₂ equivalent (mkPCFieldsSeqFields v₁ v₂ refl) = mk&ₚ v₁ v₂ refl

iso : Iso Rep PCFieldsSeqFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ refl) = refl
proj₂ (proj₂ iso) (mkPCFieldsSeqFields require inhibit refl) = refl

@0 unambiguous : Unambiguous PCFieldsSeqFields
unambiguous =
  Iso.unambiguous iso
    (Unambiguous.option₂&₁
      (TLV.unambiguous λ {xs} → Int.unambiguous{xs})  TLV.nosubstrings TLV.nonempty
      (TLV.unambiguous λ {xs} → Int.unambiguous{xs}) TLV.nonempty (TLV.noconfusion λ ()))
