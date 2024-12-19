{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509.Name
open import Armor.Data.X509.Semantic.StringPrep.ExecDS
open import Armor.Data.X509.Semantic.StringPrep.ExecPS
open import Armor.Data.X509.Semantic.StringPrep.ExecIS
open import Armor.Data.X509.Extension
open import Armor.Data.X509.Extension.AKI
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.SetOf
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.X509.Semantic.Chain.KIMatch where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Option   UInt8
open Armor.Grammar.Parallel    UInt8

KIMatch : Exists─ (List UInt8) (Option ExtensionFieldAKI)
          → Exists─ (List UInt8) (Option ExtensionFieldSKI)
          → Set
KIMatch (─ .[] , none) (─ .[] , none) = ⊤
KIMatch (─ .[] , none) (─ _ , some _) = ⊤
KIMatch (─ _ , some _) (─ .[] , none) = ⊥
KIMatch (─ _ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₂ (mkAKIFieldsSeqFields none authcertiss authcertsn bs≡₅) len≡₂ bs≡₄) len≡ bs≡₂) bs≡)) (─ _ , some (mkExtensionFields extnId₁ extnId≡₁ crit₁ (mkTLV len₁ val₁ len≡₁ bs≡₃) bs≡₁)) = ⊤
KIMatch (─ _ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₂ (mkAKIFieldsSeqFields (some (mkTLV len₃ akidval len≡₃ refl)) authcertiss authcertsn refl) len≡₂ refl) len≡ refl) refl)) (─ _ , some (mkExtensionFields extnId₁ extnId≡₁ crit₁ (mkTLV len₁ (mkTLV len₄ skidval len≡₄ refl) len≡₁ refl) refl)) =
  _≋_ {A = OctetStringValue} akidval skidval


kiMatch? : (id₁ : Exists─ (List UInt8) (Option ExtensionFieldAKI))
          → (id₂ : Exists─ (List UInt8) (Option ExtensionFieldSKI))
          → Dec (KIMatch id₁ id₂)
kiMatch? (─ .[] , none) (─ .[] , none) = yes tt
kiMatch? (─ .[] , none) (─ _ , some _) = yes tt
kiMatch? (─ _ , some _) (─ .[] , none) = no λ ()
kiMatch? (─ _ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₂ (mkAKIFieldsSeqFields none authcertiss authcertsn bs≡₅) len≡₂ bs≡₄) len≡ bs≡₂) bs≡)) (─ _ , some (mkExtensionFields extnId₁ extnId≡₁ crit₁ (mkTLV len₁ val₁ len≡₁ bs≡₃) bs≡₁)) = yes tt
kiMatch? (─ _ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₂ (mkAKIFieldsSeqFields (some (mkTLV len₃ akidval len≡₃ refl)) authcertiss authcertsn refl) len≡₂ refl) len≡ refl) refl)) (─ _ , some (mkExtensionFields extnId₁ extnId≡₁ crit₁ (mkTLV len₁ (mkTLV len₄ skidval len≡₄ refl) len≡₁ refl) refl)) =
  _≋?_ {A = OctetStringValue} akidval skidval
