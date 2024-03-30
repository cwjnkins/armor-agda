open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.R18.TCB
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.IList
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.R18 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Option      UInt8

r18 : (kp : Maybe KeyPurpose) → ∀ {@0 bs} → (c : Cert bs) → Dec (R18 kp c)
r18 (just kp) c = r18' kp (proj₂ (Cert.getKU c)) (proj₂ (Cert.getEKU c))
  where
  keyPurposeConsistentWithEKU?
    : ∀ {@0 bs} → (kp : KeyPurpose) (eku : ExtensionFieldEKU bs)
      → Dec (KeyPurposeConsistentWithEKU kp eku)
  keyPurposeConsistentWithEKU? kp eku =
    _ ∈? _ ⊎-dec _ ∈? _

  r18' : ∀ {@0 bs₁ bs₂} → (kp : KeyPurpose) → (ku : Option ExtensionFieldKU bs₁) (eku : Option ExtensionFieldEKU bs₂)
         → Dec (R18' kp ku eku)
  r18' kp none none = yes tt
  r18' kp none (some eku) = keyPurposeConsistentWithEKU? kp eku
  r18' kp (some ku) none = T-dec
  r18' kp (some ku) (some eku) = T-dec ×-dec keyPurposeConsistentWithEKU? kp eku
r18 nothing c = T-dec
