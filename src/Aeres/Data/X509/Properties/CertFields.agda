{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.TBSCertFields as TBSCertFieldsProps
open import Aeres.Data.X690-DER
open import Aeres.Prelude

module Aeres.Data.X509.Properties.CertFields where

open import Aeres.Grammar.Definitions UInt8
open ≡-Reasoning

Rep : @0 List UInt8 → Set
Rep = &ₚ (X509.TBSCert ×ₚ Singleton) (&ₚ SignAlg (BitString ×ₚ Singleton))

equiv : Equivalent Rep X509.CertFields
proj₁ equiv (mk&ₚ (mk×ₚ fstₚ₁ s refl) (mk&ₚ fstₚ₂ (mk×ₚ sndₚ₁ s' refl) refl) bs≡) =
  X509.mkCertFields fstₚ₁ s fstₚ₂ sndₚ₁ s' bs≡
proj₂ equiv (X509.mkCertFields tbs tbsBytes signAlg signature signatureBytes bs≡)
  = mk&ₚ (mk×ₚ tbs tbsBytes refl) (mk&ₚ signAlg (mk×ₚ signature signatureBytes refl) refl) bs≡

iso   : Iso Rep X509.CertFields
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk&ₚ (mk×ₚ fstₚ₁ s refl) (mk&ₚ fstₚ₂ (mk×ₚ sndₚ₁ _ refl) refl) refl) = refl
proj₂ (proj₂ iso) (X509.mkCertFields tbs tbsBytes signAlg signature sbytes refl) = refl

instance
  CertEq : Eq (Exists─ (List UInt8) X509.CertFields)
  CertEq = (isoEq iso eq)
    where
    eq : Eq (Exists─ (List UInt8) Rep)
    eq = eq&ₚ (eqΣₚ it λ _ → it)
           (eq&ₚ (Eq≋⇒Eq it)
             (eqΣₚ (Eq≋⇒Eq (TLV.EqTLV ⦃ Eq⇒Eq≋ BitString.eq ⦄)) λ _ → it))

@0 unambiguous : Unambiguous X509.CertFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ (unambiguous×ₚ (TLV.unambiguous TBSCertFieldsProps.unambiguous) (λ where self self → refl))
      (nonnestingΣₚ₁ TLV.nonnesting)
      (unambiguous&ₚ (TLV.unambiguous SignAlg.unambiguous) TLV.nonnesting
        (unambiguous×ₚ (TLV.unambiguous BitString.unambiguous) (λ where self self → refl))))
