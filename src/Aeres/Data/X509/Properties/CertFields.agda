{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.SignAlgFields as SignAlgFieldsProps
import      Aeres.Data.X509.Properties.TBSCertFields as TBSCertFieldsProps
open import Aeres.Data.X690-DER
open import Aeres.Prelude

module Aeres.Data.X509.Properties.CertFields where

open import Aeres.Grammar.Definitions UInt8
open ≡-Reasoning

Rep : @0 List UInt8 → Set
Rep = &ₚ (X509.TBSCert ×ₚ Singleton) (&ₚ X509.SignAlg BitString)

equiv : Equivalent Rep X509.CertFields
proj₁ equiv (mk&ₚ (mk×ₚ fstₚ₁ s refl) (mk&ₚ fstₚ₂ sndₚ₁ refl) bs≡) =
  X509.mkCertFields fstₚ₁ s fstₚ₂ sndₚ₁ bs≡
proj₂ equiv (X509.mkCertFields tbs tbsBytes signAlg signature bs≡)
  = mk&ₚ (mk×ₚ tbs tbsBytes refl) (mk&ₚ signAlg signature refl) bs≡

iso   : Iso Rep X509.CertFields
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk&ₚ (mk×ₚ fstₚ₁ s refl) (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (X509.mkCertFields tbs tbsBytes signAlg signature refl) = refl

instance
  CertEq : Eq (Exists─ (List UInt8) X509.Cert)
  CertEq = Eq≋⇒Eq (TLV.EqTLV ⦃ Eq⇒Eq≋ (isoEq iso eq) ⦄)
    where
    eq : Eq (Exists─ (List UInt8) Rep)
    eq = eq&ₚ (eqΣₚ it λ _ → it) (eq&ₚ (Eq≋⇒Eq it) (Eq≋⇒Eq (TLV.EqTLV ⦃ Eq⇒Eq≋ BitString.eq ⦄)))

@0 unambiguous : Unambiguous X509.CertFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ (unambiguous×ₚ (TLV.unambiguous TBSCertFieldsProps.unambiguous) (λ where self self → refl))
      (nonnestingΣₚ₁ TLV.nonnesting)
      (unambiguous&ₚ (TLV.unambiguous SignAlgFieldsProps.unambiguous) TLV.nonnesting
        (TLV.unambiguous BitString.unambiguous)))
