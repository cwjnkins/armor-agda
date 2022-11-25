{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Cert.TCB
open import Aeres.Data.X509.Extension.TCB
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X509.SignAlg
open import Aeres.Data.X509.TBSCert
import      Aeres.Data.X509.TBSCert.UID.TCB as TBSCert
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.Time.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.Cert.Properties where

open Aeres.Grammar.Definitions  UInt8
open Aeres.Grammar.IList        UInt8
open Aeres.Grammar.Option       UInt8

Rep : @0 List UInt8 → Set
Rep = &ₚ (TBSCert ×ₚ Singleton) (&ₚ SignAlg (BitString ×ₚ Singleton))

equiv : Equivalent Rep CertFields
proj₁ equiv (mk&ₚ (mk×ₚ fstₚ₁ s refl) (mk&ₚ fstₚ₂ (mk×ₚ sndₚ₁ s' refl) refl) bs≡) =
  mkCertFields fstₚ₁ s fstₚ₂ sndₚ₁ s' bs≡
proj₂ equiv (mkCertFields tbs tbsBytes signAlg signature signatureBytes bs≡)
  = mk&ₚ (mk×ₚ tbs tbsBytes refl) (mk&ₚ signAlg (mk×ₚ signature signatureBytes refl) refl) bs≡

iso   : Iso Rep CertFields
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk&ₚ (mk×ₚ fstₚ₁ s refl) (mk&ₚ fstₚ₂ (mk×ₚ sndₚ₁ _ refl) refl) refl) = refl
proj₂ (proj₂ iso) (mkCertFields tbs tbsBytes signAlg signature sbytes refl) = refl

-- instance
--   CertEq : Eq (Exists─ (List UInt8) CertFields)
--   CertEq = (isoEq iso eq)
--     where
--     eq : Eq (Exists─ (List UInt8) Rep)
--     eq = eq&ₚ (eqΣₚ it λ _ → it)
--            (eq&ₚ it
--              (eqΣₚ (Eq≋⇒Eq (TLV.EqTLV ⦃ Eq⇒Eq≋ BitString.eq ⦄)) λ _ → it))

@0 unambiguous : Unambiguous CertFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ
      (unambiguous×ₚ (TLV.unambiguous TBSCert.unambiguous) (λ where self self → refl))
      (nonnestingΣₚ₁ TLV.nonnesting)
      (unambiguous&ₚ SignAlg.unambiguous SignAlg.nonnesting
        (unambiguous×ₚ (TLV.unambiguous BitString.unambiguous) (λ where self self → refl))))

