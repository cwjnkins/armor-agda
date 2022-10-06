{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.TBSCertFields as TBSCert
import      Aeres.Data.X509.Properties.SignAlgFields as SignAlg
import      Aeres.Grammar.Definitions
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.Cert where

open Aeres.Grammar.Definitions UInt8

Rep : @0 List UInt8 → Set
Rep = &ₚ X509.TBSCert (&ₚ X509.SignAlg BitString)


equiv : Equivalent Rep X509.CertFields
proj₁ equiv (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) bs≡) = X509.mkCertFields fstₚ₁ fstₚ₂ sndₚ₁ bs≡
proj₂ equiv (X509.mkCertFields tbs signAlg signature bs≡) = mk&ₚ tbs (mk&ₚ signAlg signature refl) bs≡

iso   : Iso Rep X509.CertFields
proj₁ iso = equiv
proj₁ (proj₂ iso) (Aeres.Grammar.Definitions.mk&ₚ fstₚ₁ (Aeres.Grammar.Definitions.mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (X509.mkCertFields tbs signAlg signature refl) = refl

instance
  CertEq : Eq (Exists─ (List UInt8) X509.Cert)
  CertEq = Eq≋⇒Eq (TLV.EqTLV ⦃ Eq⇒Eq≋ (isoEq iso eq) ⦄)
    where
    eq : Eq (Exists─ (List UInt8) Rep)
    eq = eq&ₚ it (eq&ₚ (Eq≋⇒Eq it) (Eq≋⇒Eq (TLV.EqTLV ⦃ Eq⇒Eq≋ BitString.eq ⦄)))
