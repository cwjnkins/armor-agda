{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.OctetstringValue as OSProps
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.SignAlgFields where

open Base256
open Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig

iso : Iso (&ₚ OID (Option (NotEmpty OctetStringValue))) X509.SignAlg.SignAlgFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.SignAlg.mkSignAlgFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (X509.SignAlg.mkSignAlgFields signOID param bs≡) = mk&ₚ signOID param bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.SignAlg.mkSignAlgFields signOID param bs≡) = refl

@0 unambiguous : Unambiguous X509.SignAlg.SignAlgFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.unambiguous-&₁option₁
      OID.unambiguous TLV.nonnesting
      (unambiguous×ₚ OSProps.unambiguous λ a₁ a₂ → erased-unique ≤-irrelevant a₁ a₂)
      λ where (mk×ₚ _ () refl) refl)


instance
  SignAlgFieldsEq : Eq≋ X509.SignAlg.SignAlgFields
  Eq≋._≋?_ SignAlgFieldsEq{bs₁} {bs₂} sf₁ sf₂ =
    case X509.SignAlg.SignAlgFields.signOID sf₁ ≋? X509.SignAlg.SignAlgFields.signOID sf₂ of λ where
      (no ¬oid₁≋oid₂) →
        no λ where
          ≋-refl → contradiction ≋-refl ¬oid₁≋oid₂
      (yes ≋-refl) →
        case X509.SignAlg.SignAlgFields.param sf₁ ≋? X509.SignAlg.SignAlgFields.param sf₂ of λ where
          (no ¬param₁≋param₂) →
            no λ where
              ≋-refl → contradiction ≋-refl ¬param₁≋param₂
          (yes ≋-refl) → yes (‼
            let @0 bs₁≡bs₂ : bs₁ ≡ bs₂
                bs₁≡bs₂ = trans (X509.SignAlg.SignAlgFields.bs≡ sf₁) (sym (X509.SignAlg.SignAlgFields.bs≡ sf₂))
            in
            case (‼ bs₁≡bs₂) of λ where
              refl →
                case (‼ ≡-unique (X509.SignAlg.SignAlgFields.bs≡ sf₁) (X509.SignAlg.SignAlgFields.bs≡ sf₂)) ret (const _) of λ where
                  refl → ≋-refl)
