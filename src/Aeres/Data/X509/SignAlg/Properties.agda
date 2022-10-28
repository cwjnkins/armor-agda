{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.SignAlg.TCB
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.SignAlg.Properties where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8

iso : Iso (&ₚ OID (Option (NotEmpty OctetStringValue))) SignAlgFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkSignAlgFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (mkSignAlgFields signOID param bs≡) = mk&ₚ signOID param bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkSignAlgFields signOID param bs≡) = refl

@0 unambiguous : Unambiguous SignAlgFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.unambiguous-&₁option₁
      OID.unambiguous TLV.nonnesting
      (unambiguous×ₚ OctetString.unambiguous λ a₁ a₂ → erased-unique ≤-irrelevant a₁ a₂)
      λ where (mk×ₚ _ () refl) refl)


instance
  SignAlgFieldsEq≋ : Eq≋ SignAlgFields
  Eq≋._≋?_ SignAlgFieldsEq≋{bs₁} {bs₂} sf₁ sf₂ =
    case SignAlgFields.signOID sf₁ ≋? SignAlgFields.signOID sf₂ of λ where
      (no ¬oid₁≋oid₂) →
        no λ where
          ≋-refl → contradiction ≋-refl ¬oid₁≋oid₂
      (yes ≋-refl) →
        case SignAlgFields.param sf₁ ≋? SignAlgFields.param sf₂ of λ where
          (no ¬param₁≋param₂) →
            no λ where
              ≋-refl → contradiction ≋-refl ¬param₁≋param₂
          (yes ≋-refl) → yes (‼
            let @0 bs₁≡bs₂ : bs₁ ≡ bs₂
                bs₁≡bs₂ = trans (SignAlgFields.bs≡ sf₁) (sym (SignAlgFields.bs≡ sf₂))
            in
            case (‼ bs₁≡bs₂) of λ where
              refl →
                case (‼ ≡-unique (SignAlgFields.bs≡ sf₁) (SignAlgFields.bs≡ sf₂)) ret (const _) of λ where
                  refl → ≋-refl)

  SignAlgFieldsEq : Eq (Exists─ (List UInt8) SignAlgFields)
  SignAlgFieldsEq = Eq≋⇒Eq it
