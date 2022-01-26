{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.OID              as OIDProps
import      Aeres.Data.X509.Properties.OIDSub           as OIDSubProps
import      Aeres.Data.X509.Properties.OctetstringValue as OSProps
import      Aeres.Data.X509.Properties.TLV              as TLVProps
import      Aeres.Data.X509.Properties.SequenceOf       as SeqProps
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.SignAlgFields where

open Base256
open Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig

iso : Iso (&ₚ Generic.OID (Option (NotEmpty Generic.OctetstringValue))) X509.SignAlgFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkSignAlgFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (X509.mkSignAlgFields signOID param bs≡) = mk&ₚ signOID param bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkSignAlgFields signOID param bs≡) = refl

@0 unambiguous : Unambiguous X509.SignAlgFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.unambiguous-&₁option₁
      OIDProps.unambiguous TLVProps.nonnesting
      (unambiguous×ₚ OSProps.unambiguous ≤-irrelevant)
      λ where (mk×ₚ _ () refl) refl)


instance
  SignAlgFieldsEq : Eq≋ X509.SignAlgFields
  Eq≋._≋?_ SignAlgFieldsEq{bs₁} {bs₂} sf₁ sf₂
    with X509.SignAlgFields.signOID sf₁ ≋? X509.SignAlgFields.signOID sf₂
    |    X509.SignAlgFields.param   sf₁ ≋? X509.SignAlgFields.param   sf₂
  ... | no ¬oid₁≋oid₂ | _ = no λ where
    ≋-refl → contradiction ≋-refl ¬oid₁≋oid₂
  ... | yes ≋-refl | no ¬param₁≋param₂ = no λ where
    ≋-refl → contradiction ≋-refl ¬param₁≋param₂
  ... | yes ≋-refl | yes ≋-refl
    with ‼ bs₁≡bs₂
    where
    @0 bs₁≡bs₂ : bs₁ ≡ bs₂
    bs₁≡bs₂ = trans (X509.SignAlgFields.bs≡ sf₁) (sym (X509.SignAlgFields.bs≡ sf₂))
  ... | refl
    with ‼ ≡-unique (X509.SignAlgFields.bs≡ sf₁) (X509.SignAlgFields.bs≡ sf₂)
  ... | refl = yes ≋-refl
