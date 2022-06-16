{-# OPTIONS --subtyping --allow-unsolved-metas #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.BitstringValue as BitstringProps
import      Aeres.Data.X509.Properties.SignAlgFields  as SignAlgFieldsProps
import      Aeres.Data.X509.Properties.PkAlg          as PkAlgProps
import      Aeres.Data.X509.Properties.PkVal          as PkValProps
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.PublicKeyFields where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8
open ≡-Reasoning

Rep : @0 List UInt8 → Set
Rep = &ₚᵈ X509.PkAlg λ _ → X509.PkVal ∘ X509.PkAlg.getOID

equivalent : Equivalent Rep X509.PublicKeyFields
proj₁ equivalent (Aeres.Grammar.Definitions.mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkPublicKeyFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (X509.mkPublicKeyFields pkalg pubkey bs≡) = Aeres.Grammar.Definitions.mk&ₚ pkalg pubkey bs≡

iso : Iso Rep X509.PublicKeyFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkPublicKeyFields pkalg pubkey bs≡) = refl

@0 unambiguous : Unambiguous X509.PublicKeyFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚᵈ PkAlgProps.unambiguous PkAlgProps.nonnesting
      λ _ → PkValProps.unambiguous _)

nonnesting : NonNesting X509.PublicKeyFields
nonnesting{xs₁}{ys₁}{xs₂}{ys₂} x (X509.mkPublicKeyFields {alg = alg} {pk = pk} pkalg pubkey bs≡) (X509.mkPublicKeyFields {alg = alg₁} {pk = pk₁} pkalg₁ pubkey₁ bs≡₁) = {!!}


-- nonnesting {xs₁} {ys₁} {xs₂} {ys₂} x (X509.mkPublicKeyFields {alg = alg} {pk = pk} signalg pubkey bs≡) (X509.mkPublicKeyFields {alg = alg₁} {pk = pk₁} signalg₁ pubkey₁ bs≡₁)
--   with ‼ TLVprops.nonnesting x' signalg signalg₁
--   | ‼ x'
--   where
--   @0 x' : alg ++ pk ++ ys₁ ≡ alg₁ ++ pk₁ ++ ys₂
--   x' = begin (alg ++ pk ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩ -- assoc + identity
--              (alg ++ pk) ++ ys₁ ≡⟨ cong (_++ ys₁ ) (sym bs≡) ⟩
--              xs₁ ++ ys₁ ≡⟨ x ⟩
--              xs₂ ++ ys₂ ≡⟨  cong (_++ ys₂ ) (bs≡₁) ⟩
--              (alg₁ ++ pk₁) ++ ys₂ ≡⟨  solve (++-monoid UInt8) ⟩
--              alg₁ ++ pk₁ ++ ys₂ ∎)
-- ... | foo | x'
--   with ‼ TLVprops.nonnesting (Lemmas.++-cancel≡ˡ _ _ foo x') pubkey pubkey₁
-- ... | bar = ‼ (begin (xs₁ ≡⟨ bs≡ ⟩
--                      alg ++ pk ≡⟨ cong₂ _++_ foo bar ⟩
--                      alg₁ ++ pk₁ ≡⟨ sym bs≡₁ ⟩
--                      xs₂ ∎))
