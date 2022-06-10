{-# OPTIONS --subtyping --allow-unsolved-metas #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Data.X509.Properties.BitstringValue as BitstringProps
import      Aeres.Data.X509.Properties.SignAlgFields  as SignAlgFieldsProps
import      Aeres.Data.X509.Properties.TLV            as TLVprops
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.PublicKeyFields where

open Base256
open Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum Dig
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
    (unambiguous&ₚᵈ {!!} {!!} {!!} )

-- unambiguous{xs} (X509.mkPublicKeyFields{alg = alg₁}{pk₁} signalg₁ pubkey₁ bs≡₁) (X509.mkPublicKeyFields{alg = alg₂}{pk₂} signalg₂ pubkey₂ bs≡₂) =
--   ≡-elim (λ {alg₂} alg≡ → ∀ (signalg₂ : X509.SignAlg alg₂) bs≡₂ → X509.mkPublicKeyFields signalg₁ pubkey₁ bs≡₁ ≡ X509.mkPublicKeyFields signalg₂ pubkey₂ bs≡₂)
--     (λ signalg₂' bs≡₂' →
--       ≡-elim (λ {pk₂} pk≡ → ∀ (pubkey₂ : BitString pk₂) bs≡₂ → X509.mkPublicKeyFields signalg₁ pubkey₁ bs≡₁ ≡ X509.mkPublicKeyFields signalg₂' pubkey₂ bs≡₂)
--         (λ pubkey₂' bs≡₂' →
--           subst₂ (λ x y → X509.mkPublicKeyFields signalg₁ pubkey₁ bs≡₁ ≡ X509.mkPublicKeyFields x y bs≡₂')
--             (TLVprops.unambiguous SignAlgFieldsProps.unambiguous signalg₁ signalg₂') (TLVprops.unambiguous BitstringProps.unambiguous pubkey₁ pubkey₂')
--             (subst₀ (λ x → X509.mkPublicKeyFields signalg₁ pubkey₁ bs≡₁ ≡ X509.mkPublicKeyFields signalg₁ pubkey₁ x) (≡-unique bs≡₁ bs≡₂')
--               refl))
--         pk≡ pubkey₂ bs≡₂')
--     alg≡ signalg₂ bs≡₂
--   where
--   @0 bs≡ : alg₁ ++ pk₁ ≡ alg₂ ++ pk₂
--   bs≡ = trans (sym bs≡₁) bs≡₂

--   @0 alg≡ : alg₁ ≡ alg₂
--   alg≡ = TLVprops.nonnesting bs≡ signalg₁ signalg₂

--   @0 pk≡ : pk₁ ≡ pk₂
--   pk≡ = Lemmas.++-cancel≡ˡ _ _ alg≡ bs≡


nonnesting : NonNesting X509.PublicKeyFields
nonnesting {xs₁} {ys₁} {xs₂} {ys₂} x (X509.mkPublicKeyFields {alg = alg} {pk = pk} pkalg pubkey bs≡) (X509.mkPublicKeyFields {alg = alg₁} {pk = pk₁} pkalg₁ pubkey₁ bs≡₁) = {!!}





-- nonnesting {xs₁} {ys₁} {xs₂} {ys₂} x (X509.mkPublicKeyFields {alg = alg} {pk = pk} signalg pubkey bs≡) (X509.mkPublicKeyFields {alg = alg₁} {pk = pk₁} signalg₁ pubkey₁ bs≡₁)
--   with ‼ TLVprops.nonnesting x' signalg signalg₁
--   | ‼ x'
--   where
--   @0 x' : alg ++ pk ++ ys₁ ≡ alg₁ ++ pk₁ ++ ys₂
--   x' = begin (alg ++ pk ++ ys₁ ≡⟨ solve (++-monoid Dig) ⟩ -- assoc + identity
--              (alg ++ pk) ++ ys₁ ≡⟨ cong (_++ ys₁ ) (sym bs≡) ⟩
--              xs₁ ++ ys₁ ≡⟨ x ⟩
--              xs₂ ++ ys₂ ≡⟨  cong (_++ ys₂ ) (bs≡₁) ⟩
--              (alg₁ ++ pk₁) ++ ys₂ ≡⟨  solve (++-monoid Dig) ⟩
--              alg₁ ++ pk₁ ++ ys₂ ∎)
-- ... | foo | x'
--   with ‼ TLVprops.nonnesting (Lemmas.++-cancel≡ˡ _ _ foo x') pubkey pubkey₁
-- ... | bar = ‼ (begin (xs₁ ≡⟨ bs≡ ⟩
--                      alg ++ pk ≡⟨ cong₂ _++_ foo bar ⟩
--                      alg₁ ++ pk₁ ≡⟨ sym bs≡₁ ⟩
--                      xs₂ ∎))
