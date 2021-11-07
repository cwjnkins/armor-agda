{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Properties.TLV as TLVprops

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.PublicKeyFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open ≡-Reasoning

postulate
  unambiguous : Unambiguous X509.PublicKeyFields

nonnesting : NonNesting X509.PublicKeyFields
nonnesting {xs₁} {ys₁} {xs₂} {ys₂} x (X509.mkPublicKeyFields {alg = alg} {pk = pk} signalg pubkey bs≡) (X509.mkPublicKeyFields {alg = alg₁} {pk = pk₁} signalg₁ pubkey₁ bs≡₁)
  with ‼ TLVprops.nonnesting x' signalg signalg₁
  | ‼ x'
  where
  @0 x' : alg ++ pk ++ ys₁ ≡ alg₁ ++ pk₁ ++ ys₂
  x' = begin (alg ++ pk ++ ys₁ ≡⟨ solve (++-monoid Dig) ⟩ -- assoc + identity
             (alg ++ pk) ++ ys₁ ≡⟨ cong (_++ ys₁ ) (sym bs≡) ⟩
             xs₁ ++ ys₁ ≡⟨ x ⟩
             xs₂ ++ ys₂ ≡⟨  cong (_++ ys₂ ) (bs≡₁) ⟩
             (alg₁ ++ pk₁) ++ ys₂ ≡⟨  solve (++-monoid Dig) ⟩
             alg₁ ++ pk₁ ++ ys₂ ∎)
... | foo | x' 
  with ‼ TLVprops.nonnesting (Lemmas.++-cancel≡ˡ _ _ foo x') pubkey pubkey₁
... | bar = ‼ (begin (xs₁ ≡⟨ bs≡ ⟩
                     alg ++ pk ≡⟨ cong₂ _++_ foo bar ⟩
                     alg₁ ++ pk₁ ≡⟨ sym bs≡₁ ⟩
                     xs₂ ∎))
