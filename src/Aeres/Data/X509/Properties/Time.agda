{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Properties.TLV as TLVprops
open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.Time where

open Base256
open import Aeres.Grammar.Definitions Dig

nonempty : NonEmpty Generic.Time
nonempty (Generic.utctm ()) refl
nonempty (Generic.gentm ()) refl

module UTC where
  @0 nonnesting : NonNesting Generic.UtcTimeFields
  nonnesting {xs₁ = xs₁} {xs₂ = xs₂} x (Generic.mkUtcTimeFields year yearRange mmddhhmmss term bs≡) (Generic.mkUtcTimeFields year₁ yearRange₁ mmddhhmmss₁ term₁ bs≡₁)
    with Lemmas.length-++-≡ xs₁ _ xs₂ _ x (trans₀ (cong length bs≡) (cong length (sym bs≡₁)))
  ... | fst , snd = fst

module GenTime where
  postulate
    @0 nonnesting : NonNesting Generic.GenTimeFields
  -- nonnesting {xs₁ = xs₁} {xs₂ = xs₂} x (Generic.mkGenTimeFields year yearRange mmddhhmmss sfrac bs≡) (Generic.mkGenTimeFields year₁ yearRange₁ mmddhhmmss₁ sfrac₁ bs≡₁)
  --   with Lemmas.length-++-≡ xs₁ _ xs₂ _ x (trans₀ (cong length bs≡) (cong length (sym {!bs≡₁!})))
  -- ... | fst , snd = fst

@0 nonnesting : NonNesting Generic.Time
nonnesting x (Generic.utctm x₁) (Generic.utctm x₂) = ‼ TLVprops.nonnesting x x₁ x₂
nonnesting x (Generic.utctm x₁) (Generic.gentm x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (Generic.gentm x₁) (Generic.utctm x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (Generic.gentm x₁) (Generic.gentm x₂) = ‼ TLVprops.nonnesting x x₁ x₂
