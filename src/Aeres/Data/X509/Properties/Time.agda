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

  postulate
    @0 unambiguous : Unambiguous Generic.UtcTimeFields

module GenTime where
  @0 nonnesting : NonNesting Generic.GenTimeFields
  nonnesting {xs₁ = xs₁} {xs₂ = xs₂} x (Generic.mkGenTimeFields year yearRange (Generic.mkMDHMSFields mon monRange day dayRange hour hourRange min minRange sec secRange refl) z≡ bs≡) (Generic.mkGenTimeFields year₁ yearRange₁ (Generic.mkMDHMSFields mon₁ monRange₁ day₁ dayRange₁ hour₁ hourRange₁ min₁ minRange₁ sec₁ secRange₁ refl) z≡₁ bs≡₁)
    with Lemmas.length-++-≡ xs₁ _ xs₂ _ x (trans₀ (cong length bs≡) (cong length (sym bs≡₁)))
  ... | fst , snd = fst

  postulate
    @0 unambiguous : Unambiguous Generic.GenTimeFields

@0 nonnesting : NonNesting Generic.Time
nonnesting x (Generic.utctm x₁) (Generic.utctm x₂) = ‼ TLVprops.nonnesting x x₁ x₂
nonnesting x (Generic.utctm x₁) (Generic.gentm x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (Generic.gentm x₁) (Generic.utctm x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (Generic.gentm x₁) (Generic.gentm x₂) = ‼ TLVprops.nonnesting x x₁ x₂

@0 unambiguous : Unambiguous Generic.Time
unambiguous (Generic.utctm x) (Generic.utctm x₁) = cong Generic.utctm $ TLVprops.unambiguous UTC.unambiguous x x₁
unambiguous (Generic.utctm x) (Generic.gentm x₁) = ⊥-elim (TLVprops.noconfusion (λ ()) (cong (_++ []) refl) x x₁)
unambiguous (Generic.gentm x) (Generic.utctm x₁) = ⊥-elim (TLVprops.noconfusion (λ ()) (cong (_++ []) refl) x x₁)
unambiguous (Generic.gentm x) (Generic.gentm x₁) = cong Generic.gentm $ TLVprops.unambiguous GenTime.unambiguous x x₁
