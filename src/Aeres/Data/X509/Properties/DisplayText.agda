{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Properties.TLV as TLVprops
open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.DisplayText where

open Base256
open import Aeres.Grammar.Definitions Dig

nonnesting : NonNesting X509.DisplayText
nonnesting x (X509.ia5String x₁) (X509.ia5String x₂) = ‼ TLVprops.nonnesting x x₁ x₂
nonnesting x (X509.ia5String x₁) (X509.visibleString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ia5String x₁) (X509.bmpString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ia5String x₁) (X509.utf8String x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.visibleString x₁) (X509.ia5String x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.visibleString x₁) (X509.visibleString x₂) = ‼ TLVprops.nonnesting x x₁ x₂
nonnesting x (X509.visibleString x₁) (X509.bmpString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.visibleString x₁) (X509.utf8String x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.ia5String x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.visibleString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.bmpString x₂) = ‼ TLVprops.nonnesting x x₁ x₂
nonnesting x (X509.bmpString x₁) (X509.utf8String x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.ia5String x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.visibleString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.bmpString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.utf8String x₂) = ‼ TLVprops.nonnesting x x₁ x₂

postulate
  @0 noconfusionTLV : ∀ {t} {@0 A} → t ∉ Tag.IA5String ∷ Tag.PrintableString ∷ Tag.UniversalString ∷ Tag.UTF8String ∷ [ Tag.BMPString ]
                      → NoConfusion (Generic.TLV t A) X509.DisplayText

@0 noconfusionNoticeReference : NoConfusion X509.NoticeReference X509.DisplayText
noconfusionNoticeReference = noconfusionTLV pf
  where
  pf : Tag.Sequence ∉ _
  pf (there (there (there (there (there ())))))
