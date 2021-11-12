{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Properties.TLV as TLVprops
import Aeres.Data.X509.Properties.OctetstringValue as OctetstringValueProps
import Aeres.Grammar.Sum
open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.DirectoryString where

open Base256
open import Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Sum Dig

nonnesting : NonNesting X509.DirectoryString
nonnesting x (X509.teletexString x₁) (X509.teletexString x₂) = ‼ TLVprops.nonnesting x x₁ x₂
nonnesting x (X509.teletexString x₁) (X509.printableString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.teletexString x₁) (X509.universalString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.teletexString x₁) (X509.utf8String x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.teletexString x₁) (X509.bmpString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.teletexString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.printableString x₂) = ‼ TLVprops.nonnesting x x₁ x₂
nonnesting x (X509.printableString x₁) (X509.universalString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.utf8String x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.bmpString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.teletexString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.printableString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.universalString x₂) = ‼ TLVprops.nonnesting x x₁ x₂
nonnesting x (X509.universalString x₁) (X509.utf8String x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.bmpString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.teletexString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.printableString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.universalString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.utf8String x₂) = ‼ TLVprops.nonnesting x x₁ x₂
nonnesting x (X509.utf8String x₁) (X509.bmpString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.teletexString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.printableString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.universalString x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.utf8String x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.bmpString x₂) = ‼ TLVprops.nonnesting x x₁ x₂

@0 noconfusion₁ : NoConfusion X509.TeletexString (Sum X509.PrintableString (Sum X509.UniversalString (Sum X509.UTF8String X509.BMPString)))
noconfusion₁ x x₁ (Aeres.Grammar.Sum.inj₁ x₂) = TLVprops.noconfusion (λ ()) x x₁ x₂
noconfusion₁ x x₁ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x₂)) = TLVprops.noconfusion (λ ()) x x₁ x₂
noconfusion₁ x x₁ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x₂))) = TLVprops.noconfusion (λ ()) x x₁ x₂
noconfusion₁ x x₁ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ x₂))) = TLVprops.noconfusion (λ ()) x x₁ x₂

@0 noconfusion₂ : NoConfusion X509.PrintableString (Sum X509.UniversalString (Sum X509.UTF8String X509.BMPString))
noconfusion₂ x x₁ (Aeres.Grammar.Sum.inj₁ x₂) = TLVprops.noconfusion (λ ()) x x₁ x₂
noconfusion₂ x x₁ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x₂)) =  TLVprops.noconfusion (λ ()) x x₁ x₂
noconfusion₂ x x₁ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ x₂)) =  TLVprops.noconfusion (λ ()) x x₁ x₂

@0 noconfusion₃ : NoConfusion X509.UniversalString (Sum X509.UTF8String X509.BMPString)
noconfusion₃ x x₁ (Aeres.Grammar.Sum.inj₁ x₂) = TLVprops.noconfusion (λ ()) x x₁ x₂
noconfusion₃ x x₁ (Aeres.Grammar.Sum.inj₂ x₂) = TLVprops.noconfusion (λ ()) x x₁ x₂


@0 iso : Iso (Sum X509.TeletexString (Sum X509.PrintableString (Sum X509.UniversalString
   (Sum X509.UTF8String X509.BMPString)))) X509.DirectoryString
proj₁ (proj₁ iso) (Aeres.Grammar.Sum.inj₁ x) = X509.teletexString x
proj₁ (proj₁ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x)) = X509.printableString x
proj₁ (proj₁ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x))) = X509.universalString x
proj₁ (proj₁ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x)))) = X509.utf8String x
proj₁ (proj₁ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ x)))) = X509.bmpString x
proj₂ (proj₁ iso) (X509.teletexString x) = Aeres.Grammar.Sum.inj₁ x
proj₂ (proj₁ iso) (X509.printableString x) = Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x)
proj₂ (proj₁ iso) (X509.universalString x) = Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x))
proj₂ (proj₁ iso) (X509.utf8String x) = Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x)))
proj₂ (proj₁ iso) (X509.bmpString x) = Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ x)))
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x))) = refl
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x)))) = refl
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ x)))) = refl
proj₂ (proj₂ iso) (X509.teletexString x) = refl
proj₂ (proj₂ iso) (X509.printableString x) = refl
proj₂ (proj₂ iso) (X509.universalString x) = refl
proj₂ (proj₂ iso) (X509.utf8String x) = refl
proj₂ (proj₂ iso) (X509.bmpString x) = refl


@0 unambiguous : Unambiguous X509.DirectoryString
unambiguous = isoUnambiguous iso (unambiguousSum (TLVprops.unambiguous OctetstringValueProps.unambiguous)
  (unambiguousSum (TLVprops.unambiguous OctetstringValueProps.unambiguous) (unambiguousSum (TLVprops.unambiguous OctetstringValueProps.unambiguous)
    (unambiguousSum (TLVprops.unambiguous OctetstringValueProps.unambiguous) (TLVprops.unambiguous OctetstringValueProps.unambiguous)
     (TLVprops.noconfusion (λ ()))) noconfusion₃) noconfusion₂) noconfusion₁)
