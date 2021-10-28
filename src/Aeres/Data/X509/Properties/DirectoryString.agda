{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Properties.TLV as TLVprops
open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.DirectoryString where

open Base256
open import Aeres.Grammar.Definitions Dig

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
