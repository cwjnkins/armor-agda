{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Sum
open import Aeres.Data.UTF8
import      Aeres.Data.UTF8.Properties                  as UTF8Props
open import Aeres.Data.X509
open import Aeres.Data.X690-DER
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.DirectoryString where

open Base256
open import Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Sum Dig

nonnesting : NonNesting X509.DirectoryString
nonnesting x (X509.teletexString x₁) (X509.teletexString x₂)      = ‼ (nonnestingΣₚ₁ TLV.nonnesting x x₁ x₂)
nonnesting x (X509.teletexString x₁) (X509.printableString x₂)    = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.teletexString x₁) (X509.universalString x₂)    = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.teletexString x₁) (X509.utf8String x₂)         = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.teletexString x₁) (X509.bmpString x₂)          = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.teletexString x₂)    = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.printableString x₂)  = ‼ (nonnestingΣₚ₁ TLV.nonnesting x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.universalString x₂)  = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.utf8String x₂)       = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.bmpString x₂)        = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.teletexString x₂)    = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.printableString x₂)  = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.universalString x₂)  = ‼ (nonnestingΣₚ₁ TLV.nonnesting x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.utf8String x₂)       = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.bmpString x₂)        = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.teletexString x₂)         = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.printableString x₂)       = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.universalString x₂)       = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.utf8String x₂)            = ‼ (nonnestingΣₚ₁ TLV.nonnesting x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.bmpString x₂)             = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.teletexString x₂)          = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.printableString x₂)        = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.universalString x₂)        = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.utf8String x₂)             = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.bmpString x₂)              = ‼ (nonnestingΣₚ₁ TLV.nonnesting x x₁ x₂)

@0 noconfusion₁ : NoConfusion (Σₚ TeletexString TLVNonEmptyVal)
                    (Sum (Σₚ PrintableString TLVNonEmptyVal)
                    (Sum (Σₚ UniversalString TLVNonEmptyVal)
                    (Sum (Σₚ UTF8String TLVNonEmptyVal)
                         (Σₚ BMPString TLVNonEmptyVal))))
noconfusion₁ x x₁ (Sum.inj₁ x₂) = noconfusionΣₚ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₁ x x₁ (Sum.inj₂ (Sum.inj₁ x₂)) = noconfusionΣₚ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₁ x x₁ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x₂))) = noconfusionΣₚ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₁ x x₁ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x₂))) = noconfusionΣₚ (TLV.noconfusion (λ ())) x x₁ x₂

@0 noconfusion₂ : NoConfusion (Σₚ PrintableString TLVNonEmptyVal)
                              (Sum (Σₚ UniversalString TLVNonEmptyVal)
                              (Sum (Σₚ UTF8String      TLVNonEmptyVal)
                                   (Σₚ BMPString       TLVNonEmptyVal)))
noconfusion₂ x x₁ (Sum.inj₁ x₂) = noconfusionΣₚ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₂ x x₁ (Sum.inj₂ (Sum.inj₁ x₂)) =  noconfusionΣₚ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₂ x x₁ (Sum.inj₂ (Sum.inj₂ x₂)) =  noconfusionΣₚ (TLV.noconfusion (λ ())) x x₁ x₂

@0 noconfusion₃ : NoConfusion (Σₚ UniversalString TLVNonEmptyVal) (Sum (Σₚ UTF8String TLVNonEmptyVal) (Σₚ BMPString TLVNonEmptyVal))
noconfusion₃ x x₁ (Sum.inj₁ x₂) = noconfusionΣₚ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₃ x x₁ (Sum.inj₂ x₂) = noconfusionΣₚ (TLV.noconfusion (λ ())) x x₁ x₂


@0 iso :
         Iso (Sum (Σₚ TeletexString   TLVNonEmptyVal)
             (Sum (Σₚ PrintableString TLVNonEmptyVal)
             (Sum (Σₚ UniversalString TLVNonEmptyVal)
             (Sum (Σₚ UTF8String      TLVNonEmptyVal)
                  (Σₚ BMPString       TLVNonEmptyVal)))))
             X509.DirectoryString
proj₁ (proj₁ iso) (Sum.inj₁ x) = X509.teletexString x
proj₁ (proj₁ iso) (Sum.inj₂ (Sum.inj₁ x)) = X509.printableString x
proj₁ (proj₁ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = X509.universalString x
proj₁ (proj₁ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = X509.utf8String x
proj₁ (proj₁ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))) = X509.bmpString x
proj₂ (proj₁ iso) (X509.teletexString x) = Sum.inj₁ x
proj₂ (proj₁ iso) (X509.printableString x) = Sum.inj₂ (Sum.inj₁ x)
proj₂ (proj₁ iso) (X509.universalString x) = Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))
proj₂ (proj₁ iso) (X509.utf8String x) = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))
proj₂ (proj₁ iso) (X509.bmpString x) = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))) = refl
proj₂ (proj₂ iso) (X509.teletexString x) = refl
proj₂ (proj₂ iso) (X509.printableString x) = refl
proj₂ (proj₂ iso) (X509.universalString x) = refl
proj₂ (proj₂ iso) (X509.utf8String x) = refl
proj₂ (proj₂ iso) (X509.bmpString x) = refl


@0 unambiguous : Unambiguous X509.DirectoryString
unambiguous =
  isoUnambiguous iso
    (unambiguousSum (TLV.NonEmptyVal.unambiguous OctetString.unambiguous)
      (unambiguousSum (TLV.NonEmptyVal.unambiguous IA5String.unambiguous)
        (unambiguousSum (TLV.NonEmptyVal.unambiguous UTF8Props.unambiguous)
          (unambiguousSum (TLV.NonEmptyVal.unambiguous UTF8Props.unambiguous)
            (TLV.NonEmptyVal.unambiguous UTF8Props.unambiguous)
              (noconfusionΣₚ (TLV.noconfusion λ ())))
          noconfusion₃)
        noconfusion₂)
      noconfusion₁)
