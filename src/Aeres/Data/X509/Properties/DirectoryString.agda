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
nonnesting x (X509.teletexString x₁) (X509.teletexString x₂)      = ‼ (nonnestingΣₚ₁ TLVprops.nonnesting x x₁ x₂)
nonnesting x (X509.teletexString x₁) (X509.printableString x₂)    = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.teletexString x₁) (X509.universalString x₂)    = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.teletexString x₁) (X509.utf8String x₂)         = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.teletexString x₁) (X509.bmpString x₂)          = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.teletexString x₂)    = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.printableString x₂)  = ‼ (nonnestingΣₚ₁ TLVprops.nonnesting x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.universalString x₂)  = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.utf8String x₂)       = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.printableString x₁) (X509.bmpString x₂)        = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.teletexString x₂)    = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.printableString x₂)  = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.universalString x₂)  = ‼ (nonnestingΣₚ₁ TLVprops.nonnesting x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.utf8String x₂)       = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.universalString x₁) (X509.bmpString x₂)        = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.teletexString x₂)         = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.printableString x₂)       = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.universalString x₂)       = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.utf8String x₂)            = ‼ (nonnestingΣₚ₁ TLVprops.nonnesting x x₁ x₂)
nonnesting x (X509.utf8String x₁) (X509.bmpString x₂)             = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.teletexString x₂)          = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.printableString x₂)        = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.universalString x₂)        = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.utf8String x₂)             = ⊥-elim (noconfusionΣₚ (TLVprops.noconfusion λ ()) x x₁ x₂)
nonnesting x (X509.bmpString x₁) (X509.bmpString x₂)              = ‼ (nonnestingΣₚ₁ TLVprops.nonnesting x x₁ x₂)

@0 noconfusion₁ : NoConfusion (Σₚ X509.TeletexString Generic.NonEmptyVal)
                    (Sum (Σₚ X509.PrintableString Generic.NonEmptyVal)
                    (Sum (Σₚ X509.UniversalString Generic.NonEmptyVal)
                    (Sum (Σₚ X509.UTF8String Generic.NonEmptyVal)
                         (Σₚ X509.BMPString Generic.NonEmptyVal))))
noconfusion₁ x x₁ (Sum.inj₁ x₂) = noconfusionΣₚ (TLVprops.noconfusion (λ ())) x x₁ x₂
noconfusion₁ x x₁ (Sum.inj₂ (Sum.inj₁ x₂)) = noconfusionΣₚ (TLVprops.noconfusion (λ ())) x x₁ x₂
noconfusion₁ x x₁ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x₂))) = noconfusionΣₚ (TLVprops.noconfusion (λ ())) x x₁ x₂
noconfusion₁ x x₁ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x₂))) = noconfusionΣₚ (TLVprops.noconfusion (λ ())) x x₁ x₂

@0 noconfusion₂ : NoConfusion (Σₚ X509.PrintableString Generic.NonEmptyVal)
                              (Sum (Σₚ X509.UniversalString Generic.NonEmptyVal)
                              (Sum (Σₚ X509.UTF8String      Generic.NonEmptyVal)
                                   (Σₚ X509.BMPString       Generic.NonEmptyVal)))
noconfusion₂ x x₁ (Sum.inj₁ x₂) = noconfusionΣₚ (TLVprops.noconfusion (λ ())) x x₁ x₂
noconfusion₂ x x₁ (Sum.inj₂ (Sum.inj₁ x₂)) =  noconfusionΣₚ (TLVprops.noconfusion (λ ())) x x₁ x₂
noconfusion₂ x x₁ (Sum.inj₂ (Sum.inj₂ x₂)) =  noconfusionΣₚ (TLVprops.noconfusion (λ ())) x x₁ x₂

@0 noconfusion₃ : NoConfusion (Σₚ X509.UniversalString Generic.NonEmptyVal) (Sum (Σₚ X509.UTF8String Generic.NonEmptyVal) (Σₚ X509.BMPString Generic.NonEmptyVal))
noconfusion₃ x x₁ (Sum.inj₁ x₂) = noconfusionΣₚ (TLVprops.noconfusion (λ ())) x x₁ x₂
noconfusion₃ x x₁ (Sum.inj₂ x₂) = noconfusionΣₚ (TLVprops.noconfusion (λ ())) x x₁ x₂


@0 iso :
         Iso (Sum (Σₚ X509.TeletexString   Generic.NonEmptyVal)
             (Sum (Σₚ X509.PrintableString Generic.NonEmptyVal)
             (Sum (Σₚ X509.UniversalString Generic.NonEmptyVal)
             (Sum (Σₚ X509.UTF8String      Generic.NonEmptyVal)
                  (Σₚ X509.BMPString       Generic.NonEmptyVal)))))
             X509.DirectoryString
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
unambiguous =
  isoUnambiguous iso
    (unambiguousSum
      (TLVprops.NonEmptyVal.unambiguous OctetstringValueProps.unambiguous)
      (unambiguousSum
        (TLVprops.NonEmptyVal.unambiguous OctetstringValueProps.unambiguous)
        (unambiguousSum (TLVprops.NonEmptyVal.unambiguous OctetstringValueProps.unambiguous)
          (unambiguousSum (TLVprops.NonEmptyVal.unambiguous OctetstringValueProps.unambiguous)
            (TLVprops.NonEmptyVal.unambiguous OctetstringValueProps.unambiguous)
            (noconfusionΣₚ (TLVprops.noconfusion λ ())))
          noconfusion₃)
        noconfusion₂)
      noconfusion₁)
