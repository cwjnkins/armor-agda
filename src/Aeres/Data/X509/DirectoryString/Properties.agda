{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Sum
open import Aeres.Data.Unicode
open import Aeres.Data.X690-DER.Strings.IA5String
open import Aeres.Data.X690-DER.Strings.PrintableString
open import Aeres.Data.X509.DirectoryString.TCB
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.DirectoryString.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Sum                UInt8

nonnesting : NonNesting DirectoryString
nonnesting x (teletexString x₁) (teletexString x₂)      = ‼ (nonnestingΣₚ₁ TLV.nonnesting x x₁ x₂)
nonnesting x (teletexString x₁) (printableString x₂)    = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (teletexString x₁) (universalString x₂)    = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (teletexString x₁) (utf8String x₂)         = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (teletexString x₁) (bmpString x₂)          = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (printableString x₁) (teletexString x₂)    = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (printableString x₁) (printableString x₂)  = ‼ (nonnestingΣₚ₁ TLV.nonnesting x x₁ x₂)
nonnesting x (printableString x₁) (universalString x₂)  = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (printableString x₁) (utf8String x₂)       = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (printableString x₁) (bmpString x₂)        = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (universalString x₁) (teletexString x₂)    = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (universalString x₁) (printableString x₂)  = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (universalString x₁) (universalString x₂)  = ‼ (nonnestingΣₚ₁ TLV.nonnesting x x₁ x₂)
nonnesting x (universalString x₁) (utf8String x₂)       = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (universalString x₁) (bmpString x₂)        = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (utf8String x₁) (teletexString x₂)         = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (utf8String x₁) (printableString x₂)       = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (utf8String x₁) (universalString x₂)       = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (utf8String x₁) (utf8String x₂)            = ‼ (nonnestingΣₚ₁ TLV.nonnesting x x₁ x₂)
nonnesting x (utf8String x₁) (bmpString x₂)             = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (bmpString x₁) (teletexString x₂)          = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (bmpString x₁) (printableString x₂)        = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (bmpString x₁) (universalString x₂)        = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (bmpString x₁) (utf8String x₂)             = ⊥-elim (noconfusionΣₚ (TLV.noconfusion λ ()) x x₁ x₂)
nonnesting x (bmpString x₁) (bmpString x₂)              = ‼ (nonnestingΣₚ₁ TLV.nonnesting x x₁ x₂)

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

iso : Iso DirectoryStringRep DirectoryString
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))) = refl
proj₂ (proj₂ iso) (teletexString x) = refl
proj₂ (proj₂ iso) (printableString x) = refl
proj₂ (proj₂ iso) (universalString x) = refl
proj₂ (proj₂ iso) (utf8String x) = refl
proj₂ (proj₂ iso) (bmpString x) = refl

@0 nonmalleable : NonMalleable DirectoryString RawDirectoryString
nonmalleable =
  Iso.nonmalleable iso RawDirectoryStringRep nm
  where
  -- @0 unambiguousRep : Unambiguous Rep
  -- unambiguousRep =
  --   (unambiguousSum (TLV.NonEmptyVal.unambiguous OctetString.unambiguous)
  --     (unambiguousSum
  --       (TLV.NonEmptyVal.unambiguous
  --         (IList.unambiguous
  --           PrintableString.Char.unambiguous
  --           PrintableString.Char.nonempty
  --           PrintableString.Char.nonnesting))
  --       (unambiguousSum (TLV.NonEmptyVal.unambiguous UTF32.unambiguous)
  --         (unambiguousSum (TLV.NonEmptyVal.unambiguous UTF8.unambiguous)
  --           (TLV.NonEmptyVal.unambiguous
  --             (IList.unambiguous
  --               UTF16.BMP.unambiguous UTF16.BMP.nonempty UTF16.BMP.nonnesting))
  --           (noconfusionΣₚ (TLV.noconfusion λ ())))
  --         noconfusion₃)
  --       noconfusion₂)
  --     noconfusion₁)
  postulate
    nmTele : NonMalleable (Σₚ TeletexString TLVNonEmptyVal) (RawΣₚ₁ RawTeletexString TLVNonEmptyVal)
    nmPrin : NonMalleable (Σₚ PrintableString TLVNonEmptyVal) (RawΣₚ₁ RawPrintableString TLVNonEmptyVal)
    nmUniv : NonMalleable (Σₚ UniversalString TLVNonEmptyVal) (RawΣₚ₁ RawUniversalString TLVNonEmptyVal)
    nmUTF8 : NonMalleable (Σₚ UTF8String TLVNonEmptyVal) (RawΣₚ₁ RawUTF8String TLVNonEmptyVal)
    nmBMPS : NonMalleable (Σₚ BMPString TLVNonEmptyVal) (RawΣₚ₁ RawBMPString TLVNonEmptyVal)

  nm : NonMalleable DirectoryStringRep RawDirectoryStringRep
  nm =
    nonmalleableSum nmTele
      (nonmalleableSum nmPrin
        (nonmalleableSum nmUniv
          (nonmalleableSum nmUTF8 nmBMPS
            (noconfusionΣₚ (TLV.noconfusion λ ())))
          noconfusion₃)
        noconfusion₂)
      noconfusion₁
 
@0 unambiguous : Unambiguous DirectoryString
unambiguous = NonMalleable.unambiguous nonmalleable
