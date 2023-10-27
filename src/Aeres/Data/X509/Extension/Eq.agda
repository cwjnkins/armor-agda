{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA
open import Aeres.Data.X509.Extension.AKI
open import Aeres.Data.X509.Extension.BC
open import Aeres.Data.X509.Extension.CRLDistPoint
open import Aeres.Data.X509.Extension.CertPolicy
open import Aeres.Data.X509.Extension.EKU
open import Aeres.Data.X509.Extension.IAN
open import Aeres.Data.X509.Extension.INAP
open import Aeres.Data.X509.Extension.KU
open import Aeres.Data.X509.Extension.NC
open import Aeres.Data.X509.Extension.PC
open import Aeres.Data.X509.Extension.PM
open import Aeres.Data.X509.Extension.SAN
open import Aeres.Data.X509.Extension.SKI
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.Properties
open import Aeres.Data.X509.Extension.TCB
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X509.GeneralNames.GeneralName
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.Boool
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Extension.Eq where

open ≡-Reasoning

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8
open Aeres.Grammar.Sum         UInt8

postulate
  eq≋Field : ∀ {@0 P} {@0 A} → (∀ {@0 bs} → Unique (P bs)) → ⦃ _ : Eq≋ A ⦄ → Eq≋ (ExtensionFields P A)
-- eq≋Field eqP =
--   Iso.isoEq≋ Fields.iso
--     (Seq.eq≋&ₚ
--       (Parallel.eq≋Σₚ it λ _ →
--         record
--           { _≟_ = λ x y → yes (erased-unique eqP x y)
--           })
--       (Seq.eq≋&ₚ it it))

instance
  eq≋ : Eq≋ SelectExtn
  eq≋ =
    Iso.isoEq≋ Select.iso
             (Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ {@0 xs} a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field (λ a b → ‼ ≡-unique a b) ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b  ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b  ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = eq≋Field (λ p₁ p₂ → ‼ T-unique p₁ p₂) ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄)
    where
    instance
      e₁ : Eq≋ (NonEmptySequenceOf OID)
      e₁ = SequenceOf.BoundedSequenceOfEq≋

      e₂ : Eq≋ (NonEmptySequenceOf CertPolicy.PolicyInformation)
      e₂ = SequenceOf.BoundedSequenceOfEq≋

      e₃ : Eq≋ (NonEmptySequenceOf CRLDistPoint.DistPoint)
      e₃ = SequenceOf.BoundedSequenceOfEq≋

      e₄ : Eq≋ (NonEmptySequenceOf PolicyMap)
      e₄ = SequenceOf.BoundedSequenceOfEq≋

      e₅ : Eq≋ (NonEmptySequenceOf AIA.AccessDesc)
      e₅ = SequenceOf.BoundedSequenceOfEq≋
