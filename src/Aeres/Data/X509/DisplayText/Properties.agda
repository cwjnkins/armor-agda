{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Unicode.UTF8
open import Aeres.Data.Unicode.UTF16
open import Aeres.Data.X509.DisplayText.TCB
open import Aeres.Data.X690-DER.Strings
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.List
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.DisplayText.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

equivalent
  : Equivalent
      (Sum (Σₚ IA5String     (TLVSizeBounded IA5StringValue.size 1 200))
      (Sum (Σₚ VisibleString (TLVSizeBounded VisibleStringValue.size 1 200))
      (Sum (Σₚ BMPString     (TLVSizeBounded UTF16.size 1 200))
           (Σₚ UTF8String    (TLVSizeBounded UTF8.size 1 200)))))
      DisplayText
proj₁ equivalent (Sum.inj₁ x) = ia5String x
proj₁ equivalent (Sum.inj₂ (Sum.inj₁ x)) = visibleString x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = bmpString x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x))) = utf8String x
proj₂ equivalent (ia5String x) = inj₁ x
proj₂ equivalent (visibleString x) = inj₂ (inj₁ x)
proj₂ equivalent (bmpString x) = inj₂ (inj₂ (inj₁ x))
proj₂ equivalent (utf8String x) = inj₂ (inj₂ (inj₂ x))

iso
  : Iso
      (Sum (Σₚ IA5String     (TLVSizeBounded IA5StringValue.size 1 200))
      (Sum (Σₚ VisibleString (TLVSizeBounded VisibleStringValue.size 1 200))
      (Sum (Σₚ BMPString     (TLVSizeBounded UTF16.size 1 200))
           (Σₚ UTF8String    (TLVSizeBounded UTF8.size 1 200)))))
      DisplayText
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x))) = refl
proj₂ (proj₂ iso) (ia5String x) = refl
proj₂ (proj₂ iso) (visibleString x) = refl
proj₂ (proj₂ iso) (bmpString x) = refl
proj₂ (proj₂ iso) (utf8String x) = refl

@0 nonempty : NonEmpty DisplayText
nonempty =
  equivalent-nonempty equivalent
    (nonemptySum (nonemptyΣₚ₁ TLV.nonempty)
      (nonemptySum (nonemptyΣₚ₁ TLV.nonempty)
        (nonemptySum (nonemptyΣₚ₁ TLV.nonempty)
          (nonemptyΣₚ₁ TLV.nonempty))))

@0 nonnesting : NonNesting DisplayText
nonnesting =
  equivalent-nonnesting equivalent
    (nonnestingSum (nonnestingΣₚ₁ TLV.nonnesting)
      (nonnestingSum (nonnestingΣₚ₁ TLV.nonnesting)
        (nonnestingSum (nonnestingΣₚ₁ TLV.nonnesting)
          (nonnestingΣₚ₁ TLV.nonnesting)
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ())))
        (NoConfusion.sumₚ{A = Σₚ VisibleString _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))))
      (NoConfusion.sumₚ{A = Σₚ IA5String _}
        (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
        (NoConfusion.sumₚ{A = Σₚ IA5String _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ())))))

@0 noconfusionTLV
  : ∀ {t} {@0 A} → t ∉ Tag.IA5String ∷ Tag.VisibleString ∷ Tag.BMPString ∷ [ Tag.UTF8String ]
    → NoConfusion (TLV t A) DisplayText
noconfusionTLV{t}{A} t∉ =
  symNoConfusion{A = DisplayText}{B = TLV _ A}
    (NoConfusion.equivalent{B = TLV _ A} equivalent
      (symNoConfusion{A = TLV _ A}{B = Sum _ _}
        (NoConfusion.sumₚ{A = TLV _ A}
          (NoConfusion.sigmaₚ₁ᵣ{A₁ = TLV _ A}
            (TLV.noconfusion (λ where refl → t∉ (here refl))))
          (NoConfusion.sumₚ{A = TLV t A}
            (NoConfusion.sigmaₚ₁ᵣ{A₁ = TLV t A}
              (TLV.noconfusion (λ where refl → t∉ (there (here refl)))))
            (NoConfusion.sumₚ{A = TLV t A}
              (NoConfusion.sigmaₚ₁ᵣ{A₁ = TLV t A}
                (TLV.noconfusion (λ where refl → t∉ (there (there (here refl))))))
              (NoConfusion.sigmaₚ₁ᵣ{A₁ = TLV t A}
                (TLV.noconfusion λ where refl → t∉ (there (there (there (here refl)))))))))))

@0 noconfusionSeq : ∀ {@0 A} → NoConfusion (Seq A) DisplayText
noconfusionSeq = noconfusionTLV pf
  where
  pf : Tag.Sequence  ∉ _
  pf (there (there (there (there ()))))

-- @0 noconfusionNoticeReference : NoConfusion X509.NoticeReference DisplayText
-- noconfusionNoticeReference = noconfusionTLV pf
--   where
--   pf : Tag.Sequence ∉ _
--   pf (there (there (there (there ()))))

@0 unambiguous : Unambiguous DisplayText
unambiguous =
  isoUnambiguous iso
    (unambiguousSum
      (unambiguousΣₚ (TLV.unambiguous IA5String.unambiguous) λ _ → inRange-unique{A = ℕ}{B = ℕ})
      (unambiguousSum (unambiguousΣₚ (TLV.unambiguous VisibleString.unambiguous) (λ _ → inRange-unique{A = ℕ}{B = ℕ}))
        (unambiguousSum
          (unambiguousΣₚ
            (TLV.unambiguous (IList.unambiguous UTF16.BMP.unambiguous UTF16.BMP.nonempty UTF16.BMP.nonnesting))
            λ _ → inRange-unique{A = ℕ}{B = ℕ})
          (unambiguousΣₚ (TLV.unambiguous UTF8.unambiguous) (λ _ → inRange-unique{A = ℕ}{B = ℕ}))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ())))
        (NoConfusion.sumₚ{A = Σₚ _ _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))))
      (NoConfusion.sumₚ {A = Σₚ _ _}
        (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
        (NoConfusion.sumₚ {A = Σₚ _ _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ())))))
  where
  open import Aeres.Grammar.IList UInt8



instance
  DisplayTextEq : Eq (Exists─ _ DisplayText)
  DisplayTextEq =
    isoEq iso
      (sumEq ⦃ eqΣₚ it λ a → record { _≟_ = λ x y → yes (inRange-unique{A = ℕ}{B = ℕ} x y) } ⦄
        ⦃ sumEq ⦃ eqΣₚ it λ a → record { _≟_ = λ x y → yes (inRange-unique{A = ℕ}{B = ℕ} x y) } ⦄
            ⦃ sumEq ⦃ eqΣₚ it λ a → record { _≟_ = λ x y → yes (inRange-unique{A = ℕ}{B = ℕ} x y) } ⦄
                ⦃ eqΣₚ (TLV.eqTLV ⦃ UTF8.UTF8Eq ⦄) λ a → record { _≟_ = λ x y → yes (inRange-unique{A = ℕ}{B = ℕ} x y) } ⦄  ⦄ ⦄)

  eq≋ : Eq≋ DisplayText
  eq≋ = Eq⇒Eq≋ it

postulate
  @0 nonmalleable : NonMalleable DisplayText RawDisplayText
