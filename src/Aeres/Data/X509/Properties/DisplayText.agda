{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Data.UTF8
import      Aeres.Data.UTF8.Properties                  as UTF8Props
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.OctetstringValue as OSProps
open import Aeres.Prelude
open import Data.List
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.DisplayText where

open ≡-Reasoning

open Base256
open Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Properties  Dig
open Aeres.Grammar.Sum         Dig

equivalent : Equivalent
               (Sum (Σₚ IA5String     (TLVLenBounded 1 200))
               (Sum (Σₚ X509.VisibleString (TLVLenBounded 1 200))
               (Sum (Σₚ X509.BMPString     (TLVLenBounded 1 200))
                    (Σₚ X509.UTF8String    (TLVLenBounded 1 200)))))
               X509.DisplayText
proj₁ equivalent (Sum.inj₁ x) = X509.ia5String x
proj₁ equivalent (Sum.inj₂ (Sum.inj₁ x)) = X509.visibleString x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = X509.bmpString x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x))) = X509.utf8String x
proj₂ equivalent (X509.ia5String x) = inj₁ x
proj₂ equivalent (X509.visibleString x) = inj₂ (inj₁ x)
proj₂ equivalent (X509.bmpString x) = inj₂ (inj₂ (inj₁ x))
proj₂ equivalent (X509.utf8String x) = inj₂ (inj₂ (inj₂ x))

iso : Iso
        (Sum (Σₚ IA5String     (TLVLenBounded 1 200))
        (Sum (Σₚ X509.VisibleString (TLVLenBounded 1 200))
        (Sum (Σₚ X509.BMPString     (TLVLenBounded 1 200))
             (Σₚ X509.UTF8String    (TLVLenBounded 1 200)))))
        X509.DisplayText
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₁ x))) = refl
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Sum.inj₂ x))) = refl
proj₂ (proj₂ iso) (X509.ia5String x) = refl
proj₂ (proj₂ iso) (X509.visibleString x) = refl
proj₂ (proj₂ iso) (X509.bmpString x) = refl
proj₂ (proj₂ iso) (X509.utf8String x) = refl

@0 nonempty : NonEmpty X509.DisplayText
nonempty =
  equivalent-nonempty equivalent
    (nonemptySum (nonemptyΣₚ₁ TLV.nonempty)
      (nonemptySum (nonemptyΣₚ₁ TLV.nonempty)
        (nonemptySum (nonemptyΣₚ₁ TLV.nonempty)
          (nonemptyΣₚ₁ TLV.nonempty))))

@0 nonnesting : NonNesting X509.DisplayText
nonnesting =
  equivalent-nonnesting equivalent
    (nonnestingSum (nonnestingΣₚ₁ TLV.nonnesting)
      (nonnestingSum (nonnestingΣₚ₁ TLV.nonnesting)
        (nonnestingSum (nonnestingΣₚ₁ TLV.nonnesting)
          (nonnestingΣₚ₁ TLV.nonnesting)
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ())))
        (NoConfusion.sumₚ{A = Σₚ X509.VisibleString _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))))
      (NoConfusion.sumₚ{A = Σₚ IA5String _}
        (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
        (NoConfusion.sumₚ{A = Σₚ IA5String _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ())))))

@0 noconfusionTLV : ∀ {t} {@0 A} → t ∉ Tag.IA5String ∷ Tag.VisibleString ∷ Tag.BMPString ∷ [ Tag.UTF8String ]
                      → NoConfusion (TLV t A) X509.DisplayText
noconfusionTLV{t}{A} t∉ =
  symNoConfusion{A = X509.DisplayText}{B = TLV _ A}
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

@0 noconfusionSeq : ∀ {@0 A} → NoConfusion (Seq A) X509.DisplayText
noconfusionSeq = noconfusionTLV pf
  where
  pf : Tag.Sequence  ∉ _
  pf (there (there (there (there ()))))


@0 noconfusionNoticeReference : NoConfusion X509.NoticeReference X509.DisplayText
noconfusionNoticeReference = noconfusionTLV pf
  where
  pf : Tag.Sequence ∉ _
  pf (there (there (there (there ()))))

@0 unambiguous : Unambiguous X509.DisplayText
unambiguous =
  isoUnambiguous iso
    (unambiguousSum
      (unambiguousΣₚ (TLV.unambiguous IA5String.unambiguous)
        (λ _ → inRange-unique{A = ℕ}{B = ℕ}))
      (unambiguousSum
        (unambiguousΣₚ (TLV.unambiguous UTF8Props.unambiguous)
          λ _ → inRange-unique{A =  ℕ}{B = ℕ})
        (unambiguousSum
          (unambiguousΣₚ (TLV.unambiguous UTF8Props.unambiguous)
            (λ _ → inRange-unique {A = ℕ} {B = ℕ}))
          (unambiguousΣₚ (TLV.unambiguous UTF8Props.unambiguous)
            (λ _ → inRange-unique {A = ℕ} {B = ℕ}))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion (λ ()))))
        (NoConfusion.sumₚ{A = Σₚ _ _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion (λ ())))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion (λ ())))))
      (NoConfusion.sumₚ {A = Σₚ _ _}
        (NoConfusion.sigmaₚ₁ (TLV.noconfusion (λ ())))
        (NoConfusion.sumₚ{A = Σₚ _ _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ())))))
