{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.IA5StringValue   as IA5Props
import      Aeres.Data.X509.Properties.OctetstringValue as OSProps
import      Aeres.Data.X509.Properties.TLV              as TLVProps
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
               (Sum (Σₚ X509.IA5String     (Generic.LenBounded 1 200))
               (Sum (Σₚ X509.VisibleString (Generic.LenBounded 1 200))
               (Sum (Σₚ X509.BMPString     (Generic.LenBounded 1 200))
                    (Σₚ X509.UTF8String    (Generic.LenBounded 1 200)))))
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
        (Sum (Σₚ X509.IA5String     (Generic.LenBounded 1 200))
        (Sum (Σₚ X509.VisibleString (Generic.LenBounded 1 200))
        (Sum (Σₚ X509.BMPString     (Generic.LenBounded 1 200))
             (Σₚ X509.UTF8String    (Generic.LenBounded 1 200)))))
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
    (nonemptySum (nonemptyΣₚ₁ TLVProps.nonempty)
      (nonemptySum (nonemptyΣₚ₁ TLVProps.nonempty)
        (nonemptySum (nonemptyΣₚ₁ TLVProps.nonempty)
          (nonemptyΣₚ₁ TLVProps.nonempty))))

@0 nonnesting : NonNesting X509.DisplayText
nonnesting =
  equivalent-nonnesting equivalent
    (nonnestingSum (nonnestingΣₚ₁ TLVProps.nonnesting)
      (nonnestingSum (nonnestingΣₚ₁ TLVProps.nonnesting)
        (nonnestingSum (nonnestingΣₚ₁ TLVProps.nonnesting)
          (nonnestingΣₚ₁ TLVProps.nonnesting)
          (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ())))
        (NoConfusion.sumₚ{A = Σₚ X509.VisibleString _}
          (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ()))))
      (NoConfusion.sumₚ{A = Σₚ X509.IA5String _}
        (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ()))
        (NoConfusion.sumₚ{A = Σₚ X509.IA5String _}
          (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ())))))

@0 noconfusionTLV : ∀ {t} {@0 A} → t ∉ Tag.IA5String ∷ Tag.VisibleString ∷ Tag.BMPString ∷ [ Tag.UTF8String ]
                      → NoConfusion (Generic.TLV t A) X509.DisplayText
noconfusionTLV{t}{A} t∉ =
  symNoConfusion{A = X509.DisplayText}{B = Generic.TLV _ A}
    (NoConfusion.equivalent{B = Generic.TLV _ A} equivalent
      (symNoConfusion{A = Generic.TLV _ A}{B = Sum _ _}
        (NoConfusion.sumₚ{A = Generic.TLV _ A}
          (NoConfusion.sigmaₚ₁ᵣ{A₁ = Generic.TLV _ A}
            (TLVProps.noconfusion (λ where refl → t∉ (here refl))))
          (NoConfusion.sumₚ{A = Generic.TLV t A}
            (NoConfusion.sigmaₚ₁ᵣ{A₁ = Generic.TLV t A}
              (TLVProps.noconfusion (λ where refl → t∉ (there (here refl)))))
            (NoConfusion.sumₚ{A = Generic.TLV t A}
              (NoConfusion.sigmaₚ₁ᵣ{A₁ = Generic.TLV t A}
                (TLVProps.noconfusion (λ where refl → t∉ (there (there (here refl))))))
              (NoConfusion.sigmaₚ₁ᵣ{A₁ = Generic.TLV t A}
                (TLVProps.noconfusion λ where refl → t∉ (there (there (there (here refl)))))))))))

@0 noconfusionSeq : ∀ {@0 A} → NoConfusion (Generic.Seq A) X509.DisplayText
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
      (unambiguousΣₚ (TLVProps.unambiguous IA5Props.unambiguous)
        (λ _ → inRange-unique{A = ℕ}{B = ℕ}))
      (unambiguousSum
        (unambiguousΣₚ (TLVProps.unambiguous OSProps.unambiguous)
          (λ _ → inRange-unique{A = ℕ}{B = ℕ}))
        (unambiguousSum
          (unambiguousΣₚ (TLVProps.unambiguous OSProps.unambiguous)
            (λ _ → inRange-unique{A = ℕ}{B = ℕ}))
          (unambiguousΣₚ (TLVProps.unambiguous OSProps.unambiguous)
            (λ _ → inRange-unique{A = ℕ}{B = ℕ}))
          (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ())))
        (NoConfusion.sumₚ{A = Σₚ X509.VisibleString _}
          (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ()))))
      (NoConfusion.sumₚ{A = Σₚ X509.IA5String _}
        (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ()))
        (NoConfusion.sumₚ{A = Σₚ X509.IA5String _}
          (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLVProps.noconfusion λ ())))))
