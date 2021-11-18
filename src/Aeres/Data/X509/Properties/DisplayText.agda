{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.TLV as TLVprops
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Data.List
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.DisplayText where
open ≡-Reasoning

open Base256
open Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Properties  Dig
open Aeres.Grammar.Sum         Dig

postulate
  equivalent : Equivalent
                 (Sum X509.IA5String
                 (Sum X509.VisibleString
                 (Sum X509.BMPString
                      X509.UTF8String)))
                 X509.DisplayText

postulate
  @0 nonempty : NonEmpty X509.DisplayText

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



@0 noconfusionTLV : ∀ {t} {@0 A} → t ∉ Tag.IA5String ∷ Tag.VisibleString ∷ Tag.BMPString ∷ [ Tag.UTF8String ]
                      → NoConfusion (Generic.TLV t A) X509.DisplayText
noconfusionTLV {t} {A} x {xs₁} {ys₁} {xs₂} {ys₂} x₁ (Generic.mkTLV {l = l} {v = v} len val len≡ bs≡) (X509.ia5String (Generic.mkTLV {l = l₁} {v = v₁} len₁ val₁ len≡₁ bs≡₁))
               = contradiction (here (∷-injectiveˡ (‼ x'))) x
  where
  @0 x' : t ∷ l ++ v ++ ys₁ ≡ Tag.IA5String ∷ l₁ ++ v₁ ++ ys₂
  x' = begin ( t ∷ l ++ v ++ ys₁ ≡⟨ cong (t ∷_) (solve (++-monoid Dig))⟩
              (t ∷ l ++ v) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡)  ⟩
              xs₁ ++ ys₁ ≡⟨ x₁ ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
              (Tag.IA5String ∷ l₁ ++ v₁) ++ ys₂ ≡⟨ cong (Tag.IA5String ∷_) (solve (++-monoid Dig))⟩
              Tag.IA5String ∷ l₁ ++ v₁ ++ ys₂ ∎)
noconfusionTLV {t} {A} x {xs₁} {ys₁} {xs₂} {ys₂} x₁ (Generic.mkTLV {l = l} {v = v} len val len≡ bs≡) (X509.visibleString (Generic.mkTLV {l = l₁} {v = v₁} len₁ val₁ len≡₁ bs≡₁))
  = contradiction (there (here (∷-injectiveˡ (‼ x')))) x
  where
  @0 x' : t ∷ l ++ v ++ ys₁ ≡ Tag.VisibleString ∷ l₁ ++ v₁ ++ ys₂
  x' = begin ( t ∷ l ++ v ++ ys₁ ≡⟨ cong (t ∷_) (solve (++-monoid Dig))⟩
              (t ∷ l ++ v) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡)  ⟩
              xs₁ ++ ys₁ ≡⟨ x₁ ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
              (Tag.VisibleString ∷ l₁ ++ v₁) ++ ys₂ ≡⟨ cong (Tag.VisibleString ∷_) (solve (++-monoid Dig))⟩
              Tag.VisibleString ∷ l₁ ++ v₁ ++ ys₂ ∎)
noconfusionTLV {t} {A} x {xs₁} {ys₁} {xs₂} {ys₂} x₁ (Generic.mkTLV {l = l} {v = v} len val len≡ bs≡) (X509.bmpString (Generic.mkTLV {l = l₁} {v = v₁} len₁ val₁ len≡₁ bs≡₁))
  = contradiction (there (there (here (∷-injectiveˡ (‼ x'))))) x
  where
  @0 x' : t ∷ l ++ v ++ ys₁ ≡ Tag.BMPString ∷ l₁ ++ v₁ ++ ys₂
  x' = begin ( t ∷ l ++ v ++ ys₁ ≡⟨ cong (t ∷_) (solve (++-monoid Dig))⟩
              (t ∷ l ++ v) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡)  ⟩
              xs₁ ++ ys₁ ≡⟨ x₁ ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
              (Tag.BMPString ∷ l₁ ++ v₁) ++ ys₂ ≡⟨ cong (Tag.BMPString ∷_) (solve (++-monoid Dig))⟩
              Tag.BMPString ∷ l₁ ++ v₁ ++ ys₂ ∎)
noconfusionTLV {t} {A} x {xs₁} {ys₁} {xs₂} {ys₂} x₁ (Generic.mkTLV {l = l} {v = v} len val len≡ bs≡) (X509.utf8String (Generic.mkTLV {l = l₁} {v = v₁} len₁ val₁ len≡₁ bs≡₁))
  = contradiction (there (there (there (here(∷-injectiveˡ (‼ x')))))) x
  where
  @0 x' : t ∷ l ++ v ++ ys₁ ≡ Tag.UTF8String ∷ l₁ ++ v₁ ++ ys₂
  x' = begin ( t ∷ l ++ v ++ ys₁ ≡⟨ cong (t ∷_) (solve (++-monoid Dig))⟩
              (t ∷ l ++ v) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡)  ⟩
              xs₁ ++ ys₁ ≡⟨ x₁ ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
              (Tag.UTF8String ∷ l₁ ++ v₁) ++ ys₂ ≡⟨ cong (Tag.UTF8String ∷_) (solve (++-monoid Dig))⟩
              Tag.UTF8String ∷ l₁ ++ v₁ ++ ys₂ ∎)



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


postulate
  @0 unambiguous : Unambiguous X509.DisplayText
