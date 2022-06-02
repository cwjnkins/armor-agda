{-# OPTIONS --subtyping #-}


open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.IA5StringValue   as IA5Props
import      Aeres.Data.X509.Properties.TLV              as TLVProps
import      Aeres.Data.X509.Properties.UserNoticeFields as UserNoticeProps
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.PolicyQualifierInfoFields where
open ≡-Reasoning

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum         Dig

module CPSURIQualifier where

  equivalent : Equivalent (&ₚ (_≡ X509.PQOID.CPSURI) X509.IA5String) X509.CPSURIQualifier
  proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkCPSURIQualifier fstₚ₁ sndₚ₁ bs≡
  proj₂ equivalent (X509.mkCPSURIQualifier ≡cpsuri cpsPointer bs≡) = mk&ₚ ≡cpsuri cpsPointer bs≡

  iso : Iso (&ₚ (_≡ X509.PQOID.CPSURI) X509.IA5String) X509.CPSURIQualifier
  proj₁ iso = equivalent
  proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
  proj₂ (proj₂ iso) (X509.mkCPSURIQualifier ≡cpsuri cpsPointer bs≡) = refl

  @0 unambiguous : Unambiguous X509.CPSURIQualifier
  unambiguous =
    isoUnambiguous iso
      (unambiguous&ₚ ≡-unique (λ where _ refl refl → refl) (TLVProps.unambiguous IA5Props.unambiguous))


module UserNoticeQualifier where

  equivalent : Equivalent (&ₚ (_≡ X509.PQOID.USERNOTICE) X509.UserNotice) X509.UserNoticeQualifier
  proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkUserNoticeQualifier fstₚ₁ sndₚ₁ bs≡
  proj₂ equivalent (X509.mkUserNoticeQualifier ≡usernotice unotice bs≡) = mk&ₚ ≡usernotice unotice bs≡

  iso : Iso (&ₚ (_≡ X509.PQOID.USERNOTICE) X509.UserNotice) X509.UserNoticeQualifier
  proj₁ iso = equivalent
  proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
  proj₂ (proj₂ iso) (X509.mkUserNoticeQualifier ≡usernotice unotice bs≡) = refl

  @0 unambiguous : Unambiguous X509.UserNoticeQualifier
  unambiguous =
    isoUnambiguous iso
      (unambiguous&ₚ ≡-unique (λ where _ refl refl → refl) (TLVProps.unambiguous UserNoticeProps.unambiguous))


equivalent : Equivalent (Sum X509.CPSURIQualifier X509.UserNoticeQualifier) X509.PolicyQualifierInfoFields
proj₁ equivalent (Sum.inj₁ x) = X509.cpsURI x
proj₁ equivalent (Sum.inj₂ x) = X509.userNotice x
proj₂ equivalent (X509.cpsURI x) = Sum.inj₁ x
proj₂ equivalent (X509.userNotice x) = Sum.inj₂ x

iso : Iso (Sum X509.CPSURIQualifier X509.UserNoticeQualifier) X509.PolicyQualifierInfoFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ x) = refl
proj₂ (proj₂ iso) (X509.cpsURI x) = refl
proj₂ (proj₂ iso) (X509.userNotice x) = refl

@0 nonnesting : NonNesting X509.PolicyQualifierInfoFields
nonnesting {xs₁} {ys₁} {xs₂} {ys₂} x (X509.cpsURI (X509.mkCPSURIQualifier {bs₁ = bs₁} {bs₂} refl cpsPointer bs≡)) (X509.cpsURI (X509.mkCPSURIQualifier {bs₁ = bs₃} {bs₄} refl cpsPointer₁ bs≡₁)) =
  begin (xs₁ ≡⟨ bs≡ ⟩
        oid ++ bs₂ ≡⟨ cong (oid ++_) bs₂≡ ⟩
        oid ++ bs₄ ≡⟨ sym bs≡₁ ⟩
        xs₂ ∎)
  where
  oid =  # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 1 ]
  @0 x' : oid ++ bs₂ ++ ys₁ ≡ oid ++ bs₄ ++ ys₂
  x' = (begin (oid ++ bs₂ ++ ys₁ ≡⟨ solve (++-monoid Dig) ⟩
              (oid ++ bs₂) ++ ys₁ ≡⟨ sym (cong (_++ ys₁) bs≡) ⟩
              xs₁ ++ ys₁ ≡⟨ x ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
              (oid ++ bs₄) ++ ys₂ ≡⟨ solve (++-monoid Dig) ⟩
              oid ++ bs₄ ++ ys₂ ∎))
  @0 bs₂≡ : bs₂ ≡ bs₄
  bs₂≡ = TLVProps.nonnesting (++-cancelˡ oid x') cpsPointer cpsPointer₁
nonnesting {xs₁} {ys₁} {xs₂} {ys₂} x (X509.cpsURI (X509.mkCPSURIQualifier {bs₁ = bs₁} {bs₂} refl cpsPointer bs≡)) (X509.userNotice (X509.mkUserNoticeQualifier {bs₁ = bs₃} {bs₄} refl unotice bs≡₁)) = case (‼ x') of λ ()
  where
  OID₁ =  # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 1 ]
  OID₂ =  # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 2 ]
  @0 x' : OID₁ ++ bs₂ ++ ys₁ ≡ OID₂ ++ bs₄ ++ ys₂
  x' = (begin (OID₁ ++ bs₂ ++ ys₁ ≡⟨ solve (++-monoid Dig) ⟩
              (OID₁ ++ bs₂) ++ ys₁ ≡⟨ sym (cong (_++ ys₁) bs≡) ⟩
              xs₁ ++ ys₁ ≡⟨ x ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
              (OID₂ ++ bs₄) ++ ys₂ ≡⟨ solve (++-monoid Dig) ⟩
              OID₂ ++ bs₄ ++ ys₂ ∎))
nonnesting {xs₁} {ys₁} {xs₂} {ys₂}  x (X509.userNotice (X509.mkUserNoticeQualifier {bs₁ = bs₁} {bs₂} refl unotice bs≡)) (X509.cpsURI (X509.mkCPSURIQualifier {bs₁ = bs₃} {bs₄} refl cpsPointer bs≡₁)) = case (‼ x') of λ ()
  where
  OID₁ =  # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 2 ]
  OID₂ =  # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 1 ]
  @0 x' : OID₁ ++ bs₂ ++ ys₁ ≡ OID₂ ++ bs₄ ++ ys₂
  x' = (begin (OID₁ ++ bs₂ ++ ys₁ ≡⟨ solve (++-monoid Dig) ⟩
              (OID₁ ++ bs₂) ++ ys₁ ≡⟨ sym (cong (_++ ys₁) bs≡) ⟩
              xs₁ ++ ys₁ ≡⟨ x ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
              (OID₂ ++ bs₄) ++ ys₂ ≡⟨ solve (++-monoid Dig) ⟩
              OID₂ ++ bs₄ ++ ys₂ ∎))
nonnesting {xs₁} {ys₁} {xs₂} {ys₂} x (X509.userNotice (X509.mkUserNoticeQualifier {bs₁ = bs₁} {bs₂} refl unotice bs≡)) (X509.userNotice (X509.mkUserNoticeQualifier {bs₁ = bs₃} {bs₄} refl unotice₁ bs≡₁)) =
  begin (xs₁ ≡⟨ bs≡ ⟩
        oid ++ bs₂ ≡⟨ cong (oid ++_) bs₂≡ ⟩
        oid ++ bs₄ ≡⟨ sym bs≡₁ ⟩
        xs₂ ∎)
  where
  oid =  # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 2 ]
  @0 x' : oid ++ bs₂ ++ ys₁ ≡ oid ++ bs₄ ++ ys₂
  x' = (begin (oid ++ bs₂ ++ ys₁ ≡⟨ solve (++-monoid Dig) ⟩
              (oid ++ bs₂) ++ ys₁ ≡⟨ sym (cong (_++ ys₁) bs≡) ⟩
              xs₁ ++ ys₁ ≡⟨ x ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
              (oid ++ bs₄) ++ ys₂ ≡⟨ solve (++-monoid Dig) ⟩
              oid ++ bs₄ ++ ys₂ ∎))
  @0 bs₂≡ : bs₂ ≡ bs₄
  bs₂≡ =  TLVProps.nonnesting (++-cancelˡ oid x') unotice unotice₁

@0 unambiguous : Unambiguous X509.PolicyQualifierInfoFields
unambiguous =
  isoUnambiguous iso
    (unambiguousSum CPSURIQualifier.unambiguous UserNoticeQualifier.unambiguous
      λ where
        {xs₁}{ys₁}{xs₂}{ys₂} ++≡ (X509.mkCPSURIQualifier{bs₂ = bs₂} refl cpsPointer bs≡) (X509.mkUserNoticeQualifier{bs₂ = bs₃} refl unotice bs≡₁) → ‼
          let @0 bs≡' : X509.PQOID.CPSURI ++ bs₂ ++ ys₁ ≡ X509.PQOID.USERNOTICE ++ bs₃ ++ ys₂
              bs≡' = begin
                 X509.PQOID.CPSURI ++ bs₂ ++ ys₁ ≡⟨ solve (++-monoid Dig) ⟩
                (X509.PQOID.CPSURI ++ bs₂) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                (X509.PQOID.USERNOTICE ++ bs₃) ++ ys₂ ≡⟨ solve (++-monoid Dig) ⟩
                _ ∎
          in
          case ‼ bs≡' of λ ())
