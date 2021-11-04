{-# OPTIONS --subtyping #-}


open import Aeres.Binary
open import Aeres.Data.X509
import Aeres.Data.X509.Properties.TLV as TLVProps
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


module UserNoticeQualifier where

  equivalent : Equivalent (&ₚ (_≡ X509.PQOID.USERNOTICE) X509.UserNotice) X509.UserNoticeQualifier
  proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkUserNoticeQualifier fstₚ₁ sndₚ₁ bs≡
  proj₂ equivalent (X509.mkUserNoticeQualifier ≡usernotice unotice bs≡) = mk&ₚ ≡usernotice unotice bs≡


equivalent : Equivalent (Sum X509.CPSURIQualifier X509.UserNoticeQualifier) X509.PolicyQualifierInfoFields
proj₁ equivalent (Sum.inj₁ x) = X509.cpsURI x
proj₁ equivalent (Sum.inj₂ x) = X509.userNotice x
proj₂ equivalent (X509.cpsURI x) = Sum.inj₁ x
proj₂ equivalent (X509.userNotice x) = Sum.inj₂ x


@0 nonnesting : NonNesting X509.PolicyQualifierInfoFields
nonnesting {xs₁} {ys₁} {xs₂} {ys₂} x (X509.cpsURI (X509.mkCPSURIQualifier {bs₁ = bs₁} {bs₂} refl cpsPointer bs≡)) (X509.cpsURI (X509.mkCPSURIQualifier {bs₁ = bs₃} {bs₄} refl cpsPointer₁ bs≡₁)) =
  begin (xs₁ ≡⟨ bs≡ ⟩
        OID ++ bs₂ ≡⟨ cong (OID ++_) bs₂≡ ⟩
        OID ++ bs₄ ≡⟨ sym bs≡₁ ⟩
        xs₂ ∎)
  where
  OID =  # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 1 ]
  @0 x' : OID ++ bs₂ ++ ys₁ ≡ OID ++ bs₄ ++ ys₂
  x' = (begin (OID ++ bs₂ ++ ys₁ ≡⟨ solve (++-monoid Dig) ⟩
              (OID ++ bs₂) ++ ys₁ ≡⟨ sym (cong (_++ ys₁) bs≡) ⟩
              xs₁ ++ ys₁ ≡⟨ x ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
              (OID ++ bs₄) ++ ys₂ ≡⟨ solve (++-monoid Dig) ⟩
              OID ++ bs₄ ++ ys₂ ∎))
  @0 bs₂≡ : bs₂ ≡ bs₄
  bs₂≡ = TLVProps.nonnesting (++-cancelˡ OID x') cpsPointer cpsPointer₁
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
        OID ++ bs₂ ≡⟨ cong (OID ++_) bs₂≡ ⟩
        OID ++ bs₄ ≡⟨ sym bs≡₁ ⟩
        xs₂ ∎)
  where
  OID =  # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 2 ]
  @0 x' : OID ++ bs₂ ++ ys₁ ≡ OID ++ bs₄ ++ ys₂
  x' = (begin (OID ++ bs₂ ++ ys₁ ≡⟨ solve (++-monoid Dig) ⟩
              (OID ++ bs₂) ++ ys₁ ≡⟨ sym (cong (_++ ys₁) bs≡) ⟩
              xs₁ ++ ys₁ ≡⟨ x ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
              (OID ++ bs₄) ++ ys₂ ≡⟨ solve (++-monoid Dig) ⟩
              OID ++ bs₄ ++ ys₂ ∎))
  @0 bs₂≡ : bs₂ ≡ bs₄
  bs₂≡ =  TLVProps.nonnesting (++-cancelˡ OID x') unotice unotice₁
