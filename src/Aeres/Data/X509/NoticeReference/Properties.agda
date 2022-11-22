{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
open import Aeres.Data.X509.DisplayText
open import Aeres.Data.X509.NoticeReference.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Prelude

module Aeres.Data.X509.NoticeReference.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8

iso : Iso (&ₚ DisplayText IntegerSeq) NoticeReferenceFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkNoticeReferenceFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (mkNoticeReferenceFields organization noticenums bs≡) = mk&ₚ organization noticenums bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkNoticeReferenceFields organization noticenums bs≡) = refl

@0 unambiguous : Unambiguous NoticeReferenceFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ
      DisplayText.unambiguous DisplayText.nonnesting
      (TLV.unambiguous
        (SequenceOf.unambiguous (TLV.unambiguous λ {xs} → Int.unambiguous{xs})
          TLV.nonempty (NonNesting Int ∋ TLV.nonnesting))))
          
instance
  NoticeReferenceEq : Eq (Exists─ _ NoticeReferenceFields)
  NoticeReferenceEq =
    isoEq iso (eq&ₚ it it)
  
