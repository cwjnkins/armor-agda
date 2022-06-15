{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.DisplayText as DisplayTextProps
import      Aeres.Data.X509.Properties.Primitives  as PrimProps
open import Aeres.Data.X690-DER
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.NoticeReferenceFields where

open Base256

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8


iso : Iso (&ₚ X509.DisplayText IntegerSeq) X509.NoticeReferenceFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkNoticeReferenceFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (X509.mkNoticeReferenceFields organization noticenums bs≡) = mk&ₚ organization noticenums bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkNoticeReferenceFields organization noticenums bs≡) = refl

@0 unambiguous : Unambiguous X509.NoticeReferenceFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ
      DisplayTextProps.unambiguous DisplayTextProps.nonnesting
      (TLV.unambiguous
        (SequenceOf.unambiguous (TLV.unambiguous λ {xs} → PrimProps.IntegerValue.unambiguous{xs})
          TLV.nonempty (NonNesting Int ∋ TLV.nonnesting))))
          
