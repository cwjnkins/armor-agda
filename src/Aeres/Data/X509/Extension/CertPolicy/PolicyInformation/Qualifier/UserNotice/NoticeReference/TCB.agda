{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.DisplayText.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference.TCB where

record NoticeReferenceFields (@0 bs : List UInt8) : Set where
  constructor mkNoticeReferenceFields
  field
    @0 {org nn} : List UInt8
    organization : DisplayText org
    noticenums : IntegerSeq nn
    @0 bs≡  : bs ≡ org ++ nn

NoticeReference : @0 List UInt8 → Set
NoticeReference xs = TLV Tag.Sequence NoticeReferenceFields xs
