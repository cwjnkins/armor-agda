open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.DisplayText.TCB
import      Aeres.Grammar.Option
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.TCB where

open Aeres.Grammar.Option UInt8
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq.TCB UInt8

record UserNoticeFields (@0 bs : List UInt8) : Set where
  constructor mkUserNoticeFields
  field
    @0 {nr et} : List UInt8
    noticeRef : Option NoticeReference nr
    expText : Option DisplayText et
    @0 bs≡  : bs ≡ nr ++ et

UserNotice : (@0 _ : List UInt8) → Set
UserNotice xs = TLV Tag.Sequence UserNoticeFields xs

UserNoticeFieldsRep = &ₚ (Option NoticeReference) (Option DisplayText)

equivalentUserNoticeFields : Equivalent UserNoticeFieldsRep UserNoticeFields
proj₂ equivalentUserNoticeFields (mkUserNoticeFields noticeRef expText bs≡) = mk&ₚ noticeRef expText bs≡
proj₁ equivalentUserNoticeFields (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkUserNoticeFields fstₚ₁ sndₚ₁ bs≡

RawUserNoticeFieldsRep : Raw UserNoticeFieldsRep
RawUserNoticeFieldsRep = Raw&ₚ (RawOption RawNoticeReference) (RawOption RawDisplayText)

RawUserNoticeFields : Raw UserNoticeFields
RawUserNoticeFields = Iso.raw equivalentUserNoticeFields RawUserNoticeFieldsRep

RawUserNotice : Raw UserNotice
RawUserNotice = RawTLV _ RawUserNoticeFields
