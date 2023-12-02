open import Aeres.Binary
open import Aeres.Data.X509.DisplayText
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference.Properties
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8
          
instance
  NoticeReferenceEq : Eq (Exists─ _ NoticeReferenceFields)
  NoticeReferenceEq =
    Iso.isoEq iso (Seq.eq&ₚ it it)
  
  eq≋ : Eq≋ NoticeReferenceFields
  eq≋ = Eq⇒Eq≋ it
