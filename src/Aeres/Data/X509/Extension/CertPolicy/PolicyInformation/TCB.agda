open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.TCB where

open Aeres.Grammar.Definitions              UInt8
open Aeres.Grammar.Option UInt8
open Aeres.Grammar.Seq.TCB UInt8

record PolicyInformationFields (@0 bs : List UInt8) : Set where
  constructor mkPolicyInformationFields
  field
    @0 {pid pqls} : List UInt8
    cpid : OID pid
    cpqls : Option PolicyQualifiersSeq pqls
    @0 bs≡  : bs ≡ pid ++ pqls

PolicyInformation : @0 List UInt8 → Set
PolicyInformation xs = TLV Tag.Sequence PolicyInformationFields xs

PolicyInformationFieldsRep = &ₚ OID (Option PolicyQualifiersSeq)

equivalentPolicyInformationFields : Equivalent PolicyInformationFieldsRep PolicyInformationFields
proj₂ equivalentPolicyInformationFields (mkPolicyInformationFields cpid cpqls bs≡) = Aeres.Grammar.Seq.TCB.mk&ₚ cpid cpqls bs≡
proj₁ equivalentPolicyInformationFields (Aeres.Grammar.Seq.TCB.mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkPolicyInformationFields  fstₚ₁ sndₚ₁ bs≡

RawPolicyInformationFieldsRep : Raw PolicyInformationFieldsRep
RawPolicyInformationFieldsRep = Raw&ₚ RawOID (RawOption RawPolicyQualifiersSeq)

RawPolicyInformationFields : Raw PolicyInformationFields
RawPolicyInformationFields = Iso.raw equivalentPolicyInformationFields RawPolicyInformationFieldsRep

RawPolicyInformation : Raw PolicyInformation
RawPolicyInformation = RawTLV _ RawPolicyInformationFields
