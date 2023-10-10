{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames.TCB
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option UInt8
open Aeres.Grammar.Seq.TCB UInt8

CrlIssuer : @0 List UInt8 → Set
CrlIssuer xs = TLV Tag.AA2 GeneralNamesElems xs

ReasonFlags : @0 List UInt8 → Set
ReasonFlags xs = TLV Tag.A81 BitStringValue xs

record DistPointFields (@0 bs : List UInt8) : Set where
  constructor mkDistPointFields
  field
    @0 {dp rsn issr} : List UInt8
    crldp : Option DistPointName dp
    crldprsn : Option ReasonFlags rsn
    crlissr : Option CrlIssuer issr
    @0 bs≡  : bs ≡ dp ++ rsn ++ issr

DistPoint : @0 List UInt8 → Set
DistPoint xs = TLV Tag.Sequence DistPointFields xs

DistPointFieldsRep = &ₚ (Option DistPointName) (&ₚ (Option ReasonFlags) (Option CrlIssuer))

equivalentDistPointFields : Equivalent DistPointFieldsRep DistPointFields
proj₁ equivalentDistPointFields (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = mkDistPointFields fstₚ₁ fstₚ₂ sndₚ₁ refl
proj₂ equivalentDistPointFields (mkDistPointFields crldp crldprsn crlissr bs≡) = mk&ₚ crldp (mk&ₚ crldprsn crlissr refl) bs≡

RawDistPointFieldsRep : Raw DistPointFieldsRep
RawDistPointFieldsRep = Raw&ₚ (RawOption RawDistPointName)
                          (Raw&ₚ (RawOption (RawTLV _ RawBitStringValue))
                                  (RawOption (RawTLV _ RawGeneralNamesElems)))

RawDistPointFields : Raw DistPointFields
RawDistPointFields = Iso.raw equivalentDistPointFields RawDistPointFieldsRep

RawDistPoint : Raw DistPoint
RawDistPoint = RawTLV _ RawDistPointFields
