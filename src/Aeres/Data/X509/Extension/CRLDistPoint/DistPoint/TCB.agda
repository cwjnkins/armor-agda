{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralName.TCB
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.TCB where

open Aeres.Grammar.Option UInt8

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
