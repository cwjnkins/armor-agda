{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Option
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.PC.TCB where

open Aeres.Grammar.Definitions    UInt8
open Aeres.Grammar.Option UInt8

RequireExplicitPolicy : @0 List UInt8 → Set
RequireExplicitPolicy xs = TLV Tag.A80 IntegerValue xs

InhibitPolicyMapping : @0 List UInt8 → Set
InhibitPolicyMapping xs = TLV Tag.A81 IntegerValue xs

record PCFieldsSeqFields (@0 bs : List UInt8) : Set where
  constructor mkPCFieldsSeqFields
  field
    @0 {req ini} : List UInt8
    require : Option RequireExplicitPolicy req
    ihibit : Option InhibitPolicyMapping ini
    @0 bs≡  : bs ≡ req ++ ini

PCFieldsSeq : @0 List UInt8 → Set
PCFieldsSeq xs = TLV Tag.Sequence PCFieldsSeqFields xs

PCFields : @0 List UInt8 → Set
PCFields xs = TLV Tag.OctetString  PCFieldsSeq xs

postulate
  RawPCFieldsSeqFields : Raw PCFieldsSeqFields

RawPCFields : Raw PCFields
RawPCFields = RawTLV _ (RawTLV _ RawPCFieldsSeqFields)
