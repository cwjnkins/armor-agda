{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Boool.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Option
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.BC.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option UInt8

record BCFieldsSeqFields (@0 bs : List UInt8) : Set where
  constructor mkBCFieldsSeqFields
  field
    @0 {ca pl} : List UInt8
    bcca : Option Boool ca
    bcpathlen : Option Int pl
    @0 bs≡  : bs ≡ ca ++ pl

BCFieldsSeq : @0 List UInt8 → Set
BCFieldsSeq xs = TLV Tag.Sequence  BCFieldsSeqFields xs

BCFields : @0 List UInt8 → Set
BCFields xs = TLV Tag.OctetString  BCFieldsSeq xs

postulate
  RawBCFieldsSeqFields : Raw BCFieldsSeqFields

RawBCFields : Raw BCFields
RawBCFields = RawTLV _ (RawTLV _ RawBCFieldsSeqFields)
