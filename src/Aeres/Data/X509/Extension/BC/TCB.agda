{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Boool.TCB
open import Aeres.Data.X690-DER.Boool.Eq
open import Aeres.Data.X690-DER.Default.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.Length.TCB
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X690-DER.TLV.Properties
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Option
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Extension.BC.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option UInt8
open Aeres.Grammar.Seq.TCB UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.9
--    id-ce-basicConstraints OBJECT IDENTIFIER ::=  { id-ce 19 }

--    BasicConstraints ::= SEQUENCE {
--         cA                      BOOLEAN DEFAULT FALSE,
--         pathLenConstraint       INTEGER (0..MAX) OPTIONAL }

record BCFieldsSeqFields (@0 bs : List UInt8) : Set where
  constructor mkBCFieldsSeqFields
  field
    @0 {ca pl} : List UInt8
    bcca : Default Boool falseBoool ca
    bcpathlen : Option Int pl
    @0 bs≡  : bs ≡ ca ++ pl

BCFieldsSeq : @0 List UInt8 → Set
BCFieldsSeq xs = TLV Tag.Sequence  BCFieldsSeqFields xs

BCFields : @0 List UInt8 → Set
BCFields xs = TLV Tag.OctetString  BCFieldsSeq xs

BCFieldsSeqFieldsRep = &ₚ (Default Boool falseBoool) (Option Int)

equivalentBCFieldsSeqFields : Equivalent BCFieldsSeqFieldsRep BCFieldsSeqFields
proj₁ equivalentBCFieldsSeqFields (Aeres.Grammar.Seq.TCB.mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkBCFieldsSeqFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalentBCFieldsSeqFields (mkBCFieldsSeqFields bcca bcpathlen bs≡) = Aeres.Grammar.Seq.TCB.mk&ₚ bcca bcpathlen bs≡

RawBCFieldsSeqFieldsRep : Raw BCFieldsSeqFieldsRep
RawBCFieldsSeqFieldsRep = Raw&ₚ (RawDefault RawBoool falseBoool) (RawOption RawInt)

RawBCFieldsSeqFields : Raw BCFieldsSeqFields
RawBCFieldsSeqFields = Iso.raw equivalentBCFieldsSeqFields RawBCFieldsSeqFieldsRep

RawBCFields : Raw BCFields
RawBCFields = RawTLV _ (RawTLV _  RawBCFieldsSeqFields)
