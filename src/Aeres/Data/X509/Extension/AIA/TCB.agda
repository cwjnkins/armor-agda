{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA.AccessDesc.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.TCB where

open Aeres.Grammar.Definitions UInt8

AIAFieldsSeq : @0 List UInt8 → Set
AIAFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf AccessDesc) xs

AIAFields : @0 List UInt8 → Set
AIAFields xs = TLV Tag.OctetString AIAFieldsSeq xs

RawAIAFields : Raw AIAFields
RawAIAFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf RawAccessDesc 1))
