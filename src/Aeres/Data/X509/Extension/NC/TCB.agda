{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.NC.GeneralSubtree.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.Extension.NC.TCB where

open Aeres.Grammar.Option UInt8

PermittedSubtrees : @0 List UInt8 → Set
PermittedSubtrees xs = TLV Tag.AA0 GeneralSubtrees xs

ExcludedSubtrees : @0 List UInt8 → Set
ExcludedSubtrees xs = TLV Tag.AA1 GeneralSubtrees xs

record NCFieldsSeqFields (@0 bs : List UInt8) : Set where
  constructor mkNCFieldsSeqFields
  field
    @0 {pe ex} : List UInt8
    permt : Option PermittedSubtrees pe
    excld : Option ExcludedSubtrees ex
    @0 bs≡  : bs ≡ pe ++ ex

NCFieldsSeq : @0 List UInt8 → Set
NCFieldsSeq xs = TLV Tag.Sequence NCFieldsSeqFields xs

NCFields : @0 List UInt8 → Set
NCFields xs = TLV Tag.OctetString  NCFieldsSeq xs
