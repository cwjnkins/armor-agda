{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.Extension.EKU.TCB where

EKUFieldsSeq : @0 List UInt8 → Set
EKUFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf OID) xs

EKUFields : @0 List UInt8 → Set
EKUFields xs = TLV Tag.OctetString EKUFieldsSeq xs

