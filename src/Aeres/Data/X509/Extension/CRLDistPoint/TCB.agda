{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames.TCB
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.TCB where

open Aeres.Grammar.Definitions UInt8

CRLDistFieldsSeq : @0 List UInt8 → Set
CRLDistFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf DistPoint) xs

CRLDistFields : @0 List UInt8 → Set
CRLDistFields xs = TLV Tag.OctetString  CRLDistFieldsSeq xs

RawCRLDistFields : Raw CRLDistFields
RawCRLDistFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf RawDistPoint 1))
