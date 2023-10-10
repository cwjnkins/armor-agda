{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.Name.RDN.ATV.TCB
import      Aeres.Grammar.Definitions.NonMalleable.Base
open import Aeres.Prelude

module Aeres.Data.X509.Name.RDN.TCB where

open Aeres.Grammar.Definitions.NonMalleable.Base UInt8

RDNElems : @0 List UInt8 → Set
RDNElems = NonEmptySequenceOf ATV

RDN : @0 List UInt8 → Set
RDN = TLV Tag.Sett RDNElems

RawRDN : Raw RDN
RawRDN = RawTLV Tag.Sett (RawBoundedSequenceOf RawATV 1)
