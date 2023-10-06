{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.Name.RDN.TCB
import      Aeres.Grammar.Definitions.NonMalleable.Base
open import Aeres.Prelude

module Aeres.Data.X509.Name.TCB where

open Aeres.Grammar.Definitions.NonMalleable.Base UInt8

Name : @0 List UInt8 → Set
Name = Seq RDN

RawName : Raw Name
RawName = RawTLV _ (RawSequenceOf RawRDN)
