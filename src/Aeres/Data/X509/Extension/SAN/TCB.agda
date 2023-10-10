{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X509.Extension.SAN.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

SANFields : @0 List UInt8 → Set
SANFields xs = TLV Tag.OctetString GeneralNames xs

RawSANFields : Raw SANFields
RawSANFields = RawTLV _ RawGeneralNames
