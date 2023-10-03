{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.SAN.TCB
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
open import       Aeres.Data.X509.GeneralName

open import Aeres.Prelude

module Aeres.Data.X509.Extension.SAN.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8

@0 unambiguousSANFields : Unambiguous SANFields
unambiguousSANFields = TLV.unambiguous GeneralName.GeneralNames.unambiguous

@0 nonmalleableSANFields : NonMalleable RawSANFields
nonmalleableSANFields = TLV.nonmalleable GeneralName.GeneralNames.nonmalleable
