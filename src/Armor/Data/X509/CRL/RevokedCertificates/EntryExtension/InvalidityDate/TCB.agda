{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X690-DER.Time.GeneralizedTime.TCB
open import Armor.Data.X690-DER.Int.TCB as Int
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.InvalidityDate.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

-- id-ce-invalidityDate OBJECT IDENTIFIER ::= { id-ce 24 }
-- InvalidityDate ::=  GeneralizedTime

InvalidityDateFields : @0 List UInt8 → Set
InvalidityDateFields xs = TLV Tag.OctetString GeneralizedTime xs

RawInvalidityDateFields : Raw InvalidityDateFields
RawInvalidityDateFields = RawTLV _ RawGeneralizedTime
