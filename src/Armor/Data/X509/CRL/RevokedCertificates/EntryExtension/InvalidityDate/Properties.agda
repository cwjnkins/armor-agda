{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.InvalidityDate.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Properties
open import Armor.Data.X690-DER.Time.GeneralizedTime

open import Armor.Prelude

module  Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.InvalidityDate.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Properties  UInt8

@0 unambiguous : Unambiguous InvalidityDateFields
unambiguous = TLV.unambiguous GeneralizedTime.unambiguous

@0 nonmalleable : NonMalleable RawInvalidityDateFields
nonmalleable = TLV.nonmalleable GeneralizedTime.nonmalleable
