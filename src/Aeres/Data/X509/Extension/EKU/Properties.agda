{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.EKU.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.SequenceOf

open import Aeres.Prelude

module Aeres.Data.X509.Extension.EKU.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous EKUFields
unambiguous = TLV.unambiguous (TLV.unambiguous
                         (SequenceOf.Bounded.unambiguous OID.unambiguous  TLV.nonempty TLV.nosubstrings))

@0 nonmalleable : NonMalleable RawEKUFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable
                        (SequenceOf.Bounded.nonmalleable TLV.nonempty TLV.nosubstrings  OID.nonmalleable))
