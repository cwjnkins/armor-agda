{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.DirectoryString
open import Aeres.Data.X509.Name.OLD.Properties
open import Aeres.Data.X509.Name.OLD.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
import      Data.Nat.Properties as Nat

module Aeres.Data.X509.Name.OLD.Eq where

open Aeres.Grammar.Definitions UInt8

-- instance
--   eq≋ATV : Eq≋ RDNATVFields
--   eq≋ATV =
--     isoEq≋ ATV.iso
--       (Eq⇒Eq≋ (eq&ₚ it (Eq≋⇒Eq it)))

--   eq≋Elems : Eq≋ RDNElems
--   eq≋Elems = SequenceOf.BoundedSequenceOfEq≋
