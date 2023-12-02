open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA.TCB
open import Aeres.Data.X509.Extension.AIA.AccessDesc
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8

@0 unambiguous : Unambiguous AIAFields
unambiguous = TLV.unambiguous (TLV.unambiguous (SequenceOf.Bounded.unambiguous
  AccessDesc.unambiguous TLV.nonempty TLV.nosubstrings))

@0 nonmalleable : NonMalleable RawAIAFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable (SequenceOf.Bounded.nonmalleable
  TLV.nonempty TLV.nosubstrings AccessDesc.nonmalleable))
