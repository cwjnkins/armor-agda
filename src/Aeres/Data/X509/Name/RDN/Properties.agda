{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.Name.RDN.ATV
open import Aeres.Data.X509.Name.RDN.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Name.RDN.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguousElems : Unambiguous RDNElems
unambiguousElems = SequenceOf.Bounded.unambiguous ATV.unambiguous TLV.nonempty TLV.nosubstrings

@0 unambiguous : Unambiguous RDN
unambiguous = TLV.unambiguous unambiguousElems

@0 nonmalleable : NonMalleable RawRDN
nonmalleable =
  TLV.nonmalleable{A = NonEmptySequenceOf ATV}{R = RawBoundedSequenceOf RawATV 1}
    (SequenceOf.Bounded.nonmalleable{n = 1}{R = RawATV} TLV.nonempty TLV.nosubstrings ATV.nonmalleable)

instance
  eq≋ : Eq≋ (NonEmptySequenceOf ATV)
  eq≋ = SequenceOf.BoundedSequenceOfEq≋
