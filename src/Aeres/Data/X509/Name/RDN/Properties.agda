open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.SetOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.Name.RDN.ATV
open import Aeres.Data.X509.Name.RDN.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Name.RDN.Properties where

open Aeres.Grammar.Definitions UInt8

module RDN where
  @0 [_]unambiguous : ∀ t → Unambiguous [ t ]RDN
  [ t ]unambiguous = TLV.unambiguous (SetOf.unambiguousFields ATV.unambiguous TLV.nonempty TLV.nosubstrings)

  @0 unambiguous : Unambiguous RDN
  unambiguous = [ Tag.Sett ]unambiguous

  @0 [_]nonmalleable : ∀ t → NonMalleable [ t ]RawRDN
  [ t ]nonmalleable = TLV.nonmalleable (SetOf.nonmalleableFields {R = RawATV} TLV.nonempty TLV.nosubstrings ATV.nonmalleable)

  @0 nonmalleable : NonMalleable RawRDN
  nonmalleable = SetOf.nonmalleable{R = RawATV} TLV.nonempty TLV.nosubstrings ATV.nonmalleable

module Sequence where
  @0 unambiguous : Unambiguous RDNSequence
  unambiguous = TLV.unambiguous (SequenceOf.unambiguous RDN.unambiguous TLV.nonempty TLV.nosubstrings)

  @0 nonmalleable : NonMalleable RawRDNSequence
  nonmalleable = TLV.nonmalleable {R = RawSequenceOf RawRDN} (SequenceOf.nonmalleable {R = RawRDN} TLV.nonempty TLV.nosubstrings RDN.nonmalleable)

open RDN public

