{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.SetOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.Name.RDN.ATV.TCB
import      Aeres.Grammar.Definitions.NonMalleable.Base
open import Aeres.Prelude

module Aeres.Data.X509.Name.RDN.TCB where

open Aeres.Grammar.Definitions.NonMalleable.Base UInt8


{- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.4
-- Name ::= CHOICE { -- only one possibility for now --
--   rdnSequence  RDNSequence }
--
-- RDNSequence ::= SEQUENCE OF RelativeDistinguishedName
--
-- RelativeDistinguishedName ::=
--   SET SIZE (1..MAX) OF AttributeTypeAndValue
-}

[_]RDN : UInt8 → @0 List UInt8 → Set
[ t ]RDN = TLV t (SetOfFields ATV)

RDN : @0 List UInt8 → Set
RDN = [ Tag.Sett ]RDN

[_]RawRDN : ∀ t → Raw [ t ]RDN
[ t ]RawRDN = RawTLV t (RawSetOfFields RawATV)

RawRDN : Raw RDN
RawRDN = [ Tag.Sett ]RawRDN

RDNSequence : @0 List UInt8 → Set
RDNSequence = Seq RDN

RawRDNSequence : Raw RDNSequence
RawRDNSequence = RawTLV _ (RawSequenceOf RawRDN)
