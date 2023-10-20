{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.Name.RDN.TCB
import      Aeres.Grammar.Definitions.NonMalleable.Base
open import Aeres.Prelude

module Aeres.Data.X509.Name.TCB where

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

Name : @0 List UInt8 → Set
Name = RDNSequence

RawName : Raw Name
RawName = RawRDNSequence
