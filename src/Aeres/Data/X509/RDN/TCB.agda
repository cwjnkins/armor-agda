{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.RDN.ATV.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.RDN.TCB where

open import       Aeres.Grammar.Definitions UInt8

RDNElems = NonEmptySequenceOf ATV
RDN      = TLV Tag.Sett RDNElems
Name     = Seq RDN

getSeqLen : ∀ {@0 bs} → Name bs → ℕ
getSeqLen = lengthSequence ∘ TLV.val

RawRDNElems : Raw RDNElems
RawRDNElems = RawBoundedSequenceOf RawATV 1

RawName : Raw Name
RawName = RawTLV _ (RawSequenceOf (RawTLV _ RawRDNElems))
