{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.RDN.ATV.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.RDN.TCB where

RDNElems = NonEmptySequenceOf ATV
RDN      = TLV Tag.Sett RDNElems
Name     = Seq RDN

getSeqLen : ∀ {@0 bs} → Name bs → ℕ
getSeqLen = lengthSequence ∘ TLV.val
