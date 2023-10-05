{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Validity.Time.Ordering
open import Aeres.Data.X509.Validity.Time.TCB
  hiding (equivalent)
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.Iso
import      Aeres.Grammar.Definitions.NonMalleable.Base
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Validity.TCB where

open Aeres.Grammar.Definitions.Iso UInt8
open Aeres.Grammar.Definitions.NonMalleable.Base UInt8
open Aeres.Grammar.Seq.TCB UInt8

record ValidityFields (@0 bs : List UInt8) : Set where
  constructor mkValidityFields
  field
    @0 {nb na} : List UInt8
    start : Time nb
    end : Time na
    @0 bs≡  : bs ≡ nb ++ na

ValidityFieldsRep : @0 List UInt8 → Set
ValidityFieldsRep = &ₚ Time Time

equivalent : Equivalent ValidityFieldsRep ValidityFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkValidityFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkValidityFields start end bs≡) = mk&ₚ start end bs≡

RawValidityFieldsRep : Raw ValidityFieldsRep
RawValidityFieldsRep = Raw&ₚ RawTime RawTime

RawValidityFields : Raw ValidityFields
RawValidityFields = Iso.raw equivalent RawValidityFieldsRep

Validity : @0 List UInt8 → Set
Validity = TLV Tag.Sequence ValidityFields

RawValidity : Raw Validity
RawValidity = RawTLV _ RawValidityFields

getNBTime : ∀ {@0 bs} → (v : Validity bs) → Time (ValidityFields.nb (TLV.val v))
getNBTime v = ValidityFields.start (TLV.val v)

getNATime : ∀ {@0 bs} → (v : Validity bs) → Time (ValidityFields.na (TLV.val v))
getNATime v = ValidityFields.end (TLV.val v)

ValidTime : {@0 bs₁ bs₂ : List UInt8} → Time bs₁ → Validity bs₂ → Set
ValidTime t v = getNBTime v Time≤ t × t Time≤ getNATime v

validTime? : ∀ {@0 bs₁ bs₂} → (t : Time bs₁) (v : Validity bs₂) → Dec (ValidTime t v)
validTime? t v = (getNBTime v Time≤? t) ×-dec (t Time≤? getNATime v)
