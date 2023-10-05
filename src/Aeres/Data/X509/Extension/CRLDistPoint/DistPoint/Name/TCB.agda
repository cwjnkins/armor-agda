{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralName.TCB
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Sum.TCB
open import Aeres.Data.X509.RDN.ATV.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum.TCB     UInt8

FullName : @0 List UInt8 → Set
FullName xs = TLV Tag.AA0 GeneralNamesElems xs

NameRTCrlIssuer : @0 List UInt8 → Set
NameRTCrlIssuer xs = TLV Tag.AA1 RDNElems xs

data DistPointNameChoice : @0 List UInt8 → Set where
  fullname : ∀ {@0 bs} → FullName bs → DistPointNameChoice bs
  nameRTCrlissr : ∀ {@0 bs} → NameRTCrlIssuer bs → DistPointNameChoice bs

DistPointName : @0 List UInt8 → Set
DistPointName xs = TLV Tag.AA0 DistPointNameChoice xs

DistPointNameChoiceRep = Sum FullName NameRTCrlIssuer

equivalentDistPointNameChoice : Equivalent DistPointNameChoiceRep DistPointNameChoice
proj₁ equivalentDistPointNameChoice (inj₁ x) = fullname x
proj₁ equivalentDistPointNameChoice (inj₂ x) = nameRTCrlissr x
proj₂ equivalentDistPointNameChoice (fullname x) = inj₁ x
proj₂ equivalentDistPointNameChoice (nameRTCrlissr x) = inj₂ x

RawDistPointNameChoiceRep : Raw DistPointNameChoiceRep
RawDistPointNameChoiceRep = RawSum (RawTLV _ (RawBoundedSequenceOf RawGeneralName 1))
                                    (RawTLV _ RawRDNElems)
RawDistPointName : Raw DistPointName
RawDistPointName = RawTLV _ (Iso.raw equivalentDistPointNameChoice RawDistPointNameChoiceRep)
