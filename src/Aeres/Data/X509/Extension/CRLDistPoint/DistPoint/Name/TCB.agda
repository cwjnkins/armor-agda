{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames.TCB
open import Aeres.Data.X509.Name.TCB
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Sum.TCB
open import Aeres.Data.X509.Name.RDN.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum.TCB     UInt8

{- RFC 5820, 4.2.1.13
-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.13
-- 
-- id-ce-cRLDistributionPoints OBJECT IDENTIFIER ::=  { id-ce 31 }
-- 
--    CRLDistributionPoints ::= SEQUENCE SIZE (1..MAX) OF DistributionPoint
-- 
--    DistributionPoint ::= SEQUENCE {
--         distributionPoint       [0]     DistributionPointName OPTIONAL,
--         reasons                 [1]     ReasonFlags OPTIONAL,
--         cRLIssuer               [2]     GeneralNames OPTIONAL }
-- 
--    DistributionPointName ::= CHOICE {
--         fullName                [0]     GeneralNames,
--         nameRelativeToCRLIssuer [1]     RelativeDistinguishedName }
-- 
-- 
--    ReasonFlags ::= BIT STRING {
--         unused                  (0),
--         keyCompromise           (1),
--         cACompromise            (2),
--         affiliationChanged      (3),
--         superseded              (4),
--         cessationOfOperation    (5),
--         certificateHold         (6),
--         privilegeWithdrawn      (7),
--         aACompromise            (8) }
-}
FullName : @0 List UInt8 → Set
FullName xs = TLV Tag.AA0 GeneralNamesElems xs

NameRTCrlIssuer : @0 List UInt8 → Set
NameRTCrlIssuer xs = TLV Tag.AA1 RDN xs

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
RawDistPointNameChoiceRep = RawSum (RawTLV _ RawGeneralNamesElems)
                                    (RawTLV _ RawRDN)
RawDistPointName : Raw DistPointName
RawDistPointName = RawTLV _ (Iso.raw equivalentDistPointNameChoice RawDistPointNameChoiceRep)
