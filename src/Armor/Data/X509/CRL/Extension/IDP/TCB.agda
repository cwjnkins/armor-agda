open import Armor.Binary
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X690-DER.TLV.Properties
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.Default.TCB
open import Armor.Data.X690-DER.Boool.TCB
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.Boool.Eq
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.CRL.Extension.IDP.TCB where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option UInt8
open Armor.Grammar.Parallel UInt8
open Armor.Grammar.Seq.TCB UInt8

-- id-ce-issuingDistributionPoint OBJECT IDENTIFIER ::= { id-ce 28 }
-- IssuingDistributionPoint ::= SEQUENCE {
--        distributionPoint          [0] DistributionPointName OPTIONAL,
--        onlyContainsUserCerts      [1] BOOLEAN DEFAULT FALSE,
--        onlyContainsCACerts        [2] BOOLEAN DEFAULT FALSE,
--        onlySomeReasons            [3] ReasonFlags OPTIONAL,
--        indirectCRL                [4] BOOLEAN DEFAULT FALSE,
--        onlyContainsAttributeCerts [5] BOOLEAN DEFAULT FALSE }

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

ReasonFlags : @0 List UInt8 → Set
ReasonFlags xs = TLV Tag.A83 BitStringValue xs

record IDPFieldsSeqFields (@0 bs : List UInt8) : Set where
  constructor mkIDPFieldsSeqFields
  field
    @0 {dp ouser oca osr icrl oatt} : List UInt8
    distributionPoint : Option DistPointName dp
    onlyContainsUserCerts : Default [ Tag.A81 ]Boool [ Tag.A81 ]falseBoool ouser
    onlyContainsCACerts  : Default [ Tag.A82 ]Boool [ Tag.A82 ]falseBoool oca
    onlySomeReasons : Option ReasonFlags osr
    indirectCRL : Default [ Tag.A84 ]Boool [ Tag.A84 ]falseBoool icrl
    onlyContainsAttributeCerts : Default [ Tag.A85 ]Boool [ Tag.A85 ]falseBoool oatt
    @0 bs≡  : bs ≡ dp ++ ouser ++ oca ++ osr ++ icrl ++ oatt

IDPFieldsSeq : (@0 _ : List UInt8) → Set
IDPFieldsSeq xs = TLV Tag.Sequence  (NonEmptySequenceOf IDPFieldsSeqFields) xs

IDPFields : @0 List UInt8 → Set
IDPFields xs = TLV Tag.OctetString IDPFieldsSeq xs


IDPFieldsSeqFieldsRep = &ₚ (Option DistPointName)
                        (&ₚ (Default [ Tag.A81 ]Boool [ Tag.A81 ]falseBoool)
                        (&ₚ (Default [ Tag.A82 ]Boool [ Tag.A82 ]falseBoool)
                        (&ₚ (Option ReasonFlags)
                        (&ₚ (Default [ Tag.A84 ]Boool [ Tag.A84 ]falseBoool)
                             (Default [ Tag.A85 ]Boool [ Tag.A85 ]falseBoool)))))

equivalentIDPFieldsSeqFields : Equivalent IDPFieldsSeqFieldsRep IDPFieldsSeqFields
proj₁ equivalentIDPFieldsSeqFields (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ sndₚ₁ refl) refl) refl) refl) refl)
  = mkIDPFieldsSeqFields fstₚ₁ fstₚ₂ fstₚ₃ fstₚ₄ fstₚ₅ sndₚ₁ refl
proj₂ equivalentIDPFieldsSeqFields (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts
                                   onlySomeReasons indirectCRL onlyContainsAttributeCerts refl)
  =
    mk&ₚ distributionPoint
      (mk&ₚ onlyContainsUserCerts
        (mk&ₚ onlyContainsCACerts
          (mk&ₚ onlySomeReasons
            (mk&ₚ indirectCRL onlyContainsAttributeCerts refl) refl) refl) refl) refl


RawIDPFieldsSeqFieldsRep : Raw IDPFieldsSeqFieldsRep
RawIDPFieldsSeqFieldsRep = Raw&ₚ (RawOption RawDistPointName)
                           (Raw&ₚ (RawDefault (RawTLV _ RawBoolValue) [ Tag.A81 ]falseBoool)
                           (Raw&ₚ (RawDefault (RawTLV _ RawBoolValue) [ Tag.A82 ]falseBoool) (
                           Raw&ₚ (RawOption (RawTLV _ RawBitStringValue))
                           (Raw&ₚ (RawDefault (RawTLV _ RawBoolValue) [ Tag.A84 ]falseBoool)
                                  (RawDefault (RawTLV _ RawBoolValue) [ Tag.A85 ]falseBoool)))))

RawIDPFieldsSeqFields : Raw IDPFieldsSeqFields
RawIDPFieldsSeqFields = Iso.raw equivalentIDPFieldsSeqFields RawIDPFieldsSeqFieldsRep

RawIDPFields : Raw IDPFields
RawIDPFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf RawIDPFieldsSeqFields 1))
