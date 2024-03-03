open import Armor.Binary
open import Armor.Data.X509.GeneralNames.TCB
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Seq.TCB     UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.13
--
-- While each of these fields is optional, a DistributionPoint MUST NOT consist
-- of only the Reasons field; either distributionPoint or CRLIssuer MUST be
-- present.
--
--    DistributionPoint ::= SEQUENCE {
--         distributionPoint       [0]     DistributionPointName OPTIONAL,
--         reasons                 [1]     ReasonFlags OPTIONAL,
--         cRLIssuer               [2]     GeneralNames OPTIONAL }

--    DistributionPointName ::= CHOICE {
--         fullName                [0]     GeneralNames,
--         nameRelativeToCRLIssuer [1]     RelativeDistinguishedName }

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

CrlIssuer : @0 List UInt8 → Set
CrlIssuer xs = TLV Tag.AA2 GeneralNamesElems xs

ReasonFlags : @0 List UInt8 → Set
ReasonFlags xs = TLV Tag.A81 BitStringValue xs

notOnlyReasons : ∀ {@0 dp rsn issr} → Option ReasonFlags rsn → Option DistPointName dp → Option CrlIssuer issr → Bool
notOnlyReasons reasons distributionPoint cRLIssuer = isNone reasons ∨ isSome distributionPoint ∨ isSome cRLIssuer

record DistPointFields (@0 bs : List UInt8) : Set where
  constructor mkDistPointFields
  field
    @0 {dp rsn issr} : List UInt8
    crldp : Option DistPointName dp
    crldprsn : Option ReasonFlags rsn
    crlissr : Option CrlIssuer issr
    @0 notOnlyReasonT : T (notOnlyReasons crldprsn crldp crlissr)
    @0 bs≡  : bs ≡ dp ++ rsn ++ issr

DistPoint : @0 List UInt8 → Set
DistPoint xs = TLV Tag.Sequence DistPointFields xs

DistPointFieldsRep =
  Σₚ (&ₚ (Option DistPointName) (&ₚ (Option ReasonFlags) (Option CrlIssuer)))
     (λ _ crls → T (notOnlyReasons (fstₚ (sndₚ crls)) (fstₚ crls) (sndₚ (sndₚ crls))))

equivalentDistPointFields : Equivalent DistPointFieldsRep DistPointFields
proj₁ equivalentDistPointFields (mk×ₚ (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) nor) =
  mkDistPointFields fstₚ₁ fstₚ₂ sndₚ₁ nor refl
proj₂ equivalentDistPointFields (mkDistPointFields crldp crldprsn crlissr nor bs≡) =
  mk×ₚ (mk&ₚ crldp (mk&ₚ crldprsn crlissr refl) bs≡) (T-irrel nor)

RawDistPointFieldsRep : Raw DistPointFieldsRep
RawDistPointFieldsRep =
  RawΣₚ₁
    (Raw&ₚ (RawOption RawDistPointName)
    (Raw&ₚ (RawOption (RawTLV _ RawBitStringValue))
           (RawOption (RawTLV _ RawGeneralNamesElems))))
    (λ _ crls → T (notOnlyReasons (fstₚ (sndₚ crls)) (fstₚ crls) (sndₚ (sndₚ crls))))

RawDistPointFields : Raw DistPointFields
RawDistPointFields = Iso.raw equivalentDistPointFields RawDistPointFieldsRep

RawDistPoint : Raw DistPoint
RawDistPoint = RawTLV _ RawDistPointFields
