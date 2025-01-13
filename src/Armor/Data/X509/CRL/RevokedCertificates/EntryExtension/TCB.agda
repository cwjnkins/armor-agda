open import Armor.Binary
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.InvalidityDate.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.CertIssuer.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.TCB
import      Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB.OIDS as OIDS
open import Armor.Data.X690-DER.Boool.TCB as Boool
  hiding (getBool)
open import Armor.Data.X690-DER.Boool.Eq
open import Armor.Data.X690-DER.Default.TCB
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X690-DER.TLV.Properties
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.Length.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Option.TCB
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Sum.TCB
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Option.TCB   UInt8
open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Sum.TCB      UInt8
open Armor.Grammar.Seq         UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1
--    Extensions  ::=  SEQUENCE SIZE (1..MAX) OF Extension

--    Extension  ::=  SEQUENCE  {
--         extnID      OBJECT IDENTIFIER,
--         critical    BOOLEAN DEFAULT FALSE,
--         extnValue   OCTET STRING
--                     -- contains the DER encoding of an ASN.1 value
--                     -- corresponding to the extension type identified
--                     -- by extnID
--         }

supportedExtensions : List (List UInt8)
supportedExtensions = OIDS.REASONLit ∷ OIDS.INVALIDITYLit ∷ [ OIDS.CERTISSUERLit ]

record ExtensionFields (@0 P : List UInt8 → Set) (A : @0 List UInt8 → Set) (@0 bs : List UInt8) : Set where
  constructor mkExtensionFields
  field
    @0 {oex cex ocex} : List UInt8
    extnId : OID oex
    @0 extnId≡ : P (TLV.v extnId) -- oex ≡ lit
    crit : Default Boool falseBoool cex
    extension : A ocex
    @0 bs≡ : bs ≡ oex ++ cex ++ ocex

  getCrit : Bool
  getCrit = Boool.getBool (proj₂ (Default.getValue crit))

ExtensionFieldCRLReason       = ExtensionFields (_≡ OIDS.REASONLit)  ReasonCodeFields
ExtensionFieldInvalidityDate  = ExtensionFields (_≡ OIDS.INVALIDITYLit) InvalidityDateFields
ExtensionFieldCertIssuer      = ExtensionFields (_≡ OIDS.CERTISSUERLit)  CertIssuerFields
ExtensionFieldUnsupported     = ExtensionFields (False ∘ (_∈? supportedExtensions)) OctetString

data SelectEntryExtn : @0 List UInt8 → Set where
  crlrsnextn  : ∀ {@0 bs} → ExtensionFieldCRLReason bs → SelectEntryExtn bs 
  invdateextn  : ∀ {@0 bs} → ExtensionFieldInvalidityDate bs → SelectEntryExtn bs 
  certissextn   : ∀ {@0 bs} → ExtensionFieldCertIssuer bs  → SelectEntryExtn bs 
-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2
-- A certificate-using system MUST reject the certificate if it encounters a critical Extension
-- it does not recognize or a critical Extension that contains information that it cannot process.
  other    : ∀ {@0 bs} → (u : ExtensionFieldUnsupported bs) → T (not (ExtensionFields.getCrit u)) → SelectEntryExtn bs

EntryExtension : @0 List UInt8 → Set
EntryExtension xs = TLV Tag.Sequence SelectEntryExtn xs

EntryExtensions : @0 List UInt8 → Set
EntryExtensions xs = TLV Tag.Sequence (NonEmptySequenceOf EntryExtension) xs


ExtensionFieldsRep : (@0 P : List UInt8 → Set) (A : @0 List UInt8 → Set) → @0 List UInt8 → Set
ExtensionFieldsRep P A = &ₚ (Σₚ OID (λ _ x → Erased (P (TLV.v x)))) (&ₚ (Default Boool falseBoool) A)

equivalentExtensionFields : ∀ {@0 P : List UInt8 → Set} {A : @0 List UInt8 → Set}
               → Equivalent (ExtensionFieldsRep P A) (ExtensionFields P A)
proj₁ equivalentExtensionFields (mk&ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁)) (mk&ₚ fstₚ₂ sndₚ₂ refl) refl) =
    mkExtensionFields fstₚ₁ sndₚ₁ fstₚ₂ sndₚ₂ refl
proj₂ equivalentExtensionFields (mkExtensionFields extnId extnId≡ crit extension refl) =
    mk&ₚ (mk×ₚ extnId (─ extnId≡)) (mk&ₚ crit extension refl) refl

RawExtensionFieldsRep : ∀ {@0 P} {A : @0 List UInt8 → Set} (ra : Raw A) → Raw (ExtensionFieldsRep P A)
RawExtensionFieldsRep{P} ra = Raw&ₚ (RawΣₚ₁ RawOID (λ _ x → Erased (P (TLV.v x))))
                            (Raw&ₚ (RawDefault RawBoool falseBoool) ra)

RawExtensionFields : ∀ {@0 P} {A : @0 List UInt8 → Set} (ra : Raw A) → Raw (ExtensionFields P A)
RawExtensionFields ra = Iso.raw equivalentExtensionFields (RawExtensionFieldsRep ra)

SelectEntryExtnRep = Sum ExtensionFieldCRLReason (Sum ExtensionFieldInvalidityDate (Sum ExtensionFieldCertIssuer
  (Σₚ ExtensionFieldUnsupported (λ _ u → T (not (ExtensionFields.getCrit u))))))

equivalent : Equivalent SelectEntryExtnRep SelectEntryExtn
proj₁ equivalent (Armor.Grammar.Sum.TCB.inj₁ x) = crlrsnextn x
proj₁ equivalent (Armor.Grammar.Sum.TCB.inj₂ (Armor.Grammar.Sum.TCB.inj₁ x)) = invdateextn x
proj₁ equivalent (Armor.Grammar.Sum.TCB.inj₂ (Armor.Grammar.Sum.TCB.inj₂ (Armor.Grammar.Sum.TCB.inj₁ x))) = certissextn x
proj₁ equivalent (Armor.Grammar.Sum.TCB.inj₂ (Armor.Grammar.Sum.TCB.inj₂ (Armor.Grammar.Sum.TCB.inj₂ x))) = other (fstₚ x) (sndₚ x)
proj₂ equivalent (crlrsnextn x) = Sum.inj₁ x
proj₂ equivalent (invdateextn x) = Sum.inj₂ (Sum.inj₁ x)
proj₂ equivalent (certissextn x) = Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))
proj₂ equivalent (other u x) = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (mk×ₚ u x)))

RawSelectEntryExtnRep : Raw SelectEntryExtnRep
RawSelectEntryExtnRep = RawSum (RawExtensionFields RawReasonCodeFields)
                        (RawSum (RawExtensionFields RawInvalidityDateFields)
                        (RawSum (RawExtensionFields RawCertIssuerFields)
                        (RawΣₚ₁ (RawExtensionFields RawOctetString)
                                    (λ _ u → T (not (ExtensionFields.getCrit u))))))

RawSelectEntryExtn : Raw SelectEntryExtn
RawSelectEntryExtn = Iso.raw equivalent RawSelectEntryExtnRep

RawEntryExtensions : Raw EntryExtensions
RawEntryExtensions = RawTLV _ (RawBoundedSequenceOf (RawTLV _ RawSelectEntryExtn) 1)
