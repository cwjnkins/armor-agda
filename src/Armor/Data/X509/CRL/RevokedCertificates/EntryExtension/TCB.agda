open import Armor.Binary
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.InvalidityDate.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.CertIssuer.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.TCB
import      Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB.OIDs as OIDs
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
supportedExtensions = OIDs.REASONLit ∷ OIDs.INVALIDITYLit ∷ [ OIDs.CERTISSUERLit ]

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

ExtensionFieldCRLReason       = ExtensionFields (_≡ OIDs.REASONLit)  ReasonCodeFields
ExtensionFieldInvalidityDate  = ExtensionFields (_≡ OIDs.INVALIDITYLit) InvalidityDateFields
ExtensionFieldCertIssuer      = ExtensionFields (_≡ OIDs.CERTISSUERLit)  CertIssuerFields
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
