open import Armor.Binary
open import Armor.Data.X509.Extension.AIA.TCB
open import Armor.Data.X509.Extension.AKI.TCB
open import Armor.Data.X509.Extension.IAN.TCB
open import Armor.Data.X509.Extension.CRLDistPoint.TCB
open import Armor.Data.X509.CRL.Extension.CRLN.TCB
open import Armor.Data.X509.CRL.Extension.DCRLI.TCB
open import Armor.Data.X509.CRL.Extension.IDP.TCB
import      Armor.Data.X509.CRL.Extension.TCB.OIDs as OIDs
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

module Armor.Data.X509.CRL.Extension.TCB where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Option.TCB   UInt8
open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Sum.TCB      UInt8
open Armor.Grammar.Seq         UInt8

-- id-ce-freshestCRL OBJECT IDENTIFIER ::=  { id-ce 46 }
-- FreshestCRL ::= CRLDistributionPoints

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
supportedExtensions =
    OIDs.AKILit ∷ OIDs.IANLit ∷ OIDs.CRLNLit ∷ OIDs.DCRLILit ∷ OIDs.IDPLit ∷ OIDs.FCRLLit ∷ [ OIDs.AIALit ]

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

ExtensionFieldAKI     = ExtensionFields (_≡ OIDs.AKILit )    AKIFields
ExtensionFieldIAN     = ExtensionFields (_≡ OIDs.IANLit )    IANFields
ExtensionFieldCRLN    = ExtensionFields (_≡ OIDs.CRLNLit )   CRLNFields
ExtensionFieldDCRLI   = ExtensionFields (_≡ OIDs.DCRLILit )  DCRLIFields
ExtensionFieldIDP     = ExtensionFields (_≡ OIDs.IDPLit )    IDPFields
ExtensionFieldFCRL    = ExtensionFields (_≡ OIDs.FCRLLit)    CRLDistFields
ExtensionFieldAIA     = ExtensionFields (_≡ OIDs.AIALit )    AIAFields
ExtensionFieldUnsupported = ExtensionFields (False ∘ (_∈? supportedExtensions)) OctetString

data SelectExtn : @0 List UInt8 → Set where
  akiextn  : ∀ {@0 bs} → ExtensionFieldAKI bs → SelectExtn bs 
  ianextn  : ∀ {@0 bs} → ExtensionFieldIAN bs → SelectExtn bs 
  crlnextn   : ∀ {@0 bs} → ExtensionFieldCRLN bs  → SelectExtn bs 
  dcrliextn  : ∀ {@0 bs} → ExtensionFieldDCRLI bs → SelectExtn bs 
  idpextn   : ∀ {@0 bs} → ExtensionFieldIDP bs  → SelectExtn bs 
  fcrlextn  : ∀ {@0 bs} → ExtensionFieldFCRL bs → SelectExtn bs 
  aiaextn  : ∀ {@0 bs} → ExtensionFieldAIA bs → SelectExtn bs 
-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2
-- A certificate-using system MUST reject the certificate if it encounters a critical Extension
-- it does not recognize or a critical Extension that contains information that it cannot process.
  other    : ∀ {@0 bs} → (u : ExtensionFieldUnsupported bs) → T (not (ExtensionFields.getCrit u)) → SelectExtn bs

Extension : @0 List UInt8 → Set
Extension xs = TLV Tag.Sequence SelectExtn xs

ExtensionsSeq : @0 List UInt8 → Set
ExtensionsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf Extension) xs

Extensions : @0 List UInt8 → Set
Extensions xs = TLV Tag.AA0  ExtensionsSeq xs
