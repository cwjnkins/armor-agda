{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.DirectoryString.TCB
open import Aeres.Data.X690-DER.OID.Properties
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X509.RDN.ATV.OIDs
open import Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Aeres.Data.X690-DER.Strings.IA5String.TCB
open import Aeres.Data.X690-DER.Strings.PrintableString.TCB
  renaming (size to sizePrintableString)
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.RDN.ATV.TCB where

open Aeres.Grammar.Definitions UInt8

{-
-- https://datatracker.ietf.org/doc/html/rfc5280#appendix-A.1
--
-- AttributeType           ::= OBJECT IDENTIFIER
--
-- AttributeValue          ::= ANY -- DEFINED BY AttributeType
--
-- AttributeTypeAndValue   ::= SEQUENCE {
--         type    AttributeType,
--         value   AttributeValue }
-}

ATVParam : {@0 bs : List UInt8} → (o : OID bs) → Dec ((-, TLV.val o) ∈ Supported) → @0 List UInt8 → Set
-- Default
ATVParam o (no ¬p) = DirectoryString
-- X520 DN Qualifier
ATVParam o (yes (here px)) = PrintableString
-- X520 Country Name
ATVParam o (yes (there (here px))) = Σₚ PrintableString (TLVSizeBounded sizePrintableString 2 2)
-- X520 serial number
ATVParam o (yes (there (there (here px)))) = PrintableString
-- PCKS-9 email address
ATVParam o (yes (there (there (there (here px))))) = IA5String

ATV = DefinedByOID λ o → ATVParam o ((-, TLV.val o) ∈? Supported)

