{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.DirectoryString.TCB
open import Aeres.Data.X690-DER.OID.Properties
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X509.Name.RDN.ATV.OIDs
open import Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Aeres.Data.X690-DER.Strings.IA5String.TCB
open import Aeres.Data.X690-DER.Strings.PrintableString.TCB
  renaming (size to sizePrintableString)
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
open import Aeres.Prelude

module Aeres.Data.X509.Name.RDN.ATV.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#appendix-A.1
-- AttributeType           ::= OBJECT IDENTIFIER
--
-- AttributeValue          ::= ANY -- DEFINED BY AttributeType
--
-- AttributeTypeAndValue   ::= SEQUENCE {
--         type    AttributeType,
--         value   AttributeValue }

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

ATVParam' : AnyDefinedByOID
ATVParam' o = ATVParam o ((-, TLV.val o) ∈? Supported)

ATV = DefinedByOID λ o → ATVParam o ((-, TLV.val o) ∈? Supported)

pattern mkATVFields o p bs≡ = mkOIDDefinedFields o p bs≡

RawATVParam : Raw₁ RawOID ATVParam'
toRawATVParam : ∀ {@0 bs₁} {o : OID bs₁} {@0 bs₂} → (o? : Dec ((-, TLV.val o) ∈ Supported)) → ATVParam o o? bs₂ → Raw₁.D RawATVParam (Raw.to RawOID o)

Raw₁.D RawATVParam ro =
    Raw.D RawDirectoryString
  ⊎ Raw.D RawPrintableString
  ⊎ Raw.D (RawΣₚ₁ RawPrintableString (TLVSizeBounded sizePrintableString 2 2))
  ⊎ Raw.D RawPrintableString
  ⊎ Raw.D RawIA5String
Raw₁.to RawATVParam o {bs} = toRawATVParam ((-, TLV.val o) ∈? Supported)

toRawATVParam {o} (no ¬p) p =
  inj₁ (Raw.to RawDirectoryString p)
toRawATVParam {o} (yes (here px)) p =
  inj₂ (inj₁ (Raw.to RawPrintableString p))
toRawATVParam {o} (yes (there (here px))) p =
  inj₂ (inj₂ (inj₁ (Raw.to (RawΣₚ₁ RawPrintableString (TLVSizeBounded sizePrintableString 2 2)) p)))
toRawATVParam {o} (yes (there (there (here px)))) p =
  inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁ $ Raw.to RawPrintableString p
toRawATVParam {o} (yes (there (there (there (here px))))) p =
  inj₂ (inj₂ (inj₂ (inj₂ $ Raw.to RawIA5String p)))

RawATV : Raw ATV
RawATV = RawDefinedByOID RawATVParam
