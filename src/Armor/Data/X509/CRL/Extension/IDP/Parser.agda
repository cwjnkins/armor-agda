open import Armor.Binary
open import Armor.Data.X509.CRL.Extension.IDP.TCB
open import Armor.Data.X509.CRL.Extension.IDP.Properties as Prop
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Properties
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Boool
open import Armor.Data.X690-DER.BitString.Parser as BitString
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Option
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.CRL.Extension.IDP.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: CRL: CertList: TBSCertList: Extension: IDP"


parseIDPFieldsSeqFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength IDPFieldsSeqFields n)
parseIDPFieldsSeqFields n =
  parseEquivalent (Parallel.equivalent₁ equivalentIDPFieldsSeqFields) {!Sequence.parseOption₂Default₄!}


--   where
--   p :  Parser (Logging ∘ Dec) (ExactLength Rep n)
--   p = {!!}

-- Sequence.parseOption₂Default₄ _ _ _ _ here' Prop.uaRep
--         (parseTLV Tag.AA0 (here' String.++ " (name)") DistPointNameChoice
--                            (parseExactLength Name.nosubstrings (tell $ here' String.++ ": underflow")
--                             parseDistPointNameChoice))
--         (parseTLV Tag.A81 here' _ (parseExactLength Boool.nosubstrings (tell $ here' String.++ ": underflow") Boool.parseValue))
--         (parseTLV Tag.A82 here' _ (parseExactLength Boool.nosubstrings (tell $ here' String.++ ": underflow") Boool.parseValue))
--         (parseTLV Tag.A83 here' _ parseBitstringValue)
--         (parseTLV Tag.A84 here' _ (parseExactLength Boool.nosubstrings (tell $ here' String.++ ": underflow") Boool.parseValue))
--         (parseTLV Tag.A85 here' _ (parseExactLength Boool.nosubstrings (tell $ here' String.++ ": underflow") Boool.parseValue))
--         n


parseIDPFields : Parser (Logging ∘ Dec) IDPFields
parseIDPFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
      (parseTLV _ here' _
        parseIDPFieldsSeqFields))
