open import Armor.Binary
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.Properties
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module  Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.Parser where

open Armor.Grammar.Parser   UInt8
open Armor.Grammar.Parallel UInt8

private
  here' = "X509: CRL: CertList: TBSCertList: RevokedCertificates: EntryExtension: ReasonCode"

parseReasonCodeFields : Parser (Logging ∘ Dec) ReasonCodeFields
parseReasonCodeFields = parseTLV _ here' _
  (parseExactLength nosubstrings (tell $ here' String.++ ": underflow")
     (parseSigma TLV.nosubstrings (TLV.unambiguous Int.unambiguousValue)
       (parseTLV Tag.Enum here' _ (Int.parseValue here'))
       λ i → erased? (_ ∈? _)))
