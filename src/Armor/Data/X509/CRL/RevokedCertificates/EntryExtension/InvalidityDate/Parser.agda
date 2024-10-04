open import Armor.Binary
open import  Armor.Data.X690-DER.Time.GeneralizedTime
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.InvalidityDate.TCB
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module  Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.InvalidityDate.Parser where

open Armor.Grammar.Parser   UInt8
open Armor.Grammar.Parallel UInt8

private
  here' = "X509: CRL : EntryExtension: InvalidityDate"

parseInvalidityDateFields : Parser (Logging ∘ Dec) InvalidityDateFields
parseInvalidityDateFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
      GeneralizedTime.parse)
