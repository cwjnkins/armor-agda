open import Armor.Binary
open import Armor.Data.X509.CRL.Extension.IDP.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.CRL.Extension.IDP.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: CRL: CertList: TBSCertList: Extension: IDP"

postulate
  parseIDPFields : Parser (Logging ∘ Dec) IDPFields
-- parseIDPFields =
--   parseTLV _ here' _
--     (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
--       (parseNonEmptySeq (here' String.++ ": elems") _ {!!} {!!}
--       (parseEquivalent {!!} {!!})))


-- parseIDPFields =
--   parseTLV _ here' _
--     (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
--       (parseNonEmptySeq (here' String.++ ": elems") _ {!!} {!!}
--       {!!}))
