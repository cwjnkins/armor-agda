open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Properties
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: Extension: CRLDistPoint: DistPoint"

parseDistPointFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength DistPointFields n)
parseDistPointFields n =
  parseEquivalent
    (Parallel.equivalent₁ equivalentDistPointFields)
    (parse₂Option₃ here'
      TLV.nosubstrings TLV.nosubstrings TLV.nosubstrings
      (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())
      (parseTLV Tag.AA0 (here' String.++ " (name)") DistPointNameChoice
        (parseExactLength Name.nosubstrings (tell $ here' String.++ ": underflow")
          parseDistPointNameChoice))
      (parseTLV Tag.A81 (here' String.++ " (reason flags)") _ parseBitstringValue)
      (parseTLV Tag.AA2 (here' String.++ " (CRL issuer)") _ parseGeneralNamesElems)
      n)

parseDistPoint : Parser (Logging ∘ Dec) DistPoint
parseDistPoint =
  parseTLV _ here' _ parseDistPointFields
