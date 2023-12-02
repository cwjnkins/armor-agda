open import Aeres.Binary
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.Properties
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X509.Name
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Sum         UInt8

private
  here' = "X509: Extension: CRLDistPoint: DistPoint: Name"

parseFullName = parseTLV Tag.AA0 (here' String.++ ": full name") _ parseGeneralNamesElems

parseNameRTCrlIssuer : Parser (Logging ∘ Dec) NameRTCrlIssuer
parseNameRTCrlIssuer = Name.RDN.[ Tag.AA1 ]parse

parseDistPointNameChoice : Parser (Logging ∘ Dec) DistPointNameChoice
parseDistPointNameChoice =
  parseEquivalent equivalentDistPointNameChoice
    (parseSum parseFullName parseNameRTCrlIssuer)
