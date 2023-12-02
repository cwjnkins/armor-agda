open import Aeres.Binary
open import Aeres.Data.X509.TBSCert.Version.Properties
open import Aeres.Data.X509.TBSCert.Version.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.TBSCert.Version.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: TBSCert: Version"

parse : Parser (Logging ∘ Dec) Version
parse =
  parseSigma TLV.nosubstrings Int.unambiguous (Int.parse here')
    (λ i → erased? (_ ∈? _))

parse[0]Explicit : Parser (Logging ∘ Dec) [0]ExplicitVersion
parse[0]Explicit =
  parseTLV _ here' _
    (parseExactLength nosubstrings (tell $ here' String.++ " (nondefault): length mismatch")
      parse)
