open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X509.Name.Properties
open import Aeres.Data.X509.Name.RDN
open import Aeres.Data.X509.Name.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Name.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: Name"

parse : Parser (Logging ∘ Dec) Name
parse = RDN.parseSequence
