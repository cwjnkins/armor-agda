{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X509.Name.Properties
import      Aeres.Data.X509.Name.RDN.Parser as RDN
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
parse = parseTLV _ here' _ (parseSequenceOf (here' String.++ " (elems)") _ TLV.nonempty TLV.nosubstrings RDN.parse)
