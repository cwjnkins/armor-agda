{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.Name.RDN.ATV
open import Aeres.Data.X509.Name.RDN.Properties
open import Aeres.Data.X509.Name.RDN.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Name.RDN.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: Name: RDNSequence: RDN"

parse : Parser (Logging ∘ Dec) RDN
parse = parseTLV _ here' _ λ n →
          parseBoundedSequenceOf (here' String.++ " (elems)") _ TLV.nonempty TLV.nosubstrings ATV.parse n 1
