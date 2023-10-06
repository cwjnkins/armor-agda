{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames.Properties
open import Aeres.Data.X509.GeneralNames.GeneralName
open import Aeres.Data.X509.GeneralNames.GeneralName.Parser
open import Aeres.Data.X509.GeneralNames.TCB
open import Aeres.Data.X509.Name
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.GeneralNames.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Sum         UInt8

private
  here' = "X509: GeneralNames"

parseGeneralNamesElems : ∀ n → Parser (Logging ∘ Dec) (ExactLength GeneralNamesElems n)
parseGeneralNamesElems n =
    parseBoundedSequenceOf here' _ GeneralName.nonempty GeneralName.nosubstrings parseGeneralName  n 1

parseGeneralNames : Parser (Logging ∘ Dec) GeneralNames
parseGeneralNames = parseTLV _ here' _ parseGeneralNamesElems
