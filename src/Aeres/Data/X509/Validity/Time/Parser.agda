open import Aeres.Binary
open import Aeres.Data.X509.Validity.Time.Properties
open import Aeres.Data.X509.Validity.Time.TCB
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Time.GeneralizedTime
open import Aeres.Data.X690-DER.Time.UTCTime
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties

module Aeres.Data.X509.Validity.Time.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Sum         UInt8

parse : Parser (Logging ∘ Dec) Time
parse =
  parseEquivalent equivalent
    (parseSum GeneralizedTime.parse UTCTime.parse)
