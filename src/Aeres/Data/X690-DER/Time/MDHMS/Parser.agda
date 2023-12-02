open import Aeres.Binary
open import Aeres.Data.X690-DER.Time.Day
open import Aeres.Data.X690-DER.Time.Hour
open import Aeres.Data.X690-DER.Time.Minute
open import Aeres.Data.X690-DER.Time.MDHMS.TCB
open import Aeres.Data.X690-DER.Time.Month
open import Aeres.Data.X690-DER.Time.TimeType
open import Aeres.Data.X690-DER.Time.Sec
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X690-DER.Time.MDHMS.Parser where

open Aeres.Grammar.Parallel UInt8
open Aeres.Grammar.Parser   UInt8
open Aeres.Grammar.Seq      UInt8

parse : Parser (Logging ∘ Dec) MDHMS
parse = parseEquivalent equivalent p
  where
  p : Parser (Logging ∘ Dec) MDHMSRep
  p =  parse& (Seq.nosubstringsᵈ TimeType.nosubstrings TimeType.unambiguous
                (λ a → Parallel.nosubstrings₁ TimeType.nosubstrings))
      (parse&ᵈ TimeType.nosubstrings TimeType.unambiguous Month.parse λ r a →
        parseSigma TimeType.nosubstrings TimeType.unambiguous Day.parse (λ _ → erased? (_ ≤? _)))
      (parse& TimeType.nosubstrings Hour.parse
      (parse& TimeType.nosubstrings Minute.parse
                                      Sec.parse))
