open import Aeres.Binary
  renaming (module Base64 to B64)
open import Aeres.Data.Base64
open import Aeres.Data.PEM.RFC5234.TCB
import      Aeres.Data.PEM.RFC5234.Properties
  as RFC5234
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.PEM.RFC5234.Parser where

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.Parser      Char
open Aeres.Grammar.Sum         Char

parseMaxEOL : LogDec.MaximalParser EOL
parseMaxEOL =
  LogDec.equivalent RFC5234.EOL.equiv
    (parseMaxSum
      (LogDec.nonnesting (λ where _ (─ refl) (─ refl) → refl)
        (parseLitE (tell "parseCRLF: EOF") silent _))
      (parseMaxSum
        (LogDec.nonnesting (λ where _ (─ refl) (─ refl) → refl)
          (parseLitE (tell "parseCR: EOF") silent _))
          (LogDec.nonnesting (λ where _ (─ refl) (─ refl) → refl)
            (parseLitE (tell "parseLF: EOF") silent _))))

