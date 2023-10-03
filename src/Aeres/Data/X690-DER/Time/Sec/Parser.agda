{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Time.Sec.TCB
import      Aeres.Data.X690-DER.Time.TimeType.Parser as TimeType
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X690-DER.Time.Sec.Parser where

open Aeres.Grammar.Parser UInt8

parse : Parser (Logging ∘ Dec) Sec
parse = TimeType.parse _ _ _
