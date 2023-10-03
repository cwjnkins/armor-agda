{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Time.Year.TCB
import      Aeres.Data.X690-DER.Time.TimeType.Parser as TimeType
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X690-DER.Time.Year.Parser where

open Aeres.Grammar.Parser UInt8

parse₂ : Parser (Logging ∘ Dec) Year₂
parse₂ = TimeType.parse _ _ _

parse₄ : Parser (Logging ∘ Dec) Year₄
parse₄ = TimeType.parse _ _ _
