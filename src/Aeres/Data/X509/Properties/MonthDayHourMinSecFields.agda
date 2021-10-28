{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Properties.TLV as TLVprops
open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.MonthDayHourMinSecFields where

open Base256
open import Aeres.Grammar.Definitions Dig

@0 nonnesting : NonNesting Generic.MonthDayHourMinSecFields
nonnesting {xs₁ = xs₁} {xs₂ = xs₂} x (Generic.mkMDHMSFields mon monRange day dayRange hour hourRange min minRange sec secRange bs≡) (Generic.mkMDHMSFields mon₁ monRange₁ day₁ dayRange₁ hour₁ hourRange₁ min₁ minRange₁ sec₁ secRange₁ bs≡₁)
  with Lemmas.length-++-≡ xs₁ _ xs₂ _ x (trans₀ (cong length bs≡) (cong length (sym bs≡₁)))
... | fst , snd = fst
