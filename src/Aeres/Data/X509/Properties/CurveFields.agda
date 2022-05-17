{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Data.X509.Properties.BitstringValue as BitstringProps
import      Aeres.Data.X509.Properties.TLV            as TLVprops
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.CurveFields where

open Base256
open Aeres.Grammar.Definitions Dig
open ≡-Reasoning


postulate
  nonnesting : NonNesting X509.CurveFields

equivalent : Equivalent (&ₚ OctetString (&ₚ OctetString (Option BitString))) X509.CurveFields
proj₁ equivalent (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) bs≡) = X509.mkCurveFields fstₚ₁ fstₚ₂ sndₚ₁ bs≡
proj₂ equivalent (X509.mkCurveFields fstₚ₁ fstₚ₂ sndₚ₁ bs≡) = mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) bs≡

