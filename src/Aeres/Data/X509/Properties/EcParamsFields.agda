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

module Aeres.Data.X509.Properties.EcParamsFields where

open Base256
open Aeres.Grammar.Definitions Dig
open ≡-Reasoning


postulate
  nonnesting : NonNesting X509.EcParamsFields

equivalent : Equivalent (&ₚ (_≡ # 2 ∷ # 1 ∷ [ # 1 ]) (&ₚ X509.FieldID (&ₚ X509.Curve (&ₚ OctetString (&ₚ Int (Option Int)))))) X509.EcParamsFields
proj₁ equivalent (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ sndₚ₁ refl) refl) refl) refl) bs≡) = X509.mkEcParamsFields fstₚ₁ fstₚ₂ fstₚ₃ fstₚ₄ fstₚ₅ sndₚ₁ bs≡
proj₂ equivalent (X509.mkEcParamsFields fstₚ₁ fstₚ₂ fstₚ₃ fstₚ₄ fstₚ₅ sndₚ₁ bs≡) = mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ sndₚ₁ refl) refl) refl) refl) bs≡
