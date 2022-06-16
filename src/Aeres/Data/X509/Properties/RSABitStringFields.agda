{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Data.X509.Properties.BitstringValue as BitstringProps
open import Aeres.Data.X690-DER
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.RSABitStringFields where

open Base256
open Aeres.Grammar.Definitions Dig
open ≡-Reasoning

@0 nonnesting : NonNesting X509.RSABitStringFields
nonnesting x a₁ a₂ = foo
  where
  v2& :  ∀ {bs} → X509.RSABitStringFields bs → (&ₚ (_≡ [ # 0 ]) X509.RSAPkInts) bs
  v2& (X509.mkRSABitStringFields self rsane bs≡) = Aeres.Grammar.Definitions.mk&ₚ refl rsane bs≡
  foo = NonNesting&ₚ (λ xs₁++ys₁≡xs₂++ys₂ a₃ a₄ → trans a₃ (sym a₄)) TLV.nonnesting x (v2& a₁) (v2& a₂)


equivalent : Equivalent (&ₚ (_≡ [ # 0 ]) X509.RSAPkInts) X509.RSABitStringFields
proj₁ equivalent (Aeres.Grammar.Definitions.mk&ₚ refl sndₚ₁ bs≡) = X509.mkRSABitStringFields self sndₚ₁ bs≡
proj₂ equivalent (X509.mkRSABitStringFields self rsane bs≡) = Aeres.Grammar.Definitions.mk&ₚ refl rsane bs≡

postulate
  @0 unambiguous : Unambiguous X509.RSABitStringFields
