{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.Primitives where

open Base256
open import Aeres.Grammar.Definitions Dig

module BoolValue where
  nonempty : NonEmpty Generic.BoolValue
  nonempty () refl

  @0 nonnesting : NonNesting Generic.BoolValue
  nonnesting x (Generic.mkBoolValue v b vᵣ bs≡) (Generic.mkBoolValue v₁ b₁ vᵣ₁ bs≡₁) =
    proj₁ $ Lemmas.length-++-≡ _ _ _ _ x (trans (cong length bs≡) (cong length (sym bs≡₁)))

module IntegerValue where
  @0 unambiguous : Unambiguous Generic.IntegerValue
  unambiguous{xs} (Generic.mkIntegerValue ._ refl) (Generic.mkIntegerValue val₁ bs≡₁) =
    ≡-elim (λ {val₁} bs≡ → Generic.mkIntegerValue (twosComplement xs) refl ≡ Generic.mkIntegerValue val₁ bs≡)
      refl bs≡₁
