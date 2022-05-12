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

module Aeres.Data.X509.Properties.RSABitStringFields where

open Base256
open Aeres.Grammar.Definitions Dig
open ≡-Reasoning


postulate
  nonnesting : NonNesting X509.RSABitStringFields

equivalent : Equivalent (&ₚ (_≡ [ # 0 ]) X509.RSAPkInts) X509.RSABitStringFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkRSABitStringFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (X509.mkRSABitStringFields fstₚ₁ sndₚ₁ bs≡) = mk&ₚ fstₚ₁ sndₚ₁ bs≡