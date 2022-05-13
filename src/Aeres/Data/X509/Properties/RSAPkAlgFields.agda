{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Data.X509.Properties.TLV            as TLVprops
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.RSAPkAlgFields where

open Base256
open Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum Dig
open import Aeres.Grammar.Properties  Dig
open ≡-Reasoning


equivalent : Equivalent (&ₚ (_≡ X509.PKOID.RsaEncPk) (_≡ X509.ExpNull)) X509.RSAPkAlgFields
proj₁ equivalent (mk&ₚ refl refl refl) = X509.mkRSAPkAlgFields self self refl
proj₂ equivalent (X509.mkRSAPkAlgFields self self refl) = mk&ₚ refl refl refl

postulate
  @0 nonnesting : NonNesting X509.RSAPkAlgFields
