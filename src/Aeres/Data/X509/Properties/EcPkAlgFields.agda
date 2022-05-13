{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Data.X509.Properties.TLV            as TLVprops
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.EcPkAlgFields where

open Base256
open Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum Dig
open ≡-Reasoning

-- equivalent : Equivalent (&ₚ (_≡ X509.PKOID.EcPk) X509.EcPkAlgParams) X509.EcPkAlgFields
-- proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkEcPkAlgFields fstₚ₁ sndₚ₁ bs≡
-- proj₂ equivalent (X509.mkEcPkAlgFields ≡pkOID param bs≡) = mk&ₚ ≡pkOID param bs≡


postulate
  @0 nonnesting : NonNesting X509.EcPkAlgFields
