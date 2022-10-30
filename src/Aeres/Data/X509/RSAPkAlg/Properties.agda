{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Data.X509.PkOID as PkOID
open import Aeres.Data.X509.RSAPkAlg.TCB
open import Aeres.Data.X690-DER
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.RSAPkAlg.Properties where

open Aeres.Grammar.Definitions UInt8
open import Aeres.Grammar.Sum UInt8
open import Aeres.Grammar.Properties  UInt8
open ≡-Reasoning

Rep = &ₚ (_≡ PkOID.RsaEncPk) Null

equivalent : Equivalent Rep RSAPkAlgFields
proj₁ equivalent (mk&ₚ refl n refl) = mkRSAPkAlgFields self n refl
proj₂ equivalent (mkRSAPkAlgFields self n refl) = mk&ₚ refl n refl

iso : Iso Rep RSAPkAlgFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ refl n refl) = refl
proj₂ (proj₂ iso) (mkRSAPkAlgFields self n refl) = refl

@0 nonnesting : NonNesting RSAPkAlgFields
nonnesting =
  equivalent-nonnesting equivalent
    (NonNesting&ₚ (λ where _ refl refl → refl)
      TLV.nonnesting)

@0 unambiguous : Unambiguous RSAPkAlgFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ ≡-unique (λ where _ refl refl → refl)
      (TLV.unambiguous (λ where refl refl → refl)))
