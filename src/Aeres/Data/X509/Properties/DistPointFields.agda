{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import Aeres.Data.X509.Properties.TLV as TLVprops
import Aeres.Data.X509.Properties.DistPointNameChoice as DPNCpros
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.DistPointFields where

open Base256
open import Aeres.Grammar.Definitions Dig


equivalent : Equivalent (&ₚ (Option X509.DistPointName) (&ₚ (Option X509.ReasonFlags) (Option X509.CrlIssuer))) X509.DistPointFields
proj₁ equivalent (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = X509.mkDistPointFields fstₚ₁ fstₚ₂ sndₚ₁ refl
proj₂ equivalent (X509.mkDistPointFields crldp crldprsn crlissr bs≡) = mk&ₚ crldp (mk&ₚ crldprsn crlissr refl) bs≡

postulate
  @0 unambiguous : Unambiguous X509.DistPointFields
