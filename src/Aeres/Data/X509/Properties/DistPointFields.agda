{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.DistPointNameChoice as DPNCProps
import      Aeres.Data.X509.Properties.GeneralName         as GNProps
import      Aeres.Data.X509.Properties.Primitives          as PrimProps
open import Aeres.Data.X690-DER
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.DistPointFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties Dig

equivalent : Equivalent (&ₚ (Option X509.DistPointName) (&ₚ (Option X509.ReasonFlags) (Option X509.CrlIssuer))) X509.DistPointFields
proj₁ equivalent (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = X509.mkDistPointFields fstₚ₁ fstₚ₂ sndₚ₁ refl
proj₂ equivalent (X509.mkDistPointFields crldp crldprsn crlissr bs≡) = mk&ₚ crldp (mk&ₚ crldprsn crlissr refl) bs≡

iso : Iso (&ₚ (Option X509.DistPointName) (&ₚ (Option X509.ReasonFlags) (Option X509.CrlIssuer))) X509.DistPointFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (X509.mkDistPointFields crldp crldprsn crlissr refl) = refl

@0 unambiguous : Unambiguous X509.DistPointFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.option₃&₂
      (TLV.unambiguous DPNCProps.unambiguous) TLV.nonnesting TLV.nonempty
      (TLV.unambiguous PrimProps.BitstringValue.unambiguous) TLV.nonnesting TLV.nonempty
      (TLV.unambiguous GNProps.GeneralNamesElems.unambiguous) TLV.nonempty
      (TLV.noconfusion (λ ())) (TLV.noconfusion λ ()) (TLV.noconfusion λ ()))
