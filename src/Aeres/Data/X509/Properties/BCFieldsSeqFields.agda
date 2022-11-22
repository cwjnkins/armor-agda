{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.Properties.BCFieldsSeqFields where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8


equivalent : Equivalent (&ₚ (Option Boool) (Option Int)) BCFieldsSeqFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkBCFieldsSeqFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkBCFieldsSeqFields bcca bcpathlen bs≡) = mk&ₚ bcca bcpathlen bs≡

iso : Iso (&ₚ (Option Boool) (Option Int)) BCFieldsSeqFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkBCFieldsSeqFields bcca bcpathlen bs≡) = refl

@0 unambiguous : Unambiguous BCFieldsSeqFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.option₂&₁
      (TLV.unambiguous Boool.unambiguous) TLV.nonnesting TLV.nonempty
      (TLV.unambiguous (λ {xs} → Int.unambiguous{xs})) TLV.nonempty
      (TLV.noconfusion λ ()))
