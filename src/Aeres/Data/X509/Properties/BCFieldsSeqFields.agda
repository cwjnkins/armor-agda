{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.Primitives as PrimProps
open import Aeres.Data.X690-DER
open import Aeres.Prelude

module Aeres.Data.X509.Properties.BCFieldsSeqFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig


equivalent : Equivalent (&ₚ (Option Generic.Boool) (Option Int)) X509.BCFieldsSeqFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkBCFieldsSeqFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (X509.mkBCFieldsSeqFields bcca bcpathlen bs≡) = mk&ₚ bcca bcpathlen bs≡

iso : Iso (&ₚ (Option Generic.Boool) (Option Int)) X509.BCFieldsSeqFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkBCFieldsSeqFields bcca bcpathlen bs≡) = refl

@0 unambiguous : Unambiguous X509.BCFieldsSeqFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.option₂&₁
      (TLV.unambiguous PrimProps.BoolValue.unambiguous) TLV.nonnesting TLV.nonempty
      (TLV.unambiguous (λ {xs} → PrimProps.IntegerValue.unambiguous{xs})) TLV.nonempty
      (TLV.noconfusion λ ()))
