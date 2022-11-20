{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Properties.RDNATVFields where

open Aeres.Grammar.Definitions UInt8

iso : Iso (&ₚ OID DirectoryString) X509.RDNATVFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkRDNATVFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (X509.mkRDNATVFields oid val bs≡) = mk&ₚ oid val bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkRDNATVFields oid val bs≡) = refl

@0 unambiguous : Unambiguous X509.RDNATVFields
unambiguous = isoUnambiguous iso (unambiguous&ₚ OID.unambiguous TLV.nonnesting DirectoryString.unambiguous)
