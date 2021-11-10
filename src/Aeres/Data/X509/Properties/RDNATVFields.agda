{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude
import Aeres.Data.X509.Properties.OID as OIDProps
import Aeres.Data.X509.Properties.TLV as TLVProps
import Aeres.Data.X509.Properties.DirectoryString as DirectoryStringProps

module Aeres.Data.X509.Properties.RDNATVFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open ≡-Reasoning

iso : Iso (&ₚ Generic.OID X509.DirectoryString) X509.RDNATVFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkRDNATVFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (X509.mkRDNATVFields oid val bs≡) = mk&ₚ oid val bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkRDNATVFields oid val bs≡) = refl

@0 unambiguous : Unambiguous X509.RDNATVFields
unambiguous = isoUnambiguous iso (unambiguous&ₚ OIDProps.unambiguous TLVProps.nonnesting DirectoryStringProps.unambiguous DirectoryStringProps.nonnesting)
