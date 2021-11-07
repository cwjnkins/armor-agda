{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude

module Aeres.Data.X509.Properties.Extension where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum Dig

module SelectExtn where
  postulate
    equivalent : Equivalent
                   (Sum (X509.ExtensionFields X509.ExtensionOID.AKI X509.AKIFields)
                   (Sum (X509.ExtensionFields X509.ExtensionOID.SKI     X509.SKIFields)
                   (Sum (X509.ExtensionFields X509.ExtensionOID.KU      X509.KUFields)
                   (Sum (X509.ExtensionFields X509.ExtensionOID.EKU     X509.EKUFields)
                   (Sum (X509.ExtensionFields X509.ExtensionOID.BC      X509.BCFields)
                   (Sum (X509.ExtensionFields X509.ExtensionOID.IAN     X509.IANFields)
                   (Sum (X509.ExtensionFields X509.ExtensionOID.SAN     X509.SANFields)
                   (Sum (X509.ExtensionFields X509.ExtensionOID.CPOL    X509.CertPolFields)
                   (Sum (X509.ExtensionFields X509.ExtensionOID.CRLDIST X509.CRLDistFields)
                        (X509.ExtensionFields X509.ExtensionOID.AIA     X509.AIAFields))))))))))
                   X509.SelectExtn

equivalent : ∀ {@0 lit} {@0 A : @0 List Dig → Set}
             → Equivalent
                 (&ₚ (Generic.OID ×ₚ (_≡ lit))
                     (&ₚ (Option Generic.Boool)
                         A))
                 (X509.ExtensionFields lit A)
proj₁ equivalent (mk&ₚ (mk×ₚ fstₚ₁ sndₚ₁ refl) (mk&ₚ fstₚ₂ sndₚ₂ refl) refl) =
  X509.mkExtensionFields fstₚ₁ sndₚ₁ fstₚ₂ sndₚ₂ refl
proj₂ equivalent (X509.mkExtensionFields extnId extnId≡ crit extension refl) =
  mk&ₚ (mk×ₚ extnId (‼ extnId≡) refl) (mk&ₚ crit extension refl) refl
