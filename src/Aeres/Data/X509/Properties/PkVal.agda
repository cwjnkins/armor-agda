{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.RSABitStringFields as RSAProps
import      Aeres.Data.X509.Properties.BitstringValue     as BitStringProps
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Properties.PkVal where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8
open ≡-Reasoning

Rep : (@0 o bs : List UInt8) → Set
Rep o =  Sum ((const $ o ≡ X509.PKOID.RsaEncPk)           ×ₚ X509.RSABitString)
        (Sum ((const $ o ≡ X509.PKOID.EcPk)               ×ₚ BitString)
             ((const $ False (o ∈? X509.PKOID.Supported)) ×ₚ BitString))

equivalent : (@0 o : _) → Equivalent (Rep o) (X509.PkVal o)
proj₁ (equivalent o) (inj₁ (mk×ₚ fstₚ₁ sndₚ₁ refl)) = X509.rsapkbits fstₚ₁ sndₚ₁
proj₁ (equivalent o) (inj₂ (inj₁ (mk×ₚ fstₚ₁ sndₚ₁ refl))) = X509.ecpkbits fstₚ₁ sndₚ₁
proj₁ (equivalent o) (inj₂ (inj₂ (mk×ₚ fstₚ₁ sndₚ₁ refl))) = X509.otherpkbits fstₚ₁ sndₚ₁
proj₂ (equivalent o) (X509.rsapkbits o≡ x) = inj₁ (mk×ₚ o≡ x refl)
proj₂ (equivalent o) (X509.ecpkbits o≡ x) = inj₂ (inj₁ (mk×ₚ o≡ x refl))
proj₂ (equivalent o) (X509.otherpkbits o∉ x) = inj₂ (inj₂ (mk×ₚ o∉ x refl))

iso : (@0 o : _) → Iso (Rep o) (X509.PkVal o)
proj₁ (iso o) = equivalent o
proj₁ (proj₂ (iso o)) (inj₁ (mk×ₚ fstₚ₁ sndₚ₁ refl)) = refl
proj₁ (proj₂ (iso o)) (inj₂ (inj₁ (mk×ₚ fstₚ₁ sndₚ₁ refl))) = refl
proj₁ (proj₂ (iso o)) (inj₂ (inj₂ (mk×ₚ fstₚ₁ sndₚ₁ refl))) = refl
proj₂ (proj₂ (iso o)) (X509.rsapkbits o≡ x) = refl
proj₂ (proj₂ (iso o)) (X509.ecpkbits o≡ x) = refl
proj₂ (proj₂ (iso o)) (X509.otherpkbits o∉ x) = refl

@0 unambiguous : (@0 o : _) → Unambiguous (X509.PkVal o)
unambiguous o =
  isoUnambiguous (iso o)
    (unambiguousSum
      (unambiguous×ₚ (λ _ → ≡-unique _) (TLV.unambiguous RSAProps.unambiguous))
      (unambiguousSum
        (unambiguous×ₚ (λ _ → ≡-unique _)
          (TLV.unambiguous BitStringProps.unambiguous))
        (unambiguous×ₚ (λ _ → T-unique _) (TLV.unambiguous BitStringProps.unambiguous))
          λ where
            xs₁++ys₁≡xs₂++ys₂ (mk×ₚ refl sndₚ₁ refl) (mk×ₚ fstₚ₂ sndₚ₂ refl) →
              contradiction (toWitness{Q = X509.PKOID.EcPk ∈? X509.PKOID.Supported} tt) (toWitnessFalse{Q = _ ∈? _} fstₚ₂))
      (NoConfusion.sumₚ{A = _ ×ₚ _}
        (λ where
          xs₁++ys₁≡xs₂++ys₂ (mk×ₚ refl sndₚ₁ refl) (mk×ₚ () sndₚ₂ refl))
        λ where
          xs₁++ys₁≡xs₂++ys₂ (mk×ₚ refl sndₚ₁ refl) (mk×ₚ fstₚ₂ sndₚ₂ refl) →
            contradiction{P = X509.PKOID.RsaEncPk ∈ X509.PKOID.Supported}
             (toWitness{Q = _ ∈? _}       tt)
              (toWitnessFalse{Q = _ ∈? _} fstₚ₂)))
