{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.AlgorithmIdentifier.Properties
  (@0 P : {@0 bs : List UInt8} → OID bs → List UInt8 → Set)
  where

open Aeres.Grammar.Definitions UInt8

Rep : @0 List UInt8 → Set
Rep = &ₚᵈ OID λ bs → P {bs}

equiv : Equivalent Rep (AlgorithmIdentifierFields P)
proj₁ equiv (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkAlgIDFields fstₚ₁ sndₚ₁ bs≡
proj₂ equiv (mkAlgIDFields algOID param bs≡) = mk&ₚ algOID param bs≡

iso : Iso Rep (AlgorithmIdentifierFields P)
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkAlgIDFields algOID param bs≡) = refl
