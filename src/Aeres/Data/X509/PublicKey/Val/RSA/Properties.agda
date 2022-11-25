{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.TCB
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Properties where

open Aeres.Grammar.Definitions UInt8

@0 nonnesting : NonNesting RSABitStringFields
nonnesting x a₁ a₂ = foo
  where
  v2& :  ∀ {bs} → RSABitStringFields bs → (&ₚ (_≡ [ # 0 ]) RSAPkInts) bs
  v2& (mkRSABitStringFields self rsane bs≡) = Aeres.Grammar.Definitions.mk&ₚ refl rsane bs≡
  foo = NonNesting&ₚ (λ xs₁++ys₁≡xs₂++ys₂ a₃ a₄ → trans a₃ (sym a₄)) TLV.nonnesting x (v2& a₁) (v2& a₂)


equivalent : Equivalent (&ₚ (_≡ [ # 0 ]) RSAPkInts) RSABitStringFields
proj₁ equivalent (Aeres.Grammar.Definitions.mk&ₚ refl sndₚ₁ bs≡) = mkRSABitStringFields self sndₚ₁ bs≡
proj₂ equivalent (mkRSABitStringFields self rsane bs≡) = Aeres.Grammar.Definitions.mk&ₚ refl rsane bs≡

iso : Iso (&ₚ (_≡ [ # 0 ]) RSAPkInts) RSABitStringFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Aeres.Grammar.Definitions.mk&ₚ refl sndₚ₁ refl) = refl
proj₂ (proj₂ iso) (mkRSABitStringFields self rsane refl) = refl

@0 unambiguous : Unambiguous RSABitStringFields
unambiguous = isoUnambiguous iso
                (unambiguous&ₚ
                  ≡-unique
                  (λ where _ refl refl → refl)
                  (TLV.unambiguous Ints.unambiguous))
