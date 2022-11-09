{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Ints.Properties where

open Aeres.Grammar.Definitions UInt8

@0 nonnesting : NonNesting RSAPkIntsFields
nonnesting x a₁ a₂ = foo
  where
  v2& :  ∀ {bs} → RSAPkIntsFields bs → (&ₚ Int Int) bs
  v2& (mkRSAPkIntsFields n e bs≡) = mk&ₚ n e bs≡
  foo = NonNesting&ₚ TLV.nonnesting TLV.nonnesting x (v2& a₁) (v2& a₂)

equivalent : Equivalent (&ₚ Int Int) RSAPkIntsFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkRSAPkIntsFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkRSAPkIntsFields fstₚ₁ sndₚ₁ bs≡) = mk&ₚ fstₚ₁ sndₚ₁ bs≡

iso : Iso (&ₚ Int Int) RSAPkIntsFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Aeres.Grammar.Definitions.mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkRSAPkIntsFields nval eval bs≡) = refl

@0 unambiguous : Unambiguous RSAPkIntsFields
unambiguous = isoUnambiguous iso
                (unambiguous&ₚ
                (TLV.unambiguous λ {xs} → Int.unambiguous{xs})
                TLV.nonnesting
                (TLV.unambiguous λ {xs} → Int.unambiguous{xs}))
