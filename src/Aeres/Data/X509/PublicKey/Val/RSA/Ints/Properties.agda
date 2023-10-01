{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Ints.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq         UInt8

@0 nosubstrings : NoSubstrings RSAPkIntsFields
nosubstrings x a₁ a₂ = foo
  where
  v2& :  ∀ {bs} → RSAPkIntsFields bs → (&ₚ Int Int) bs
  v2& (mkRSAPkIntsFields n e bs≡) = mk&ₚ n e bs≡
  foo = Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings x (v2& a₁) (v2& a₂)

equivalent : Equivalent (&ₚ Int Int) RSAPkIntsFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkRSAPkIntsFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkRSAPkIntsFields fstₚ₁ sndₚ₁ bs≡) = mk&ₚ fstₚ₁ sndₚ₁ bs≡

iso : Iso (&ₚ Int Int) RSAPkIntsFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkRSAPkIntsFields nval eval bs≡) = refl

@0 unambiguous : Unambiguous RSAPkIntsFields
unambiguous = Iso.unambiguous iso
                (Seq.unambiguous
                (TLV.unambiguous λ {xs} → Int.unambiguous{xs})
                TLV.nosubstrings
                (TLV.unambiguous λ {xs} → Int.unambiguous{xs}))
