{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey.Val.EC
open import Aeres.Data.X509.PublicKey.Val.RSA
open import Aeres.Data.X509.PublicKey.Val.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
open import Aeres.Prelude
open import Data.Sum.Properties

module Aeres.Data.X509.PublicKey.Val.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel     UInt8

@0 nosubstrings : ∀ {@0 bs} → (a : PublicKeyAlg bs) → NoSubstrings (PublicKeyVal a)
nosubstrings a = nosu ((-, TLV.val (Alg.getOID a)) ∈? OIDs.Supported)
  where
  nosu : (o∈? : Dec ((-, TLV.val (Alg.getOID a)) ∈ OIDs.Supported)) → NoSubstrings (PublicKeyVal' a o∈?)
  nosu (no ¬p) = TLV.nosubstrings
  nosu (yes (here px)) = TLV.nosubstrings
  nosu (yes (there (here px))) = TLV.nosubstrings

@0 unambiguous : ∀ {@0 bs} → (a : PublicKeyAlg bs) → Unambiguous (PublicKeyVal a)
unambiguous a {xs} =
  case (-, TLV.val (Alg.getOID a)) ∈? OIDs.Supported
  ret (λ o∈? → (a₁ a₂ : PublicKeyVal' a o∈? xs) → a₁ ≡ a₂)
  of λ where
    (no ¬p) a₁ a₂ → ‼ BitString.unambiguous a₁ a₂
    (yes (here px)) a₁ a₂ → ‼ RSA.unambiguous a₁ a₂
    (yes (there (here px))) a₁ a₂ → ‼ EC.unambiguous a₁ a₂

@0 nonmalleable : NonMalleable₁ RawPublicKeyVal
nonmalleable{bs}{o}{bs₁}{bs₂} =
  case (-, TLV.val (Alg.getOID o)) ∈? OIDs.Supported
  ret (λ o∈? → (p₁ : PublicKeyVal' o o∈? bs₁) (p₂ : PublicKeyVal' o o∈? bs₂)
             → toRawPublicKeyVal o o∈? p₁ ≡ toRawPublicKeyVal o o∈? p₂
             → _≡_{A = Exists─ _ (PublicKeyVal' o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
  of λ where
    (no ¬p) p₁ p₂ eq → ‼ BitString.nonmalleable p₁ p₂ (inj₁-injective eq)
    (yes (here px)) p₁ p₂ eq → ‼ RSA.nonmalleable p₁ p₂ (inj₁-injective (inj₂-injective eq))
    (yes (there (here px))) p₁ p₂ eq → ‼ EC.nonmalleable p₁ p₂ (inj₂-injective (inj₂-injective eq))
