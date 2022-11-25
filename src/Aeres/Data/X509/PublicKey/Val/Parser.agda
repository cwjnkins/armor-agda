{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.TCB
open import Aeres.Data.X509.PublicKey.Val.EC
open import Aeres.Data.X509.PublicKey.Val.RSA
open import Aeres.Data.X509.PublicKey.Val.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.Parser where

open Aeres.Grammar.Parser UInt8

parsePublicKeyVal : ∀ {@0 bs} → (o : OID bs) → Parser (Logging ∘ Dec) (PublicKeyVal o)
runParser (parsePublicKeyVal{bs} o) xs = do
  yes s ← runParser (p₁ o (_ ∈? _)) xs
    where no ¬p → do
      return ∘ no $ λ where
        x → contradiction (mapSuccess (λ where (mkPKVal x) → x) x) ¬p
  return (yes (mapSuccess mkPKVal s))
  where
  p₁ : ∀ {@0 bs} → (o : OID bs) (d : Dec ((-, TLV.val o) ∈ supportedPublicKeyAlgs))
       → Parser (Logging ∘ Dec) (PublicKeyVal' o d)
  p₁ o d =
    case d
    ret (λ x → Parser (Logging ∘ Dec) (PublicKeyVal' o x))
    of λ where
      (yes (here px)) → parseRSABitString
      (yes (there (here px))) → parseECBitString
      (no ¬p) → parseBitstring
