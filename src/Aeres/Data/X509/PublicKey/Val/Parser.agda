{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
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

parse : ∀ {@0 bs} → (a : PublicKeyAlg bs) → Parser (Logging ∘ Dec) (PublicKeyVal a)
parse a =
  case (-, TLV.val (Alg.getOID a)) ∈? OIDs.Supported
  ret (λ o∈? → Parser (Logging ∘ Dec) (PublicKeyVal' a o∈?))
  of λ where
    (no ¬p) → parseBitstring
    (yes (here px)) → RSA.parse
    (yes (there (here px))) → EC.parse
