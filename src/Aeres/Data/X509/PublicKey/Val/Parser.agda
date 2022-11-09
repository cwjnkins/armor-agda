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
parsePublicKeyVal{bs} o =
  case (-, TLV.val o) ∈? supportedPublicKeyAlgs
  ret (λ x → Parser (Logging ∘ Dec) (PublicKeyVal' o x))
  of λ where
    (yes (here px)) → parseRSABitString
    (yes (there (here px))) → parseECBitString
    (no ¬p) → parseBitstring
