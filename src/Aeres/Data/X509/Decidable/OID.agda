{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.OID where

open Base256

module parseOIDSub where
  here' = "parseOIDSub"

  parseOIDSub : Parser Dig (Logging ∘ Dec) Generic.OIDSub
  runParser parseOIDSub xs
    with runParser (parseWhileₜ Dig ((_≥? 128) ∘ toℕ)) xs
  ... | no  ¬parse = do
    tell $ here' String.++ ": underflow"
    return ∘ no $ ‼ go
    where
    @0 go : ¬ Success Dig Generic.OIDSub xs
    go (success ._ read@._ refl (Generic.mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl) suffix refl) =
      contradiction (success (lₚ ∷ʳ lₑ) read refl (mkParseWhile lₚ lₑ lₚ≥128 (<⇒≱ lₑ<128) refl) suffix refl) ¬parse
  ... | yes (success ._ _ read≡ (mkParseWhile lₚ lₑ lₚ≥128 ¬lₑ≥128 refl) suffix refl)
    with lₚ
  ... | [] = return (yes (success [ lₑ ] _ read≡ (Generic.mkOIDSub [] All.[] lₑ (≰⇒> ¬lₑ≥128) tt refl) suffix refl))
  ... | lₚ'@(l ∷ lₚ)
    with toℕ l >? 128
  ... | no  l≯128 = do
    tell $ here' String.++ ": leading byte has value 0 (non-minimal repr.)"
    return ∘ no $ ‼ go
    where
    @0 go : ¬ Success Dig Generic.OIDSub (lₚ' ∷ʳ lₑ ++ suffix)
    go (success .([] ∷ʳ lₑ1) _ read≡ (Generic.mkOIDSub [] lₚ1≥128 lₑ1 lₑ1<128 leastDigs1 refl) .((lₚ ++ [ lₑ ]) ++ suffix) refl) =
      contradiction lₑ1<128 (≤⇒≯ (proj₁ (All.uncons lₚ≥128)))
    go (success .((x ∷ lₚ1) ∷ʳ lₑ1) _ read≡ (Generic.mkOIDSub (x ∷ lₚ1) lₚ1≥128 lₑ1 lₑ1<128 leastDigs1 refl) suffix1 ps≡1) =
      contradiction (subst (λ y → 128 < toℕ y) (∷-injectiveˡ ps≡1) leastDigs1) l≯128
  ... | yes l>128 =
    return (yes (success (lₚ' ∷ʳ lₑ) _ read≡ (Generic.mkOIDSub lₚ' lₚ≥128 lₑ (≰⇒> ¬lₑ≥128) l>128 refl) suffix refl))

open parseOIDSub public using (parseOIDSub)

module parseOIDField where
  here' = "parseOIDField"

  parseOIDElems : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig (Generic.SeqElems Generic.OIDSub) n)
  parseOIDElems = parseSeqElems "oid elems" Generic.OIDSub Props.OIDSub.nonempty Props.OIDSub.nonnesting parseOIDSub

  parseOID : Parser Dig (Logging ∘ Dec) Generic.OID
  parseOID = parseTLV Tag.ObjectIdentifier "oid" _ parseOIDElems

open parseOIDField public using (parseOIDElems ; parseOID)

private
  module Test where

    open X509.SOID

    test₁ : Generic.OID Md5Rsa
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseOID Md5Rsa)} tt)

    test₂ : Generic.OID Sha1Rsa
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseOID Sha1Rsa)} tt)

    test₃ : Generic.OID RsaPss
    test₃ = Success.value (toWitness {Q = Logging.val (runParser parseOID RsaPss)} tt)

    test₄ : Generic.OID Sha256Rsa
    test₄ = Success.value (toWitness {Q = Logging.val (runParser parseOID Sha256Rsa)} tt)

    test₅ : Generic.OID Sha384Rsa
    test₅ = Success.value (toWitness {Q = Logging.val (runParser parseOID Sha384Rsa)} tt)

    test₆ : Generic.OID Sha512Rsa
    test₆ = Success.value (toWitness {Q = Logging.val (runParser parseOID Sha512Rsa)} tt)

    test₇ : Generic.OID Sha224Rsa
    test₇ = Success.value (toWitness {Q = Logging.val (runParser parseOID Sha224Rsa)} tt)

