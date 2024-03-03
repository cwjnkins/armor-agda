{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Semantic.Cert.Utils
open import Armor.Data.X509.Semantic.Chain.NameMatch
import      Armor.Data.X509.Semantic.Chain.TCB as Chain
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.X509.Semantic.Chain.R20 where

open Armor.Grammar.Option   UInt8
open Armor.Grammar.Parallel UInt8
open Chain using (Chain)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.9
-- The PathLenConstraint field is meaningful only if the CA boolean
-- is asserted and the Key Usage extension, if present, asserts the KeyCertSign bit. In this case, it gives
-- the maximum number of non-self-issued intermediate certificates that may follow this certificate in a valid certification path.

countNextIntCACerts : List (Exists─ _ Cert) → ℕ → ℕ
countNextIntCACerts [] n = n
countNextIntCACerts ((_ , cert) ∷ certs) n =
  case Cert.isCA cert of λ where
    nothing → countNextIntCACerts certs n
    (just false) → countNextIntCACerts certs n
    (just true) → case nameMatch? (Cert.getIssuer cert) (Cert.getSubject cert) of λ where
      (no  _) → countNextIntCACerts certs (1 + n)
      (yes _) → countNextIntCACerts certs n


PathWithinMax : Exists─ _ Cert → List (Exists─ _ Cert) → Set
PathWithinMax (_ , cert) certs
  with ⌊ isConfirmedCA? cert ⌋ ∧ certAssertsKUBitField cert Extension.KUFields.keyCertSign
... | false = ⊤
... | true
  with getBCPathLen (Cert.getBC cert)
... | (─ _ , none) = ⊤
... | (_ , some x) = countNextIntCACerts certs 0 ≤ Int.getValNonNegative x

AllPathWithinMax : List (Exists─ _ Cert) → Set
AllPathWithinMax [] = ⊤
AllPathWithinMax (cert ∷ certs) =  PathWithinMax cert certs × AllPathWithinMax certs

pathWithinMax? : (c : Exists─ (List UInt8) Cert) → (t : List (Exists─ (List UInt8) Cert)) → Dec (PathWithinMax c t)
pathWithinMax? (_ , cert) certs
  with ⌊ isConfirmedCA? cert ⌋ ∧ certAssertsKUBitField cert Extension.KUFields.keyCertSign
... | false = yes tt
... | true
  with getBCPathLen (Cert.getBC cert)
... | (─ .[] , none) = yes tt
... | (fst , some x) = countNextIntCACerts certs 0 ≤? Int.getValNonNegative x

module _ {trust candidates : List (Exists─ _ Cert)} {@0 bs} (issuee : Cert bs) where

  R20 :  Chain trust candidates issuee → Set
  R20 c = AllPathWithinMax (reverse (Chain.toList c))

  r20 : Decidable R20
  r20 c = allPathWithinMax? (reverse (Chain.toList c))
    where
    allPathWithinMax? : (c : List (Exists─ (List UInt8) Cert)) → Dec (AllPathWithinMax c)
    allPathWithinMax? [] = yes tt
    allPathWithinMax? (x ∷ x₁) = pathWithinMax? x x₁ ×-dec allPathWithinMax? x₁
