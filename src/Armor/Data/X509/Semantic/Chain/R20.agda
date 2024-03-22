{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Semantic.Cert.Utils
open import Armor.Data.X509.Semantic.Chain.NameMatch
import      Armor.Data.X509.Semantic.Chain.TCB as Chain
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
open import Armor.Prelude
open import Relation.Nullary.Implication using (_→-dec_)
open import Relation.Nullary.Negation using (¬?)

module Armor.Data.X509.Semantic.Chain.R20 where

open Armor.Grammar.Option   UInt8
open Armor.Grammar.Parallel UInt8
open Chain using (Chain)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.9
-- The pathLenConstraint field is meaningful only if the cA boolean is asserted
-- and the key usage extension, if present, asserts the keyCertSign bit. In this
-- case, it gives the maximum number of non-self-issued intermediate
-- certificates that may follow this certificate in a valid certification path.
-- (Note: The last certificate in the certification path is not an intermediate
-- certificate, and is not included in this limit. Usually, the last certificate
-- is an end entity certificate, but it can be a CA certificate.) A
-- pathLenConstraint of zero indicates that no non-self-issued intermediate CA
-- certificates may follow in a valid certification path. Where it appears, the
-- pathLenConstraint field MUST be greater than or equal to zero. Where
-- pathLenConstraint does not appear, no limit is imposed.

CertSelfIssued : ∀ {@0 bs} → Cert bs → Set
CertSelfIssued c = NameMatch (Cert.getIssuer c) (Cert.getSubject c)

pathLength : (intermediateCerts : List (Exists─ _ Cert)) → ℕ
pathLength = length ∘ filter non-self-issued?
  where
  non-self-issued? : Decidable (¬_ ∘ CertSelfIssued ∘ proj₂)
  non-self-issued? (─ _ , c) = ¬? (nameMatch? (Cert.getIssuer c) (Cert.getSubject c))

PathLenContraintMeaningful : ∀ {@0 bs} → Cert bs → Set
PathLenContraintMeaningful c =
    IsConfirmedCA c
  × T (certAssertsKUBitField c Extension.KUFields.keyCertSign)
  × T (isSome (c |> Cert.getBC |> getBCPathLen |> proj₂))
-- _|>_ is flipped application, i.e., `x |> f` is `f x`

getMeaningfulPathLenContraint
  : ∀ {@0 bs} → (c : Cert bs) → PathLenContraintMeaningful c → ℕ
getMeaningfulPathLenContraint c (_ , _ , is) = Int.getValNonNegative (fromSome _ {is})

PathLenWithinConstraint : ∀ {@0 bs} → List (Exists─ _ Cert) → Cert bs → Set
PathLenWithinConstraint certs cert =
    (pm : PathLenContraintMeaningful cert)
  → pathLength certs ≤ getMeaningfulPathLenContraint cert pm

AllPathLensWithinConstraints : List (Exists─ _ Cert) → Set
AllPathLensWithinConstraints [] = ⊤
AllPathLensWithinConstraints ((─ _ , cert) ∷ certs) =
    PathLenWithinConstraint certs cert
  × AllPathLensWithinConstraints certs

------------------------------------------------------------------------

@0 unique-PathLenConstraintMeaningful
  : ∀ {@0 bs} → (c : Cert bs) → Unique (PathLenContraintMeaningful c)
unique-PathLenConstraintMeaningful c (isCA₁ , cs₁ , is₁) (isCA₂ , cs₂ , is₂)
  with Cert.isCA c
  | certAssertsKUBitField c Extension.KUFields.keyCertSign
  | c |> Cert.getBC |> getBCPathLen |> proj₂ |> isSome
... | just true | true | true = refl

pathLenConstraintMeaningful? : ∀ {@0 bs} → (c : Cert bs) → Dec (PathLenContraintMeaningful c)
pathLenConstraintMeaningful? c =
  isConfirmedCA? c ×-dec T-dec ×-dec T-dec

pathLenWithinConstraint?
  : ∀ {@0 bs} → (certs : List (Exists─ _ Cert)) (cert : Cert bs)
    → Dec (PathLenWithinConstraint certs cert)
pathLenWithinConstraint? certs cert =
  case pathLenConstraintMeaningful? cert
  of λ where
    (no ¬pm) → yes λ pm → contradiction pm ¬pm
    (yes pm) → case pathLength certs ≤? getMeaningfulPathLenContraint cert pm of λ where
      (no ¬within) → no λ plwc → contradiction (plwc pm) ¬within 
      (yes within) → yes λ pm' →
        case (‼ unique-PathLenConstraintMeaningful cert pm pm') of λ where
          refl → within

allPathLensWithinConstraints? : (certs : List (Exists─ _ Cert)) → Dec (AllPathLensWithinConstraints certs)
allPathLensWithinConstraints? [] = yes tt
allPathLensWithinConstraints? ((─ _ , cert) ∷ certs) =
        pathLenWithinConstraint? certs cert
  ×-dec allPathLensWithinConstraints? certs

------------------------------------------------------------------------

module _ {trust candidates : List (Exists─ _ Cert)} {@0 bs} (issuee : Cert bs) where

  R20 : Chain trust candidates issuee → Set
  R20 chain = AllPathLensWithinConstraints (chain |> Chain.getIssuers |> reverse)

  r20 : Decidable R20
  r20 chain = allPathLensWithinConstraints? (chain |> Chain.getIssuers |> reverse)
