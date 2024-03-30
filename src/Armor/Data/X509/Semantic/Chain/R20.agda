{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Semantic.Cert.Utils
open import Armor.Data.X509.Semantic.Chain.NameMatch
import      Armor.Data.X509.Semantic.Chain.TCB as Chain
import      Armor.Data.X509.Semantic.Chain.R20.TCB
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
open import Armor.Prelude
open import Relation.Nullary.Implication using (_→-dec_)
open import Relation.Nullary.Negation using (¬?)

module Armor.Data.X509.Semantic.Chain.R20 where

open Armor.Grammar.Option   UInt8
open Armor.Grammar.Parallel UInt8
open Chain using (Chain)
open Armor.Data.X509.Semantic.Chain.R20.TCB public

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

  r20 : Decidable (R20{trust}{candidates} issuee)
  r20 chain = allPathLensWithinConstraints? (chain |> Chain.getIssuers |> reverse)
