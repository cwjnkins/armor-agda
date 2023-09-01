{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Unicode
open import Aeres.Data.X509.DirectoryString.Properties
open import Aeres.Data.X509.DirectoryString.TCB
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Strings
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.DirectoryString.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋ : Eq≋ DirectoryString
  eq≋ =
    isoEq≋ iso
      (sumEq≋
        ⦃ eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
        ⦃ sumEq≋
          ⦃ eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
          ⦃ sumEq≋
            ⦃ eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
            ⦃ sumEq≋ ⦃ eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
                     ⦃ eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄ ⦄ ⦄ ⦄)
