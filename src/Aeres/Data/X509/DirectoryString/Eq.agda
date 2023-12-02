open import Aeres.Binary
open import Aeres.Data.Unicode
open import Aeres.Data.X509.DirectoryString.Properties
open import Aeres.Data.X509.DirectoryString.TCB
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Strings
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.DirectoryString.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋ : Eq≋ DirectoryString
  eq≋ =
    Iso.isoEq≋ iso
      (Sum.sumEq≋
        ⦃ Parallel.eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
        ⦃ Sum.sumEq≋
          ⦃ Parallel.eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
          ⦃ Sum.sumEq≋
            ⦃ Parallel.eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
            ⦃ Sum.sumEq≋ ⦃ Parallel.eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
                     ⦃ Parallel.eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄ ⦄ ⦄ ⦄)
