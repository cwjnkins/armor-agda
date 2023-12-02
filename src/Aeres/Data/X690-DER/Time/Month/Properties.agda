open import Aeres.Binary
open import Aeres.Data.X690-DER.Time.TimeType.TCB
open import Aeres.Data.X690-DER.Time.Month.TCB
import      Aeres.Grammar.Definitions.NonMalleable.Base
open import Aeres.Prelude
import      Data.Nat.Properties as Nat

module Aeres.Data.X690-DER.Time.Month.Properties where

daysInMonth≤31 : ∀ {@0 bs} → (m : Month bs) → daysInMonth m ≤ 31
daysInMonth≤31 m
  with TimeType.getTime m ∈? 1 ∷ 3 ∷ 5 ∷ 7 ∷ 8 ∷ 10 ∷ [ 12 ]
... | yes _ = Nat.≤-refl
... | no _
  with TimeType.getTime m ≟ 2
... | yes _ = Nat.m≤n+m 29 2
... | no _ = Nat.m≤n+m 30 1
