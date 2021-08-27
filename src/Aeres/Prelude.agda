module Aeres.Prelude where

open import Data.Bool    public
  hiding (_<_ ; _<?_ ; _≟_ ; _≤_ ; _≤?_)

import Data.Char
module Char = Data.Char
Char = Char.Char

import Data.Fin
module Fin where
  open Data.Fin public

  open import Data.Nat
    renaming (_+_ to _+ℕ_ ; pred to predℕ)
  open import Data.Nat.Properties

  2*_ : ∀ {m} → Fin m → Fin (predℕ (2 * m))
  2*_  (zero{n}) rewrite +-suc n (n +ℕ 0) = zero
  2* suc {suc n} i rewrite +-suc n (suc (n +ℕ 0)) =
    suc (suc (2* i))

Fin = Fin.Fin

open import Data.List    public

open import Data.List.Relation.Unary.Any public
  using (here ; there)
module Any = Data.List.Relation.Unary.Any
Any = Any.Any

open import Data.List.Membership.Propositional public
  using (_∈_ ; _∉_)

open import Data.Maybe public
  hiding (align ; alignWith ; fromMaybe ; map ; zip ; zipWith)

open import Data.Nat     public
  hiding (_≟_)

open import Data.Product public
  hiding (map ; zip)

import Data.String
module String = Data.String

open import Data.Sum     public
  hiding (map ; map₁ ; map₂ ; swap)

open import Data.Vec public
  using (_∷_ ; [])
module Vec = Data.Vec
Vec = Vec.Vec

open import Function     public

open import Relation.Binary.PropositionalEquality public
  hiding ([_] ; decSetoid)
module Reveal = Reveal_·_is_

open import Relation.Nullary public

-- Typeclasses

record Numeric {ℓ} (A : Set ℓ) : Set ℓ where
  field
    toℕ : A → ℕ
open Numeric ⦃ ... ⦄ public

instance
  ℕNumeric : Numeric ℕ
  Numeric.toℕ ℕNumeric = id

  BoolNumeric : Numeric Bool
  Numeric.toℕ BoolNumeric false = 0
  Numeric.toℕ BoolNumeric true = 1

  FinNumeric : ∀ {n} → Numeric (Fin n)
  Numeric.toℕ FinNumeric = Fin.toℕ

record Eq {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : (x y : A) → Dec (x ≡ y)

open Eq ⦃ ... ⦄ public

instance
  ℕEq : Eq ℕ
  Eq._≟_ ℕEq = Data.Nat._≟_

  CharEq : Eq Char
  Eq._≟_ CharEq = Char._≟_
