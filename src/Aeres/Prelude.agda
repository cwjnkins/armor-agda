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

  open import Data.Fin.Properties public

Fin = Fin.Fin

infix 10 #_
#_ = Fin.#_

open import Data.List    public

open import Data.List.Properties public

open import Data.List.Relation.Unary.Any public
  using (here ; there)
module Any = Data.List.Relation.Unary.Any
Any = Any.Any

open import Data.List.Membership.Propositional public
  using (_∈_ ; _∉_)

open import Data.Maybe public
  hiding (align ; alignWith ; fromMaybe ; map ; zip ; zipWith ; _>>=_)

open import Data.Nat     public
  hiding (_≟_)
open import Agda.Builtin.Nat public
  using (_-_)

open import Data.Product public
  hiding (map ; zip)

import Data.String
module String = Data.String

open import Data.Sum     public
  hiding (map ; map₁ ; map₂ ; swap)

open import Data.Unit    public
  using (⊤ ; tt)

open import Data.Vec public
  using (_∷_ ; [])
module Vec = Data.Vec
Vec = Vec.Vec

open import Function     public

module Level where
  open import Level public

open import Relation.Binary.PropositionalEquality public
  hiding ([_] ; decSetoid)
module Reveal = Reveal_·_is_

open import Relation.Binary.Definitions public
  using (Tri ; tri< ; tri≈ ; tri> )

open import Relation.Nullary public

open import Relation.Nullary.Decidable public
  hiding (map)

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

  FinEq : ∀ {n} → Eq (Fin n)
  Eq._≟_ FinEq = Fin._≟_

record Sized {ℓ} (A : Set ℓ) : Set ℓ where
  field
    sizeOf : A → ℕ
open Sized ⦃ ... ⦄ public

import Category.Monad
Monad = Category.Monad.RawMonad
MonadZero = Category.Monad.RawMonadZero

module Monad {ℓ} {M : Set ℓ → Set ℓ} (m : Monad M) where
  open Category.Monad.RawMonad m public
    hiding (zip ; zipWith)

open Monad ⦃ ... ⦄ public

instance
  MonadMaybe : ∀ {ℓ} → Monad{ℓ} Maybe
  MonadMaybe = monad
    where open import Data.Maybe.Categorical

module MonadZero {ℓ} {M : Set ℓ → Set ℓ} (m : MonadZero M) where
  import Category.Monad

  ∅ = Category.Monad.RawMonadZero.∅ m

open MonadZero ⦃ ... ⦄ public

instance
  MonadZeroMaybe : ∀ {ℓ} → MonadZero{ℓ} Maybe
  MonadZeroMaybe = monadZero
    where open import Data.Maybe.Categorical

record Writer {ℓ} (M : Set ℓ → Set ℓ) (W : Set ℓ) : Set ℓ where
  field
    tell : W → M (Level.Lift _ ⊤)

open Writer ⦃ ... ⦄ public

record Logging {ℓ} (A : Set ℓ) : Set ℓ where
  constructor mkLogged
  field
    log : List String.String
    val : A

instance
  MonadLogging : ∀ {ℓ} → Monad{ℓ} Logging
  Monad.return MonadLogging x = mkLogged [] x
  Monad._>>=_  MonadLogging (mkLogged log₁ val₁) f
    with f val₁
  ... | mkLogged log₂ val₂ = mkLogged (log₁ ++ log₂) val₂

  WriterLogging : Writer Logging String.String
  Writer.tell WriterLogging w = mkLogged [ w ] (Level.lift tt)

-- Lemmas
module Lemmas where

  open import Data.List.Solver using (module ++-Solver)
  open ++-Solver using (_⊕_)

  ++-assoc₄ : ∀ {ℓ} {A : Set ℓ} (ws xs ys zs : List A) → ws ++ xs ++ ys ++ zs ≡ (ws ++ xs ++ ys) ++ zs
  ++-assoc₄ = ++-Solver.solve 4 (λ ws xs ys zs → ws ⊕ xs ⊕ ys ⊕ zs , (ws ⊕ xs ⊕ ys) ⊕ zs) refl

  length-++-≡ : ∀ {ℓ} {A : Set ℓ} (ws xs ys zs : List A) → ws ++ xs ≡ ys ++ zs → length ws ≡ length ys → ws ≡ ys × xs ≡ zs
  length-++-≡ [] xs [] zs ++-≡ len≡ = refl , ++-≡
  length-++-≡ (x ∷ ws) xs (x₁ ∷ ys) zs ++-≡ len≡
    with length-++-≡ ws xs ys zs (∷-injectiveʳ ++-≡) (cong pred len≡)
  ...| refl , xs≡zs = cong (_∷ ws) (∷-injectiveˡ ++-≡) , xs≡zs
