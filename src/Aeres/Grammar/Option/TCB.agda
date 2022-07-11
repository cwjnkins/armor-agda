{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.Option.TCB (Σ : Set) where

data Option (@0 A : List Σ → Set) : (@0 _ : List Σ) → Set where
 none : Option A []
 some : ∀ {@0 xs} → A xs → Option A xs

elimOption : ∀ {@0 A} {X : List Σ → Set} → X [] → (∀ {@0 xs} → A xs → X xs) → ∀ {@0 xs} → Option A xs → X xs
elimOption n s none = n
elimOption n s (some x) = s x

isNone : ∀ {@0 A xs} →  Option A xs → Bool
isNone none = true
isNone (some _) = false

isSome : ∀ {@0 A xs} → Option A xs → Bool
isSome x = not (isNone x)

mapOption : ∀ {@0 A B} → (∀ {@0 xs} → A xs → B xs) → ∀ {@0 xs} → Option A xs → Option B xs
mapOption f none = none
mapOption f (some x) = some (f x)

mapOptionK : ∀ {@0 A B xs} → (A xs → B xs) → Option A xs → Option B xs
mapOptionK f none = none
mapOptionK f (some x) = some (f x)