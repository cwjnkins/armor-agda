module Aeres.Prelude where

open import Data.Bool    public
  hiding (_<_ ; _<?_ ; _≟_ ; _≤_ ; _≤?_)

import Data.Char
module Char = Data.Char

import Data.Fin
module Fin = Data.Fin

open import Data.Product public

open import Data.Nat     public

import Data.String
module String = Data.String

open import Data.Sum     public
  hiding (map ; map₁ ; map₂ ; swap)

open import Data.Vec     public
  hiding (map ; zip)
