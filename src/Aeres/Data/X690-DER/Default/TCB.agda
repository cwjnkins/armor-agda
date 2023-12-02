open import Aeres.Binary
import      Aeres.Grammar.Definitions.Eq
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Option.TCB
open import Aeres.Prelude

module Aeres.Data.X690-DER.Default.TCB where

open Aeres.Grammar.Definitions.Eq           UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.Option.TCB               UInt8

module _ {A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ {@0 bs' : List UInt8} (default : A bs') where
  NotDefault : ∀ {bs} → Option A bs → Set
  NotDefault none = ⊤
  NotDefault (some a) = False (_≋?_ a default)

record Default (A : @0 List UInt8 → Set) ⦃ _ : Eq≋ A ⦄ {@0 bs' : List UInt8} (default : A bs') (@0 bs : List UInt8) : Set where
  constructor mkDefault
  field
    value : Option A bs
    @0 notDefault : NotDefault default value

RawDefault : ∀ {A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ → Raw A → ∀ {bs'} → (default : A bs') → Raw (Default A default)
Raw.D (RawDefault R default) = Raw.D R
Raw.to (RawDefault R default) (mkDefault none notDefault) = Raw.to R default
Raw.to (RawDefault R default) (mkDefault (some value) notDefault) = Raw.to R value
