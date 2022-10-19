{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Serializer

open import Aeres.Prelude

module Aeres.Data.X690-DER.BitString.Serializer where

open Aeres.Grammar.Serializer UInt8

serializeValue : Serializer BitStringValue
Singleton.x (serializeValue x) =
  let (bₕ , bₜ) = help ∘ Singleton.x ∘ BitStringValue.bits $ x
  in bₕ ∷ bₜ
  where
  help : List Bool → UInt8 × List UInt8
  help [] = # 0 , []
  help (x₀ ∷ [])                                = # 7 , [ fromBinary (                              Vec.[ x₀ ] Vec.++ Vec.replicate{n = 7} #0) ]
  help (x₀ ∷ x₁ ∷ [])                           = # 6 , [ fromBinary (x₀ ∷                          Vec.[ x₁ ] Vec.++ Vec.replicate{n = 6} #0) ]
  help (x₀ ∷ x₁ ∷ x₂ ∷ [])                      = # 5 , [ fromBinary (x₀ ∷ x₁ ∷                     Vec.[ x₂ ] Vec.++ Vec.replicate{n = 5} #0) ]
  help (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])                 = # 4 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷                Vec.[ x₃ ] Vec.++ Vec.replicate{n = 4} #0) ]
  help (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ [])            = # 3 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷           Vec.[ x₄ ] Vec.++ Vec.replicate{n = 3} #0) ]
  help (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])       = # 2 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷      Vec.[ x₅ ] Vec.++ Vec.replicate{n = 2} #0) ]
  help (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ [])  = # 1 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ Vec.[ x₆ ] Vec.++ Vec.replicate{n = 1} #0) ]
  help (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ xs) =
    let b         = fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ Vec.[ x₇ ])
        (bₕ , bₜ) = help xs
    in bₕ , b ∷ bₜ
Singleton.x≡ (serializeValue x) = primTrustMe
  -- postulate
  where
  open import Agda.Builtin.TrustMe

serialize : Serializer BitString
serialize = TLV.serialize serializeValue
