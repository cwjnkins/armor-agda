{-# OPTIONS --allow-unsolved-metas #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.Parser
open import Aeres.Data.X509

module Aeres.Data.X509.Decidable.Length where

open Base256

parseLen : Parser Dig (Logging ∘ Dec) Length
runParser parseLen = go
  where
  here' = "parseLen"

  go : (xs : List Dig) → (Logging ∘ Dec) (Success Dig Length xs)
  go [] = do
    tell (here' String.++ ": underflow reading length")
    return $ no λ where
      (Length.short (Length.mkShort _ _ refl) ^S _ [ () ]S)
      (Length.long (Length.mkLong _ _ _ _ _ _ _ refl) ^S _ [ () ]S)
  go (l ∷ xs)
    with toℕ l <? 128
  ... | yes l<128 =
    return $ yes (Length.short (Length.mkShort l l<128 refl) ^S xs [ refl ]S)
  ... | no  l≮128
    with xs
  ... | [] = do
    tell $ here' String.++ ": underflow reading long length"
    return $ no λ where
      (Length.short (Length.mkShort l l<128 refl) ^S .[] [ refl ]S) → ⊥-irrel (l≮128 l<128)
      (Length.long (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₕₜLen lₕₜMinRep refl) ^S suffix [ () ]S)
  ... | lₕ ∷ lₜ
    with runParser (parseN Dig (toℕ l - 128)) (lₕ ∷ lₜ)
  ... | no pf = {!!}
  ... | yes ((ys , ys≡ , ysLen) ^S suffix [ ps≡ ]S) = {!!}

