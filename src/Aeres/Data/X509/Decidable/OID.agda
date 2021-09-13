open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.Parser
open import Aeres.Data.X509

module Aeres.Data.X509.Decidable.OID where

open Base256

module parseOIDSub where
  here' = "parseOIDSub"

  parseOIDSub : Parser Dig (Logging ∘ Dec) Generic.OIDSub
  runParser parseOIDSub [] = do
    tell $ here' String.++ ": underflow"
    {!!}
  runParser parseOIDSub (x ∷ xs) = {!!}

open parseOIDSub public using (parseOIDSub)
