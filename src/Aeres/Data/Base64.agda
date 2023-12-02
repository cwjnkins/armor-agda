import      Aeres.Data.Base64.Parser
import      Aeres.Data.Base64.Properties
import      Aeres.Data.Base64.Serializer
import      Aeres.Data.Base64.TCB
open import Aeres.Grammar.Parser
open import Aeres.Prelude
  hiding (module Char)

module Aeres.Data.Base64 where

open Aeres.Data.Base64.Parser       public
module Base64 where
  module Char where
    open Aeres.Data.Base64.Properties.Base64Char public
    open Aeres.Data.Base64.Serializer.Base64Char public
  module Pad where
    open Aeres.Data.Base64.Properties.Base64Pad public
    open Aeres.Data.Base64.Serializer.Base64Pad public
  module Str where
    open Aeres.Data.Base64.Properties.Base64Str public
    open Aeres.Data.Base64.Serializer.Base64Str public    
open Aeres.Data.Base64.TCB          public

base64Char? : Decidable (λ x → Base64Char x)
base64Char? xs =
  let (mkLogged _ v₂) = runParser parseBase64Char xs
  in
  case v₂ of λ where
    (no ¬p) → no (λ x → contradiction (success xs _ refl x [] (++-identityʳ _)) ¬p)
    (yes (success prefix read read≡ value [] ps≡)) →
      yes (subst₀! Base64Char (trans (sym $ ++-identityʳ _) ps≡) value)
    (yes (success prefix read read≡ (mk64 c' c'∈ i' refl) suffix@(c“ ∷ s') ps≡)) →
      no λ where
        (mk64 c c∈ i bs≡) →
          contradiction {P = [ c ] ≡ c' ∷ c“ ∷ s'}
            (begin ([ c ] ≡⟨ sym bs≡ ⟩
                   xs ≡⟨ sym ps≡ ⟩
                   c' ∷ suffix ∎))
            (λ ())
  where
  open ≡-Reasoning
