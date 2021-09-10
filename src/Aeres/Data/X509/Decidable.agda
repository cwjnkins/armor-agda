open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties

open Base256
open import Aeres.Data.Parser Dig

module Aeres.Data.X509.Decidable where

postulate
  parseLen : Parser (Logging ∘ Dec) Length

parseCert : Parser (Logging ∘ Dec) X509.Cert
runParser parseCert xs = do
  yes lenₛ@(len ^S suf₀ [ xs≡₁ ]S) ← runParser parseLen xs
    where no pf → {!!}
  {!!}
