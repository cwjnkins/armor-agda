{-# OPTIONS --subtyping #-}


open import Aeres.Data.Base64.TCB
open import Aeres.Data.PEM.CertBoundary.TCB
open import Aeres.Data.PEM.RFC5234.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.PEM.CertBoundary.Properties where

open Aeres.Grammar.Definitions Char

Rep : (ctrl : String) → @0 List Char → Set
Rep ctrl = &ₚ (_≡ (String.toList $ "-----" String.++ ctrl String.++ " CERTIFICATE-----"))
              (Erased ∘ EOL)

equiv : ∀ ctrl → Equivalent (Rep ctrl) (CertBoundary ctrl)
proj₁ (equiv ctrl) (mk&ₚ refl (─ sndₚ₁) bs≡) = mkCertBoundary self sndₚ₁ bs≡
proj₂ (equiv ctrl) (mkCertBoundary self eol bs≡) = mk&ₚ refl (─ eol) bs≡
