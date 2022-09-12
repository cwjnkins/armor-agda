{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Relation.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Aeres.Data.Base64
import      Aeres.Data.PEM.TCB as PEM

open Aeres.Grammar.Definitions          Char
open Aeres.Grammar.IList                Char
open Aeres.Grammar.Relation.Definitions Char
open Aeres.Grammar.Sum                  Char

module Aeres.Data.PEM.Properties where

module EOL where
  Rep =  Sum (_≡ '\r' ∷ [ '\n' ])
        (Sum (_≡ [ '\r' ])
             (_≡ [ '\n' ]))

  equiv : Equivalent Rep PEM.RFC5234.EOL
  proj₁ equiv (Sum.inj₁ refl) = PEM.RFC5234.crlf
  proj₁ equiv (Sum.inj₂ (Sum.inj₁ refl)) = PEM.RFC5234.cr
  proj₁ equiv (Sum.inj₂ (Sum.inj₂ refl)) = PEM.RFC5234.lf
  proj₂ equiv PEM.RFC5234.crlf = Sum.inj₁ refl
  proj₂ equiv PEM.RFC5234.cr = Sum.inj₂ (Sum.inj₁ refl)
  proj₂ equiv PEM.RFC5234.lf = Sum.inj₂ (Sum.inj₂ refl)

module CertBoundary where
  Rep : (ctrl : String) → @0 List Char → Set
  Rep ctrl = &ₚ (_≡ (String.toList $ "-----" String.++ ctrl String.++ " CERTIFICATE-----"))
                (Erased ∘ PEM.RFC5234.EOL)

  equiv : ∀ ctrl → Equivalent (Rep ctrl) (PEM.CertBoundary ctrl)
  proj₁ (equiv ctrl) (mk&ₚ refl (─ sndₚ₁) bs≡) = PEM.mkCertBoundary self sndₚ₁ bs≡
  proj₂ (equiv ctrl) (PEM.mkCertBoundary self eol bs≡) = mk&ₚ refl (─ eol) bs≡

module CertFullLine where
  Rep = &ₚ (ExactLength (IList Base64Char) 64) PEM.RFC5234.EOL

  equiv : Equivalent Rep PEM.CertFullLine
  proj₁ equiv (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = PEM.mkCertFullLine fstₚ₁ sndₚ₁ bs≡
  proj₂ equiv (PEM.mkCertFullLine line eol bs≡) = mk&ₚ line eol bs≡

module CertFinalLine where

  Rep : @0 List Char → Set
  Rep = Σₚ (&ₚ Base64Str PEM.RFC5234.EOL)
           (λ _ → Erased ∘ InRange 1 64 ∘ length ∘ &ₚᵈ.bs₁ )

  postulate
    equiv : Equivalent Rep PEM.CertFinalLine
    noOverlap : NoOverlap Base64Str PEM.RFC5234.EOL
