{-# OPTIONS --subtyping #-}


open import Aeres.Data.Base64.TCB
open import Aeres.Data.PEM.CertText.FullLine.TCB
open import Aeres.Data.PEM.RFC5234.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Relation.Definitions
open import Aeres.Prelude

module Aeres.Data.PEM.CertText.FullLine.Properties where

open Aeres.Grammar.Definitions          Char
open Aeres.Grammar.IList                Char
open Aeres.Grammar.Relation.Definitions Char

Rep = &ₚ (ExactLength (IList Base64Char) 64) EOL

equiv : Equivalent Rep CertFullLine
proj₁ equiv (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkCertFullLine fstₚ₁ sndₚ₁ bs≡
proj₂ equiv (mkCertFullLine line eol bs≡) = mk&ₚ line eol bs≡

nonempty : NonEmpty CertFullLine
nonempty (mkCertFullLine (mk×ₚ (consIList (mk64 c c∈ i refl) t refl) (─ len≡) refl) eol ()) refl

postulate
  nooverlap  : NoOverlap CertFullLine CertFullLine
  @0 fullLineLen : ∀ {@0 bs} → CertFullLine bs → InRange 65 66 (length bs)
