open import Aeres.Data.Base64.TCB
open import Aeres.Data.PEM.CertText.FinalLine.TCB
open import Aeres.Data.PEM.CertText.FullLine.TCB
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.PEM.CertText.TCB where

open Aeres.Grammar.IList Char

record CertText (@0 bs : List Char) : Set where
  constructor mkCertText
  field
    @0 {b f} : List Char
    body  : IList CertFullLine b
    final : CertFinalLine      f
    @0 bs≡ : bs ≡ b ++ f

