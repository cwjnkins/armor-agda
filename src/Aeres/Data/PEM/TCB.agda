{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Base64
open import Aeres.Data.PEM.CertBoundary.TCB
open import Aeres.Data.PEM.CertText.TCB
open import Aeres.Data.PEM.CertText.FinalLine.TCB
open import Aeres.Data.PEM.CertText.FullLine.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.PEM.TCB where

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char

record Cert (@0 bs : List Char) : Set where
  constructor mkCert
  field
    @0 {h b f} : List Char
    header : CertHeader h
    body   : CertText   b
    footer : CertFooter f
    @0 bs≡ : bs ≡ h ++ b ++ f

CertList = IList Cert

extractCert : ∀ {@0 bs} → Cert bs → List UInt8
extractCert (mkCert _ (mkCertText body final _) _ _) =
  eb body ++ ef final
  where
  eb : ∀ {@0 bs} → IList CertFullLine bs → List UInt8
  eb nil = []
  eb (cons (mkIListCons (mkCertFullLine (mk×ₚ line (─ len≡) refl) _ _) tail₁ _)) =
    decodeStr (mk64Str line (subst (λ x → x % 4 ≡ 0) (sym len≡) refl) (pad0 refl) refl) ++ eb tail₁

  ef : ∀ {@0 bs} → CertFinalLine bs → List UInt8
  ef (mkCertFinalLine line lineLen _ _) = decodeStr line

extractCerts : ∀ {@0 bs} → CertList bs → List UInt8
extractCerts nil = []
extractCerts (consIList c rest refl) =
  extractCert c ++ extractCerts rest
