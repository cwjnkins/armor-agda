{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Base64
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.PEM.TCB where

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char
open Aeres.Grammar.Option      Char

-- For now, we only support the strict PEM encoding;
-- see `stricttextualmsg` in Fig. 3 of RFC 7468

module RFC5234 where
  data EOL : @0 List Char → Set where
    crlf : EOL ('\r' ∷ [ '\n' ])
    cr   : EOL [ '\r' ]
    lf   : EOL [ '\n' ]

record CertBoundary (@0 ctrl : String) (@0 bs : List Char) : Set where
  constructor mkCertBoundary
  field
    @0 {e} : List Char
    @0 begin : Singleton ∘ String.toList $
                 "-----" String.++ ctrl String.++ " CERTIFICATE-----"
    @0 eol   : RFC5234.EOL e
    @0 bs≡   : bs ≡ ↑ begin ++ e

CertHeader = CertBoundary "BEGIN"
CertFooter = CertBoundary "END"

record CertFullLine (@0 bs : List Char) : Set where
  constructor mkCertFullLine
  field
    @0 {l e} : List Char
    line : ExactLength (IList Base64Char) 64 l
    eol  : RFC5234.EOL e
    @0 bs≡  : bs ≡ l ++ e

record CertFinalLine (@0 bs : List Char) : Set where
  constructor mkCertFinalLine
  field
    @0 {l e} : List Char
    line : Base64Str l
    @0 lineLen : InRange 1 64 ∘ length $ l
    eol : RFC5234.EOL e
    @0 bs≡ : bs ≡ l ++ e

record CertText (@0 bs : List Char) : Set where
  constructor mkCertText
  field
    @0 {b f} : List Char
    body  : IList CertFullLine b
    final : CertFinalLine      f
    @0 bs≡ : bs ≡ b ++ f

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
