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
    crlf : EOL (String.toList "\r\n")
    cr   : EOL (String.toList "\r")
    lf   : EOL (String.toList "\n")

--   data EOLWSP : @0 List Char → Set where
--     wsp : ∀ {@0 c} → WSP c → EOLWSP c
--     cr  :                    EOLWSP [ '\r' ]
--     lf  :                    EOLWSP [ '\n' ]

record CertBoundary (@0 ctrl : String) (@0 bs : List Char) : Set where
  constructor mkCertBoundary
  field
    @0 {e} : List Char
    begin : Singleton ∘ String.toList $
              "-----" String.++ ctrl String.++ " CERTIFICATE-----"
    eol   : RFC5234.EOL e
    bs≡   : bs ≡ ↑ begin ++ e

CertHeader = CertBoundary "BEGIN"
CertFooter = CertBoundary "END"

record CertFullLine (@0 bs : List Char) : Set where
  constructor mkCertFullLine
  field
    @0 {l e} : List Char
    line : ExactLength Base64Char 64 l
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

-- extract : ∀ {@0 bs} → Cert bs → List UInt8
-- extract (mkCert prefix suffix bs≡) = {!!}
--   where
--   extr : ∀ {@0 bs n} → CertLine n bs → List UInt8
--   extr (mkCertLine str _ _ _) = {!!}
