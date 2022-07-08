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

certEOL    = String.toList "\r\n"
certHeader = (String.toList "-----BEGIN CERTIFICATE-----") ++ certEOL
certFooter = (String.toList "-----END CERTIFICATE-----"  ) ++ certEOL

record CertLine (@0 n : ℕ) (@0 bs : List Char) : Set where
  constructor mkCertLine
  field
    @0 {l} : List Char
    str : Base64Str l
    @0 lenRange : InRange 1 64 (length l)
    @0 n≡ : n ≡ length (Base64Str.s str)
    @0 bs≡ : bs ≡ l ++ certEOL

ShortCertLine : @0 List Char → Set
ShortCertLine bs = Σ[ sₗ ∈ Fin 64 ] CertLine (toℕ sₗ) bs 

record Cert (@0 bs : List Char) : Set where
  constructor mkCert
  field
    @0 {p s} : List Char
    prefix : IList (CertLine 64) p
    suffix : Option ShortCertLine s
    @0 bs≡ : bs ≡ certHeader ++ p ++ s ++ certFooter
    
PEM : @0 List Char → Set
PEM = IList Cert

-- extract : ∀ {@0 bs} → Cert bs → List UInt8
-- extract (mkCert prefix suffix bs≡) = {!!}
--   where
--   extr : ∀ {@0 bs n} → CertLine n bs → List UInt8
--   extr (mkCertLine str _ _ _) = {!!}
