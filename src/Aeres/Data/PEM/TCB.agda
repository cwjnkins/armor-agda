{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude

open import Aeres.Grammar.IList Char
open import Aeres.Grammar.Sum   Char

module Aeres.Data.PEM.TCB where

certHeader = String.toList "-----BEGIN CERTIFICATE-----\n"
certFooter = String.toList "-----END CERTIFICATE-----\n"
certEOL    = String.toList "\r\n"

record CertLine (n : ℕ) (@0 bs : List Char) : Set where
  constructor mkCertLine
  field
    line : List Char
    @0 valid64 : All (_∈ Base64.charset) line
    @0 len≡ : length line ≡ n
    @0 bs≡ : bs ≡ line ++ certEOL

record Cert (@0 bs : List Char) : Set where
  constructor mkCert
  field
    @0 p s : List Char
    prefix : IList (CertLine 64) p
    @0 sufLen  : ℕ
    @0 sufLen≤ : sufLen ≤ 64
    suffix : CertLine sufLen s
    @0 bs≡ : bs ≡ certHeader ++ p ++ s ++ certFooter
    
PEM : @0 List Char → Set
PEM = IList Cert
