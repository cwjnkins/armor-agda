{-# OPTIONS --erasure #-}
open import Armor.Data.Base64.TCB
open import Armor.Data.PEM.RFC5234.TCB
open import Armor.Prelude

module Armor.Data.PEM.CRLBoundary.TCB where

record CRLBoundary (ctrl : String) (@0 bs : List Char) : Set where
  constructor mkCRLBoundary
  field
    @0 {b e} : List Char
    @0 begin : b ≡ (String.toList $ "-----" String.++ ctrl String.++ " X509 CRL-----")
    @0 eol   : EOL e
    @0 bs≡   : bs ≡ b ++ e

CRLHeader = CRLBoundary "BEGIN"
CRLFooter = CRLBoundary "END"
