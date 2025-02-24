{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X509.CRL.Version.Properties
open import Armor.Data.X509.CRL.Version.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.CRL.Version.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: CRL: CertList: TBSCertList: Version"

parse : Parser (Logging ∘ Dec) Version
parse =
  parseSigma TLV.nosubstrings Int.unambiguous (Int.parse here')
    (λ i → erased? (_ ∈? _))
