{-# OPTIONS --subtyping --allow-unsolved-metas #-}

open import Aeres.Binary
  renaming (module Base64 to B64)
open import Aeres.Data.Base64
open import Aeres.Data.PEM.CertBoundary
open import Aeres.Data.PEM.CertText
open import Aeres.Data.PEM.CertText.FinalLine
open import Aeres.Data.PEM.CertText.FullLine
open import Aeres.Data.PEM.RFC5234
open import Aeres.Data.PEM.Properties
open import Aeres.Data.PEM.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Relation.Definitions
open import Aeres.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any

module Aeres.Data.PEM.Parser where

open Aeres.Grammar.Definitions          Char
open Aeres.Grammar.IList                Char
open Aeres.Grammar.Relation.Definitions Char
open Aeres.Grammar.Parser               Char

parseCert : LogDec.MaximalParser Cert
parseCert =
  LogDec.equivalent equiv
    (LogDec.parse&
      (parseCertBoundary "BEGIN")
      (LogDec.parse&
        parseMaxCertText
        (parseCertBoundary "END")
        noOverlapTextFooter)
      noOverlapHeaderText)

parseCertList : LogDec.MaximalParser CertList
parseCertList =
  parseIListMaxNoOverlap.parseIListMax
    (tell "PEM: underflow reading cert list")
    Cert nonempty noOverlap
    parseCert

-- parseCertListWithRootStore : LogDec.MaximalParser CertListWithRootStore
-- parseCertListWithRootStore = LogDec.equivalent {!!}
--                                (LogDec.parse& parseCertList (
--                                  LogDec.parse& {!!} parseCertList {!!}) {!!})
