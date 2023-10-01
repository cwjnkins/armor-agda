{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID.Parser
open import Aeres.Data.X690-DER.OID.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel.TCB
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB.OIDs where

open Aeres.Grammar.Definitions  UInt8
open Aeres.Grammar.Parallel.TCB UInt8
open Aeres.Grammar.Parser       UInt8

CPSURILit : List UInt8
CPSURILit = # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 1 ]

CPSURI : OIDValue CPSURILit
CPSURI = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length CPSURILit)) CPSURILit)} tt))

UserNoticeLit : List UInt8
UserNoticeLit = # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 2 ]

UserNotice : OIDValue UserNoticeLit
UserNotice = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length UserNoticeLit)) UserNoticeLit)} tt))
