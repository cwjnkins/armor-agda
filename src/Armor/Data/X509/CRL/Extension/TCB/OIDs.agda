{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X690-DER.OID.Parser
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.CRL.Extension.TCB.OIDs where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Parser       UInt8

AKILit : List UInt8
AKILit = # 85 ∷ # 29 ∷ [ # 35 ]

AKI : OIDValue AKILit
AKI = fstₚ (Success.value (toWitness{a? = Logging.val (runParser (parseOIDValue (length AKILit)) AKILit)} tt))

IANLit : List UInt8
IANLit =  # 85 ∷ # 29 ∷ [ # 18 ]

IAN : OIDValue IANLit
IAN = fstₚ (Success.value (toWitness{a? = Logging.val (runParser (parseOIDValue (length IANLit)) IANLit)} tt))

CRLNLit : List UInt8
CRLNLit =  # 85 ∷ # 29 ∷ [ # 20 ]

CRLNL : OIDValue CRLNLit
CRLNL = fstₚ (Success.value (toWitness{a? = Logging.val (runParser (parseOIDValue (length CRLNLit)) CRLNLit)} tt))

DCRLILit : List UInt8
DCRLILit =  # 85 ∷ # 29 ∷ [ # 27 ]

DCRLI : OIDValue DCRLILit
DCRLI = fstₚ (Success.value (toWitness{a? = Logging.val (runParser (parseOIDValue (length DCRLILit)) DCRLILit)} tt))

IDPLit : List UInt8
IDPLit =  # 85 ∷ # 29 ∷ [ # 28 ]

IDP : OIDValue IDPLit
IDP = fstₚ (Success.value (toWitness{a? = Logging.val (runParser (parseOIDValue (length IDPLit)) IDPLit)} tt))

FCRLLit : List UInt8
FCRLLit =  # 85 ∷ # 29 ∷ [ # 46 ]

FCRL : OIDValue FCRLLit
FCRL = fstₚ (Success.value (toWitness{a? = Logging.val (runParser (parseOIDValue (length FCRLLit)) FCRLLit)} tt))

AIALit : List UInt8
AIALit = # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 1 ∷ [ # 1 ]

AIA : OIDValue AIALit
AIA = fstₚ (Success.value (toWitness{a? = Logging.val (runParser (parseOIDValue (length AIALit)) AIALit)} tt))
