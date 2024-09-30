open import Armor.Binary
open import Armor.Data.X690-DER.OID.Parser
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB.OIDs where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Parser       UInt8

REASONLit : List UInt8
REASONLit = # 85 ∷ # 29 ∷ [ # 21 ]

REASON : OIDValue REASONLit
REASON = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length REASONLit)) REASONLit)} tt))

INVALIDITYLit : List UInt8
INVALIDITYLit =  # 85 ∷ # 29 ∷ [ # 24 ]

INVALIDITY : OIDValue INVALIDITYLit
INVALIDITY = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length INVALIDITYLit)) INVALIDITYLit)} tt))

CERTISSUERLit : List UInt8
CERTISSUERLit =  # 85 ∷ # 29 ∷ [ # 29 ]

CERTISSUER : OIDValue CERTISSUERLit
CERTISSUER = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length CERTISSUERLit)) CERTISSUERLit)} tt))
