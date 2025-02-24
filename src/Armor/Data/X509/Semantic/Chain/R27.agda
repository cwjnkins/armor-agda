{-# OPTIONS --erasure --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Semantic.Cert.Utils
open import Armor.Data.X509.Semantic.Chain.TCB
import      Armor.Grammar.Option
open import Armor.Prelude

module Armor.Data.X509.Semantic.Chain.R27 where

open Armor.Grammar.Option      UInt8

{- https://datatracker.ietf.org/doc/html/rfc5270#section-6.1.4
--    To prepare for processing of certificate i+1, perform the
--    following steps for certificate i:
--
--    ...
-- 
--    (k) If a key usage extension is present, verify that the keyCertSign bit is set.
-}

module _ {trust candidates : List (Exists─ _ Cert)} {@0 bs} (issuee : Cert bs) where

  IsKeyCertSignPresent : ∀ {@0 bs} → Cert bs → Set
  IsKeyCertSignPresent c = T (certAssertsKUBitField c Extension.KUFields.keyCertSign)

  isKeyCertSignPresent? : ∀ {@0 bs} (c : Cert bs) → Dec (IsKeyCertSignPresent c)
  isKeyCertSignPresent? c = T-dec

  R27 : Chain trust candidates issuee → Set
  R27 c = All (IsKeyCertSignPresent ∘ proj₂) (tailSafe (toList c) (toListLength≥1 c))

  r27 : (c : Chain trust candidates issuee) → Dec (R27 c)
  r27 c = All.all? (isKeyCertSignPresent? ∘ proj₂) _
