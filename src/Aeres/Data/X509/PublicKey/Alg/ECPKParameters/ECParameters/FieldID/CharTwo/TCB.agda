open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.Iso
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.TCB where

open Aeres.Grammar.Definitions.Iso          UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.Seq.TCB                  UInt8

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
-- The object identifiers prime-field and characteristic-two-field name
-- the two kinds of fields defined in this Standard.  They have the
-- following values:
--   Characteristic-two ::= SEQUENCE {
--       m           INTEGER,                      -- Field size 2^m
--       basis       OBJECT IDENTIFIER,
--       parameters  ANY DEFINED BY basis }
--
-}

record CharTwoFields (@0 bs : List UInt8) : Set where
  constructor mkCharTwoFields
  field
    @0 {bs₁ bs₂} : List UInt8
    m : Int bs₁
    basis : BasisFields bs₂
    @0 bs≡ : bs ≡ bs₁ ++ bs₂

CharTwoFieldsRep : @0 List UInt8 → Set
CharTwoFieldsRep = &ₚ Int BasisFields

equivalent : Equivalent CharTwoFieldsRep CharTwoFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkCharTwoFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkCharTwoFields m basis bs≡) = mk&ₚ m basis bs≡

RawCharTwoFieldsRep : Raw CharTwoFieldsRep
RawCharTwoFieldsRep = Raw&ₚ RawInt RawBasisFields

RawCharTwoFields : Raw CharTwoFields
RawCharTwoFields = Iso.raw equivalent RawCharTwoFieldsRep

CharTwo = TLV Tag.Sequence CharTwoFields

RawCharTwo : Raw CharTwo
RawCharTwo = RawTLV _ RawCharTwoFields
