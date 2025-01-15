open import Armor.Binary
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X509.Validity.Time.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.CRL.RevokedCertificates.TCB where

open Armor.Grammar.Seq    UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel.TCB UInt8

-- TBSCertList  ::=  SEQUENCE  {
--      version                 Version OPTIONAL,
--                                   -- if present, MUST be v2
--      signature               AlgorithmIdentifier,
--      issuer                  Name,
--      thisUpdate              Time,
--      nextUpdate              Time OPTIONAL,
--      revokedCertificates     SEQUENCE OF SEQUENCE  {
--           userCertificate         CertificateSerialNumber,
--           revocationDate          Time,
--           crlEntryExtensions      Extensions OPTIONAL
--                                    -- if present, version MUST be v2
--                                }  OPTIONAL,
--      crlExtensions           [0]  EXPLICIT Extensions OPTIONAL
--                                    -- if present, version MUST be v2
--                                }

record RevokedCertificateFields (@0 bs : List UInt8) : Set where
  constructor mkRevokedCertificateFields
  field
    @0 {ser ti ex} : List UInt8
    cserial : Int ser
    rdate : Time ti
    entryextensions : Option EntryExtensions ex
    @0 bs≡  : bs ≡ ser ++ ti ++ ex

RevokedCertificate : (@0 _ : List UInt8) → Set
RevokedCertificate xs = TLV Tag.Sequence RevokedCertificateFields xs

RevokedCertificates : (@0 _ : List UInt8) → Set
RevokedCertificates xs = TLV Tag.Sequence (NonEmptySequenceOf RevokedCertificate) xs

RevokedCertificateFieldsRep : @0 List UInt8 → Set
RevokedCertificateFieldsRep = (&ₚ (&ₚ Int Time) (Option EntryExtensions))

equivalentRevokedCertificateFields : Equivalent RevokedCertificateFieldsRep RevokedCertificateFields
proj₁ equivalentRevokedCertificateFields (mk&ₚ (mk&ₚ fstₚ₁ sndₚ₂ refl) sndₚ₁ bs≡) = mkRevokedCertificateFields fstₚ₁ sndₚ₂ sndₚ₁  (trans₀ bs≡ (solve (++-monoid UInt8)))
proj₂ equivalentRevokedCertificateFields (mkRevokedCertificateFields cserial rdate entryextensions bs≡) = mk&ₚ (mk&ₚ cserial rdate refl) entryextensions (trans₀ bs≡ (solve (++-monoid UInt8)))


RawRevokedCertificateFieldsRep : Raw RevokedCertificateFieldsRep
RawRevokedCertificateFieldsRep = Raw&ₚ (Raw&ₚ RawInt RawTime) (RawOption RawEntryExtensions)

RawRevokedCertificates : Raw RevokedCertificates
RawRevokedCertificates = RawTLV _ (RawBoundedSequenceOf (RawTLV _
                                (Iso.raw equivalentRevokedCertificateFields RawRevokedCertificateFieldsRep)) 1)

module RevokedCertificates where
  getRevokedCertificates : ∀{@0 bs} → (rl : RevokedCertificates bs) → List (Exists─ (List UInt8) RevokedCertificate)
  getRevokedCertificates (mkTLV len (mk×ₚ fstₚ₁ sndₚ₁) len≡ bs≡) = helper fstₚ₁
    where
    helper : ∀ {@0 bs} → SequenceOf RevokedCertificate bs →  List (Exists─ (List UInt8) RevokedCertificate)
    helper nil = []
    helper (consIList h t bs≡) = (_ , h) ∷ helper t
