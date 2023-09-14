{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.DirectoryString
import      Aeres.Data.X690-DER.OID.Properties as OID
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X509.RDN.ATV.OIDs
open import Aeres.Data.X509.RDN.ATV.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.Strings.IA5String
open import Aeres.Data.X690-DER.Strings.PrintableString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.RDN.ATV.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous ATV
unambiguous = TLV.unambiguous (DefinedByOID.unambiguous _ λ o → u o ((-, TLV.val o) ∈? Supported))
  where
  u : ∀ {@0 bs} → (o : OID bs) (d : Dec ((-, TLV.val o) ∈ Supported)) → Unambiguous (ATVParam o d)
  u o (no ¬p) = DirectoryString.unambiguous
  u o (yes (here px)) = PrintableString.unambiguous
  u o (yes (there (here px))) = unambiguousΣₚ PrintableString.unambiguous (λ _ → inRange-unique{A = ℕ}{B = ℕ})
  u o (yes (there (there (here px)))) = PrintableString.unambiguous
  u o (yes (there (there (there (here px))))) = TLV.unambiguous IA5String.unambiguous

instance
  Eq≋ATV : Eq≋ (DefinedByOIDFields  λ o → ATVParam o ((-, TLV.val o) ∈? Supported))
  Eq≋ATV = DefinedByOID.eq≋ _ λ o → eq o ((-, TLV.val o) ∈? Supported)
    where
    eq : ∀ {@0 bs} (o : OID bs) (d : Dec ((-, TLV.val o) ∈ Supported)) → Eq≋ (ATVParam o d)
    eq o (no ¬p) = it
    eq o (yes (here px)) = it
    eq o (yes (there (here px))) = eq≋Σₚ it (λ _ → record { _≟_ = λ x y → yes (inRange-unique{A = ℕ}{B = ℕ} x y) })
    eq o (yes (there (there (here px)))) = it
    eq o (yes (there (there (there (here px))))) = it
