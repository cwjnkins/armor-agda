{-# OPTIONS --subtyping --sized-types #-}

open import Data.Nat.DivMod
import      Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
open import Aeres.Grammar.IList
import      Aeres.Grammar.Sum
open import Aeres.Prelude

open import Aeres.Data.Unicode
open import Aeres.Data.Unicode.UTF8.Trie
open import Aeres.Data.X509.Semantic.StringPrep.Common

import      Data.Nat.Properties as Nat
open import Data.These.Base

open import Aeres.Data.X509.Semantic.StringPrep.ExcludeRange

module Aeres.Data.X509.Semantic.StringPrep.ExecIS where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig

-- https://datatracker.ietf.org/doc/html/rfc4518#section-2.1
   -- Each non-Unicode string value is transcoded to Unicode.

   -- PrintableString [X.680] values are transcoded directly to Unicode.

   -- UniversalString, UTF8String, and bmpString [X.680] values need not be
   -- transcoded as they are Unicode-based strings (in the case of
   -- bmpString, a subset of Unicode).

   -- TeletexString [X.680] values are transcoded to Unicode.  As there is
   -- no standard for mapping TeletexString values to Unicode, the mapping
   -- is left a local matter.

   -- For these and other reasons, use of TeletexString is NOT RECOMMENDED.

   -- The output is the transcoded string.
   
TranscodeIS : ∀ {@0 bs} → IA5String bs → String ⊎ Exists─ (List UInt8) Unicode
TranscodeIS (mkTLV len (mkIA5StringValue str all<128) len≡ bs≡) = inj₂ (_ , utf8 (helper (toWitness all<128)))
  where
  helper :  ∀ {bs} → @0 All (Fin._< # 128) bs → UTF8 bs
  helper {[]} x = nil
  helper {x₁ ∷ bs} (px ∷ x) = cons (mkIListCons (utf81 (mkUTF8Char1 x₁ px refl)) (helper x) refl)

-- https://datatracker.ietf.org/doc/html/rfc4518#section-2
   -- The following six-step process SHALL be applied to each presented and
   -- attribute value in preparation for character string matching rule
   -- evaluation.

   --    1) Transcode
   --    2) Map
   --    3) Normalize
   --    4) Prohibit
   --    5) Check bidi
   --    6) Insignificant Character Handling

-- Note: TODO: Check bidi (https://datatracker.ietf.org/doc/html/rfc4518#section-2.5)

ProcessStringIS : ∀ {@0 bs} → IA5String bs → String ⊎ Exists─ (List UInt8) Unicode
ProcessStringIS str
  with TranscodeIS str
... | inj₁ err = inj₁ err
... | inj₂ ts
  with InitialMapping (proj₂ ts)
... | ims
  with CaseFoldingNFKC (proj₂ ims)
... | ms
  with Prohibit (proj₂ ms)
... | true = inj₁ "error in stringprep : prohibitted unicode character present"
... | false = inj₂ (InsigCharHandling (proj₂ ms))


CompareIS : ∀ {@0 bs₁ bs₂} → IA5String bs₁ → IA5String bs₂ → Set
CompareIS x x₁
  with ProcessStringIS x
... | inj₁ err = ⊥
... | inj₂ a
  with ProcessStringIS x₁
... | inj₁ err = ⊥
... | inj₂ b = _≋_ {A = Unicode} (proj₂ a) (proj₂ b)

--------------------------------------------- decidable proofs -------------------------------------------------------

CompareIS-dec : ∀ {@0 bs₁ bs₂} (xs₁ : IA5String bs₁) → (xs₂ : IA5String bs₂) → Dec (CompareIS xs₁ xs₂)
CompareIS-dec x₁ x₂
  with ProcessStringIS x₁
... | inj₁ err = no (λ ())
... | inj₂ a
  with ProcessStringIS x₂
... | inj₁ err = no (λ ())
--... | inj₂ b = 
... | inj₂ b = _≋?_{A = Unicode} (proj₂ a) (proj₂ b)
