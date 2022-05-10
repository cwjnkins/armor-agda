{-# OPTIONS --subtyping --sized-types #-}

open import Data.Nat.DivMod
import      Aeres.Binary
open import Aeres.Data.X509
import Aeres.Data.X509.Properties as Props
import      Aeres.Grammar.Definitions
open import Aeres.Grammar.IList
import      Aeres.Grammar.Sum
open import Aeres.Prelude

open import Aeres.Data.UTF8
open import Aeres.Data.UTF8.Properties
open import Aeres.Data.UTF8.Serializer
open import Aeres.Data.UTF8.Trie
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers
open import Aeres.Data.X509.Semantic.StringPrep.InitMap.Helpers
open import Aeres.Data.X509.Semantic.StringPrep.InsigCharHandler.Helpers
open import Aeres.Data.X509.Semantic.StringPrep.ProhibitList.Helpers

import      Data.Nat.Properties as Nat
open import Data.These.Base

open import Aeres.Data.X509.Semantic.StringPrep.ExcludeRange

module Aeres.Data.X509.Semantic.StringPrep.Exec where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig


appendUTF8 : Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8
appendUTF8 (fst , snd) (fst₁ , snd₁) = _ , (appendIList _ snd snd₁)

Transcode : ∀ {@0 bs} → X509.DirectoryString bs → String ⊎ Exists─ (List UInt8) UTF8
Transcode (X509.teletexString x) = inj₁ "error in stringprep : teletexstring not supported" 
Transcode (X509.printableString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len (X509.mkIA5StringValue (singleton x refl) all<128) len≡ bs≡₁) sndₚ₁ bs≡)) = inj₂ (helper x all<128)
  where
  helper : (ss : List UInt8) → @0 All (Fin._< # 128) ss → Exists─ (List UInt8) UTF8
  helper [] All.[] = _ , nil
  helper (x ∷ xs) (px All.∷ x₁) = _ , (cons (mkIListCons (utf81 (mkUTF8Char1 x px refl)) (proj₂ (helper xs x₁)) refl))
Transcode (X509.universalString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len val len≡ refl) sndₚ₁ refl)) = inj₂ (_ , val)
Transcode (X509.utf8String (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len val len≡ refl) sndₚ₁ refl)) = inj₂ (_ , val)
Transcode (X509.bmpString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len val len≡ refl) sndₚ₁ refl)) = inj₂ (_ , val)

InitialMapping : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
InitialMapping nil = _ , nil
InitialMapping (cons (mkIListCons head₁ tail₁ bs≡)) = case (checkDeleteList head₁) of λ where
  true → appendUTF8 (_ , nil) (InitialMapping tail₁)
  false → appendUTF8 (lookupInitMap head₁) (InitialMapping tail₁)

Prohibit : ∀ {@0 bs} → UTF8 bs → Bool
Prohibit nil = false
Prohibit (cons (mkIListCons head₁ tail₁ bs≡)) = case (checkProhibitUTF8Char head₁) of λ where
  true → true
  false → Prohibit tail₁

CaseFoldingNFKC : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
CaseFoldingNFKC nil = _ , nil
CaseFoldingNFKC (cons (mkIListCons head₁ tail₁ bs≡)) = appendUTF8 (lookupB2Map head₁) (CaseFoldingNFKC tail₁)

InsigCharHandling : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
InsigCharHandling x
  with checkOnlySpaces x
  ---- output only two spaces
... | true = _ , appendIList _ (proj₂ spaceUTF8) (proj₂ spaceUTF8)
  ---- else, ensure one space at start and end, two space per seq of inner spaces
... | false = _ , appendIList _ (appendIList _ (proj₂ spaceUTF8) (proj₂ (innerSeqSpaceHelper (proj₂ (stripUTF8 x)) nil))) (proj₂ spaceUTF8)

ProcessString : ∀ {@0 bs} → X509.DirectoryString bs → String ⊎ Exists─ (List UInt8) UTF8
ProcessString str
  with Transcode str
... | inj₁ err = inj₁ err
... | inj₂ ts
  with InitialMapping (proj₂ ts)
... | ims
  with CaseFoldingNFKC (proj₂ ims)
... | ms
  with Prohibit (proj₂ ms)
... | true = inj₁ "error in stringprep : prohibitted unicode character present"
... | false = inj₂ (InsigCharHandling (proj₂ ms))

Compare : ∀ {@0 bs₁ bs₂} → X509.DirectoryString bs₁ → X509.DirectoryString bs₂ → Set
Compare x x₁
  with ProcessString x
... | inj₁ err = ⊥
... | inj₂ a
  with ProcessString x₁
... | inj₁ err = ⊥
... | inj₂ b = _≋_ {A = UTF8} (proj₂ a) (proj₂ b)


--------------------------------------------- decidable proofs -------------------------------------------------------

Compare-dec : ∀ {@0 bs₁ bs₂} (xs₁ : X509.DirectoryString bs₁) → (xs₂ : X509.DirectoryString bs₂) → Dec (Compare xs₁ xs₂)
Compare-dec x₁ x₂
  with ProcessString x₁
... | inj₁ err = no (λ ())
... | inj₂ a
  with ProcessString x₂
... | inj₁ err = no (λ ())
--... | inj₂ b = 
... | inj₂ b = _≋?_ {A = UTF8} (proj₂ a) (proj₂ b)
