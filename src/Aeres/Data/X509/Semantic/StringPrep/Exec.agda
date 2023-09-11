{-# OPTIONS --subtyping --sized-types --allow-unsolved-metas #-}

open import Data.Nat.DivMod
import      Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
open import Aeres.Grammar.IList
import      Aeres.Grammar.Sum
open import Aeres.Prelude

open import Aeres.Data.Unicode
open import Aeres.Data.Unicode.UTF8.Trie
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


-- Note: Currently, we only transform unicode strings encoded in UTF8. For UTF16 and UTF32, we do not perform any transformation before comparison.

appendUTF8 : Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8
appendUTF8 (fst , snd) (fst₁ , snd₁) = _ , (appendIList _ snd snd₁)


Transcode : ∀ {@0 bs} → DirectoryString bs → String ⊎ Exists─ (List UInt8) Unicode
Transcode (teletexString x) = inj₁ "error in stringprep : teletexstring not supported" 
Transcode (printableString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len val len≡ bs≡₁) sndₚ₁ bs≡)) = inj₂ (_ , (utf8 (proj₂ (helper val))))
  where
  helper :  ∀ {@0 bs} → IList UInt8 PrintableString.PrintableStringChar bs  → Exists─ (List UInt8) UTF8
  helper nil = _ , nil
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 32) PrintableString.space bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 32) (toWitness {Q = 32 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 39) PrintableString.apostrophe bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 39) (toWitness {Q = 39 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 40) PrintableString.leftParen bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 40) (toWitness {Q = 40 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 41) PrintableString.rightParen bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 41) (toWitness {Q = 41 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 43) PrintableString.plus bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 43) (toWitness {Q = 43 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 44) PrintableString.comma bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 44) (toWitness {Q = 44 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 45) PrintableString.hyphen bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 45) (toWitness {Q = 45 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 46) PrintableString.period bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 46) (toWitness {Q = 46 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 47) PrintableString.fslash bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 47) (toWitness {Q = 47 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar c (PrintableString.numbers (fst , snd)) bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 c (Nat.≤-trans (s≤s snd) (toWitness {Q = 57 <? 128} tt)) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 58) PrintableString.colon bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 58) (toWitness {Q = 58 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 61) PrintableString.equals bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 61) (toWitness {Q = 61 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 63) PrintableString.question bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 63) (toWitness {Q = 63 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar c (PrintableString.uppers (fst , snd)) bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 c (Nat.≤-trans (s≤s snd) (toWitness {Q = 90 <? 128} tt)) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar c (PrintableString.lowers (fst , snd)) bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 c (Nat.≤-trans (s≤s snd) (toWitness {Q = 122 <? 128} tt)) bs≡₁)) (proj₂ (helper tail₁)) refl)
Transcode (universalString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len val len≡ bs≡₁) sndₚ₁ refl)) = inj₂ (_ , utf32 val)
Transcode (utf8String (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len val len≡ bs≡₁) sndₚ₁ refl)) = inj₂ (_ , utf8 val)
Transcode (bmpString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len val len≡ bs≡₁) sndₚ₁ refl)) = inj₂ (_ , utf16 val)
Transcode (ia5String (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len (mkIA5StringValue str all<128) len≡ bs≡₁) sndₚ₁ refl)) = inj₂ (_ , utf8 (helper (toWitness all<128)))
  where
  helper :  ∀ {bs} → @0 All (Fin._< # 128) bs → UTF8 bs
  helper {[]} x = nil
  helper {x₁ ∷ bs} (px ∷ x) = cons (mkIListCons (utf81 (mkUTF8Char1 x₁ px refl)) (helper x) refl)


InitialMapping : ∀ {@0 bs} → Unicode bs → Exists─ (List UInt8) Unicode
InitialMapping (utf8 nil) = _ , utf8 nil
InitialMapping (utf8 (cons (mkIListCons h t bs≡))) = _ , (utf8 (proj₂ (helper h t)))
  where
  helper : ∀ {@0 bs₁ bs₂} → UTF8Char bs₁ → IList UInt8 UTF8Char bs₂ → Exists─ (List UInt8) UTF8
  helper x nil = case (checkDeleteList x) of λ where
    true → _ , nil
    false → lookupInitMap x
  helper x (cons (mkIListCons head₁ tail₁ bs≡)) = case (checkDeleteList x) of λ where
    true → appendUTF8 (_ , nil) (helper head₁ tail₁)
    false → appendUTF8 (lookupInitMap x) (helper head₁ tail₁)
InitialMapping (utf16 x) = _ , (utf16 x) -- TODO
InitialMapping (utf32 x) = _ , (utf32 x) -- TODO


Prohibit : ∀ {@0 bs} → Unicode bs → Bool
Prohibit (utf8 nil) = false
Prohibit (utf8 (cons (mkIListCons h t bs≡))) = helper h t
  where
  helper :  ∀ {@0 bs₁ bs₂} → UTF8Char bs₁ → IList UInt8 UTF8Char bs₂ → Bool
  helper x nil = checkProhibitUTF8Char x
  helper x (cons (mkIListCons head₁ tail₁ bs≡)) = case (checkProhibitUTF8Char x) of λ where
    true → true
    false → helper head₁ tail₁
Prohibit (utf16 x) = false -- TODO
Prohibit (utf32 x) = false -- TODO


CaseFoldingNFKC : ∀ {@0 bs} → Unicode bs → Exists─ (List UInt8) Unicode
CaseFoldingNFKC (utf8 nil) = _ , utf8 nil
CaseFoldingNFKC (utf8 (cons (mkIListCons h t bs≡))) =  _ , (utf8 (proj₂ (helper h t)))
  where
  helper :  ∀ {@0 bs₁ bs₂} → UTF8Char bs₁ → IList UInt8 UTF8Char bs₂ → Exists─ (List UInt8) UTF8
  helper x nil = lookupB2Map x
  helper x (cons (mkIListCons head₁ tail₁ bs≡)) = appendUTF8 (lookupB2Map x) (helper head₁ tail₁)
CaseFoldingNFKC (utf16 x) = _ , (utf16 x) -- TODO
CaseFoldingNFKC (utf32 x) = _ , (utf32 x) -- TODO


InsigCharHandling : ∀ {@0 bs} → Unicode bs → Exists─ (List UInt8) Unicode
InsigCharHandling (utf8 x)
  with checkOnlySpaces x
  ---- output only two spaces
... | true = _ , (utf8 (appendIList _ (proj₂ spaceUTF8) (proj₂ spaceUTF8)))
  ---- else, ensure one space at start and end, two space per seq of inner spaces
... | false = _ , (utf8 (appendIList _ (appendIList _ (proj₂ spaceUTF8) (proj₂ (innerSeqSpaceHelper (proj₂ (stripUTF8 x)) nil))) (proj₂ spaceUTF8)))
InsigCharHandling (utf16 x) = _ , (utf16 x) -- TODO
InsigCharHandling (utf32 x) = _ , (utf32 x) -- TODO


ProcessString : ∀ {@0 bs} → DirectoryString bs → String ⊎ Exists─ (List UInt8) Unicode
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


Compare : ∀ {@0 bs₁ bs₂} → DirectoryString bs₁ → DirectoryString bs₂ → Set
Compare x x₁
  with ProcessString x
... | inj₁ err = ⊥
... | inj₂ a
  with ProcessString x₁
... | inj₁ err = ⊥
... | inj₂ b = _≋_ {A = Unicode} (proj₂ a) (proj₂ b)

--------------------------------------------- decidable proofs -------------------------------------------------------

Compare-dec : ∀ {@0 bs₁ bs₂} (xs₁ : DirectoryString bs₁) → (xs₂ : DirectoryString bs₂) → Dec (Compare xs₁ xs₂)
Compare-dec x₁ x₂
  with ProcessString x₁
... | inj₁ err = no (λ ())
... | inj₂ a
  with ProcessString x₂
... | inj₁ err = no (λ ())
--... | inj₂ b = 
... | inj₂ b = _≋?_{A = Unicode} (proj₂ a) (proj₂ b)
