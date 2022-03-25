{-# OPTIONS --subtyping --sized-types #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties
import      Aeres.Grammar.Definitions
open import Aeres.Grammar.IList
import      Aeres.Grammar.Sum
open import Aeres.Prelude

open import Aeres.Data.UTF8
open import Aeres.Data.UTF8.Serializer
open import Aeres.Data.UTF8.Trie
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Combine
import      Data.Nat.Properties as Nat
open import Data.These.Base

module Aeres.Data.X509.Semantic.StringPrep.Exec where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig


spaceUTF8 : Exists─ (List UInt8) UTF8
spaceUTF8 = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 32) (toWitness {Q = 32 <? 128 } tt) refl)) nil refl)

appendUTF8 : Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8
appendUTF8 (fst , snd) (fst₁ , snd₁) = _ , (appendIList _ snd snd₁)

lookupB2Map : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
lookupB2Map x 
  with lookupUTF8Trie (serializeUTF8Char' x) B2Map
... | nothing = _ , (cons (mkIListCons x nil refl))
... | just x₁
  with x₁
... | this x₂ = x₂
... | that x₃ = _ , (cons (mkIListCons x nil refl))
... | these x₂ x₃ = x₂

checkOnlySpaces : ∀ {@0 bs} → UTF8 bs → Bool
checkOnlySpaces nil = true
checkOnlySpaces (cons (mkIListCons (utf81 (mkUTF8Char1 b₁ b₁range bs≡₁)) tail₁ bs≡))
  with toℕ b₁ ≟ 32
... | no ¬p = false
... | yes p = checkOnlySpaces tail₁
checkOnlySpaces (cons (mkIListCons (utf82 x) tail₁ bs≡)) = false
checkOnlySpaces (cons (mkIListCons (utf83 x) tail₁ bs≡)) = false
checkOnlySpaces (cons (mkIListCons (utf84 x) tail₁ bs≡)) = false

lstripUTF8 : ∀ {@0 bs} → (bsname : UTF8 bs) → Exists─ (List UInt8) (Σₚ UTF8 (λ xs a → lengthIList _ a ≤ lengthIList _ bsname))
lstripUTF8 nil = _ , (Aeres.Grammar.Definitions.mk×ₚ nil z≤n refl)
lstripUTF8 a@(cons (mkIListCons (utf81 (mkUTF8Char1 b₁ b₁range bs≡₁)) tail₁ bs≡))
  with toℕ b₁ ≟ 32
... | no ¬p = _ , (Aeres.Grammar.Definitions.mk×ₚ a (s≤s Nat.≤-refl) refl)
... | yes p
  with lstripUTF8 tail₁
... | fst , Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ refl = fst , (Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ (Nat.≤-step sndₚ₁) refl)
lstripUTF8 a@(cons (mkIListCons (utf82 x) tail₁ bs≡)) = _ , (Aeres.Grammar.Definitions.mk×ₚ a (s≤s Nat.≤-refl) refl)
lstripUTF8 a@(cons (mkIListCons (utf83 x) tail₁ bs≡)) = _ , (Aeres.Grammar.Definitions.mk×ₚ a (s≤s Nat.≤-refl) refl)
lstripUTF8 a@(cons (mkIListCons (utf84 x) tail₁ bs≡)) = _ , (Aeres.Grammar.Definitions.mk×ₚ a (s≤s Nat.≤-refl) refl)

lstripUTF8' : ∀ {@0 bs} → (bsname : UTF8 bs) → Exists─ (List UInt8) UTF8
lstripUTF8' bsname
  with lstripUTF8 bsname
... | fst , snd = _ , fstₚ snd

rstripUTF8 : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
rstripUTF8 x = reverseIList _ (proj₂ (lstripUTF8' (proj₂ (reverseIList _ x))))

stripUTF8 :  ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
stripUTF8 x = rstripUTF8 (proj₂ (lstripUTF8' x))

addSpacesStartEnd :  ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
addSpacesStartEnd x = _ , (appendIList _ (appendIList _ (proj₂ spaceUTF8) x) (proj₂ spaceUTF8))

innerSeqSpaceHelperWF : ∀ {@0 bs ss} → (bsname : UTF8 bs) → Acc _<_ (lengthIList _ bsname) → UTF8 ss → Exists─ (List UInt8) UTF8
innerSeqSpaceHelperWF IList.nil ac x₁ = _ , x₁
innerSeqSpaceHelperWF (cons (mkIListCons (utf81 x@(mkUTF8Char1 b₁ b₁range bs≡₁)) tail₁ bs≡)) (WellFounded.acc rs) x₁
  with toℕ b₁ ≟ 32
... | no ¬p = innerSeqSpaceHelperWF tail₁ (rs (lengthIList _ tail₁) Nat.≤-refl) (appendIList _ x₁ (cons (mkIListCons (utf81 x) nil refl)))
... | yes p
  with lstripUTF8 tail₁
... | fst , Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡₂ = innerSeqSpaceHelperWF fstₚ₁ (rs (lengthIList _ fstₚ₁) (s≤s sndₚ₁)) (((appendIList _ x₁ (appendIList _ (proj₂ spaceUTF8) (proj₂ spaceUTF8)))))
innerSeqSpaceHelperWF (cons (mkIListCons (utf82 x) tail₁ bs≡)) (WellFounded.acc rs) x₁ =
  innerSeqSpaceHelperWF tail₁ (rs (lengthIList _ tail₁) Nat.≤-refl) (appendIList _ x₁ (cons (mkIListCons (utf82 x) nil refl)))
innerSeqSpaceHelperWF (cons (mkIListCons (utf83 x) tail₁ bs≡)) (WellFounded.acc rs) x₁ =
  innerSeqSpaceHelperWF tail₁ (rs (lengthIList _ tail₁) Nat.≤-refl) (appendIList _ x₁ (cons (mkIListCons (utf83 x) nil refl)))
innerSeqSpaceHelperWF (cons (mkIListCons (utf84 x) tail₁ bs≡)) (WellFounded.acc rs) x₁ =
  innerSeqSpaceHelperWF tail₁ (rs (lengthIList _ tail₁) Nat.≤-refl) (appendIList _ x₁ (cons (mkIListCons (utf84 x) nil refl)))

innerSeqSpaceHelper : ∀ {@0 bs ss} → (bsname : UTF8 bs) → UTF8 ss → Exists─ (List UInt8) UTF8
innerSeqSpaceHelper bsname = innerSeqSpaceHelperWF bsname (<-wellFounded _)
  where open import Data.Nat.Induction


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

postulate
  InitialMapping : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
  Prohibit : ∀ {@0 bs} → UTF8 bs → Bool

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



-- CaseFoldingNFKCTest : ∀ {@0 bs} → UTF8Char1 bs → Exists─ (List UInt8) UTF8Char1
-- CaseFoldingNFKCTest = mapUTF8Char1Range 65 26 (ℤ.+ 32) (toWitness  {Q = _ ℤ.≤? _ } tt) (toWitness  {Q = _ ℤ.≤? _ } tt)

-- -- CaseFoldingNFKCTest nil = _ , nil
-- -- CaseFoldingNFKCTest (cons (mkIListCons head₁ tail₁ bs≡)) = case inRange? 'A' 'Z' head₁ of λ where
-- --   (no ¬p) → appendUTF8 (_ , cons (mkIListCons head₁ nil refl)) (CaseFoldingNFKCTest tail₁)
-- --   (yes p) → appendUTF8 (_ , cons (mkIListCons (utf81 (mkUTF8Char1 {!!} {!!} {!!})) nil refl)) {!!}




-- 192 155 -- 192 156
-- 192 157 --
-- 192 159
