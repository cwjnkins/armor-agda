open import Aeres.Prelude
open import Aeres.Arith

open import Data.Fin.Properties
  renaming (≤-refl to Fin-≤-refl ; ≤-trans to Fin-≤-trans ; suc-injective to Fin-suc-injective)
  hiding   (_≟_)
open import Data.Nat.Induction
  hiding (Acc)
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Binary where

Binary = Vec Bool

pattern #0 = false
pattern #1 = true

toBinary : ∀ {n} → Fin (2 ^ n) → Binary n
toBinary{n} i = Vec.reverse $ help n (toℕ i) (toℕ<n i) (<-wellFounded (toℕ i))
  where
  help : (n : ℕ) (i : ℕ) (i< : i < 2 ^ n) → Acc _<_ i → Binary n
  help zero i i< ac = []
  help (suc n) 0 i< (acc rs) = Vec.replicate #0
  help (suc n) 1 i< (acc rs) = #1 ∷ Vec.replicate #0
  help (suc n) i@(suc (suc i')) i< (acc rs)
    with divmod2-≤ i'
  ...| q≤i'
    with divmod2 i'
    | inspect divmod2 i'
  ... | q , r | [ eq ]R = r ∷ help n (suc q) pf (rs (suc q) (s≤s (s≤s q≤i')))
    where
    pf : 1 + q < 2 ^ n
    pf rewrite sym (cong proj₁ eq) = divmod2-<-^ i' n i<

fromBinary : ∀ {n} → Binary n → Fin (2 ^ n)
fromBinary bits = go (Vec.reverse bits)
  where
  go : ∀ {n} → Vec Bool n → Fin (2 ^ n)
  go {.0} [] = Fin.zero
  go {n@.(suc _)} (#0 ∷ bits) rewrite sym (suc[pred[n]]≡n{2 ^ n} (2^n≢0 n)) =
    Fin.inject₁ (Fin.2* (go bits))
  go {n@.(suc _)} (#1 ∷ bits) rewrite sym (suc[pred[n]]≡n{2 ^ n} (2^n≢0 n)) =
    Fin.fromℕ 1 Fin.+ (Fin.2* (go bits))

-- TODO: prove `fromBinary` and `toBinary` form an isomorphism

private
  test₁ : toℕ (fromBinary (#1 ∷ #0 ∷ #0 ∷ Vec.[ #1 ])) ≡ 9
  test₁ = refl

  test₂ : toBinary (Fin.inject+ _ (Fin.fromℕ 9)) ≡ #1 ∷ #0 ∷ #0 ∷ Vec.[ #1 ]
  test₂ = refl

module Base256 where
  Byte = Binary 8
  Dig  = Fin (2 ^ 8)

module Base128 where
  Byte = Binary 7
  Dig  = Fin (2 ^ 7)

module Base64 where
  Byte = Binary 6
  Dig  = Fin (2 ^ 6)

  charset : List Char
  charset = String.toList "ABCDEFGHIJKLMNOPQRStUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

  isByteRep : ∀ c → Dec (c ∈ charset)
  isByteRep c = Any.any (c ≟_) charset

  toByte : Char → Maybe Byte
  toByte c
    with isByteRep c
  ...| no  c∉charset = nothing
  ...| yes c∈charset = just (toBinary (Any.index c∈charset))

  isPad : ∀ c → Dec (c ≡ '=')
  isPad = _≟ '='

module Bytes where
  base64To256 : Vec Base64.Byte 4 → Vec Base256.Byte 3
  base64To256
    (  (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ [])
     ∷ (b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ [])
     ∷ (b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ b₃₅ ∷ b₃₆ ∷ [])
     ∷ (b₄₁ ∷ b₄₂ ∷ b₄₃ ∷ b₄₄ ∷ b₄₅ ∷ b₄₆ ∷ [])
     ∷ [])
    =   (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ b₂₁ ∷ b₂₂ ∷ [])
      ∷ (b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ [])
      ∷ (b₃₅ ∷ b₃₆ ∷ b₄₁ ∷ b₄₂ ∷ b₄₃ ∷ b₄₄ ∷ b₄₅ ∷ b₄₆ ∷ [])
      ∷ []

module EncDec64 where

  decode4 : ∀ {n} → Vec Base64.Dig (4 * n) → Vec Base256.Dig (3 * n)
  decode4 {zero} cs = []
  decode4 {suc n} cs
    with *-distribˡ-+ 4 1 n
  ...| pf
    with 4 * (1 + n)
  decode4 {suc n} cs | refl | ._
    with *-distribˡ-+ 3 1 n
  ...| pf'
    with 3 * (1 + n)
  decode4 {suc n} cs | refl | ._ | refl | ._ =
    Vec._++_ {m = 3}{3 * n}
      (Vec.map fromBinary (Bytes.base64To256 (Vec.take 4 (Vec.map toBinary cs))))
      (decode4{n} (Vec.drop 4 cs))
