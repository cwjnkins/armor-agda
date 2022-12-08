{-# OPTIONS --inversion-max-depth=100 #-}

open import Aeres.Arith using (divmod2 ; 2^n≢0 ; 1≤10^n; divmod2-*2)
open import Aeres.Prelude
open import Data.Fin.Properties as Fin
  renaming (≤-refl to Fin-≤-refl ; ≤-trans to Fin-≤-trans ; suc-injective to Fin-suc-injective)
  hiding   (_≟_)
open import Data.Nat.Induction
  hiding (Acc)
open import Data.Nat.Properties as Nat
  hiding (_≟_)
import      Data.Sign

module Aeres.Binary where

module Sign = Data.Sign

Binary = Vec Bool

pattern #0 = false
pattern #1 = true

module ToBinary where
  help : (n : ℕ) (i : ℕ) → Binary n
  help 0 i = []
  help (suc n) i
    with divmod2 i
  ... | q , r = r ∷ help n q
  -- help (suc n) 0 = Vec.replicate #0
  -- help (suc n) 1 = #1 ∷ Vec.replicate #0
  -- help (suc n) i@(suc (suc i'))
  --   with divmod2 i
  -- ... | q , r = r ∷ help n q

  toBinary : ∀ {n} → Fin (2 ^ n) → Binary n
  toBinary{n} i = Vec.reverse $ help n (toℕ i)

open ToBinary public using (toBinary)

fromBinary : ∀ {n} → Binary n → Fin (2 ^ n)
fromBinary bits = go (Vec.reverse bits)
  where
  go : ∀ {n} → Vec Bool n → Fin (2 ^ n)
  go {.0} [] = Fin.zero
  go {n@.(suc _)} (#0 ∷ bits) =
    subst Fin (suc[pred[n]]≡n {2 ^ n} (2^n≢0 n)) (Fin.inject₁ (Fin.2* (go bits)))
  go {n@.(suc _)} (#1 ∷ bits) =
    subst Fin (suc[pred[n]]≡n{2 ^ n} (2^n≢0 n)) (Fin.fromℕ 1 Fin.+ (Fin.2* (go bits)))

-- TODO: postulate
toBinary-injective : ∀ {n} → (i₁ i₂ : Fin (2 ^ n)) → toBinary{n} i₁ ≡ toBinary{n} i₂ → i₁ ≡ i₂
toBinary-injective i₁ i₂ i≡ = {!!}
  where
  open ≡-Reasoning
  module ≤ = ≤-Reasoning

  lem₁ : ∀ n i → 1 ≤ n → 1 ≤ i → i < 2 ^ n → ToBinary.help n i ≢ Vec.replicate #0
  lem₁ (suc n) i 1≤n 1≤i i<2^n
    with divmod2 i
    |    divmod2-*2 i
  ... | q , #1 | i≡ = λ ()
  ... | zero , #0 | refl = contradiction 1≤i (λ ())
  lem₁ 1 ._ 1≤n 1≤i (s≤s (s≤s ())) | suc zero , #0 | refl
  lem₁ 1 i 1≤n 1≤i i<2^n | suc (suc q) , #0 | i≡ =
    {!!}
    where
    i≥ : 4 ≤ i
    i≥ = ≤.begin
      (4 ≤.≤⟨ m≤m+n 4 (q + q) ⟩
      4 + (q + q) ≤.≡⟨ {!!} ⟩
      {!!})
  lem₁ (suc (suc n)) i 1≤n 1≤i i<2^n | suc q , #0 | i≡ = {!!}

  help : ∀ {n} (i₁ i₂ : Fin (2 ^ n))
         → (n₁ : Singleton (toℕ i₁)) (n₂ : Singleton (toℕ i₂))
         → ToBinary.help n (↑ n₁) ≡ ToBinary.help n (↑ n₂)
         → i₁ ≡ i₂
  help {zero} Fin.zero Fin.zero (singleton n₁ n₁≡) (singleton n₂ n₂≡) x = refl
  help {suc n} i₁ i₂ (singleton zero n₁≡) (singleton zero n₂≡) x =
    toℕ-injective (begin
      toℕ i₁ ≡⟨ ‼ sym n₁≡ ⟩
      0 ≡⟨ ‼ n₂≡ ⟩
      toℕ i₂ ∎)
  help {suc n} i₁ i₂ (singleton zero n₁≡) (singleton (suc n₂) n₂≡) x = {!!}
  help {suc n} i₁ i₂ (singleton (suc n₁) n₁≡) (singleton zero n₂≡) x = {!!}
  help {suc n} i₁ i₂ (singleton (suc n₁) n₁≡) (singleton (suc n₂) n₂≡) x = {!!}

  open import Agda.Builtin.TrustMe

-- TODO postulate
fromBinary∘toBinary : ∀ {n} → (i : Fin (2 ^ n)) → fromBinary (toBinary{n} i) ≡ i
fromBinary∘toBinary i
  with toℕ i | inspect Fin.toℕ i
fromBinary∘toBinary {zero} Fin.zero | i' | i'Is = refl
fromBinary∘toBinary {suc n} i | zero | i'Is = primTrustMe
  where
  open import Agda.Builtin.TrustMe
  -- TODO: show reverse of replicate is replicate
fromBinary∘toBinary {suc n} i | suc i' | i'Is = primTrustMe
  where
  open import Agda.Builtin.TrustMe

private
  test₁ : toℕ (fromBinary (#1 ∷ #0 ∷ #0 ∷ Vec.[ #1 ])) ≡ 9
  test₁ = refl

  test₂ : toBinary (# 9) ≡ #0 ∷ #1 ∷ #0 ∷ #0 ∷ Vec.[ #1 ]
  test₂ = {!!}


UInt8 = Fin (2 ^ 8)

module Base256 where
  Byte  = Binary 8
  Dig   = Fin (2 ^ 8)

  twosComplement : List Dig → ℤ
  twosComplement xs = go (reverse xs) 0 0
    where
    go : List Dig → (i sum : ℕ) → ℤ
    go [] _ _ = ℤ.+ 0
    go (x ∷ []) i sum =
      if ⌊ x Fin.<? # 128 ⌋
      then ℤ.+ (sum + (toℕ x * (2 ^ i)))
      else (ℤ.+ (sum + ((toℕ x - 128) * (2 ^ i)))) ℤ.- ℤ.+ (2 ^ (i + 7))
    go (x ∷ x₁ ∷ xs) i sum = go (x₁ ∷ xs) (i + 8) (sum + toℕ x * (2 ^ i))

  private
    tc₁ : twosComplement ([ # 255 ]) ≡ ℤ.- (ℤ.+ 1)
    tc₁ = refl

    tc₂ : twosComplement (# 252 ∷ [ # 24 ]) ≡ ℤ.- (ℤ.+ 1000)
    tc₂ = refl

  -- Converts ASCII codes for '0'-'9' to the corresponding nat.
  asciiNum₁ : Dig → ℕ
  asciiNum₁ = (_- toℕ '0') ∘ toℕ

  asciiNum : List UInt8 → ℕ
  asciiNum xs = go (reverse xs)
    where
    go : List Dig → ℕ
    go [] = 0
    go (x ∷ xs) = asciiNum₁ x + 10 * go xs

  postulate
    asciiNum-injective : (xs₁ xs₂ : List UInt8) → All (InRange '0' '9') xs₁ → All (InRange '0' '9') xs₂
                         → xs₁ ≢ [] → xs₂ ≢ []
                         → asciiNum xs₁ ≡ asciiNum xs₂
                         → xs₁ ≡ xs₂

  showFixed : (w n : ℕ) → Vec UInt8 w
  showFixed zero n = Vec.[]
  showFixed w@(suc w') n =
    c₁'
    ∷ showFixed w'
        (toℕ $ _mod_ n (10 ^ w'){fromWitnessFalse (Nat.>⇒≢ (1≤10^n w'))})
    where
    c₁ : Fin 10
    c₁ = ((n div (10 ^ w')){fromWitnessFalse (>⇒≢ (1≤10^n w'))}) mod 10

    c₁' : UInt8
    c₁' = Fin.inject≤ (c₁ Fin.+ (#_ '0' {suc $ toℕ '0'}))
            (≤.begin (toℕ c₁ + suc (toℕ '0') ≤.≤⟨ +-monoˡ-≤ (suc (toℕ '0')) (Fin.toℕ≤n c₁) ⟩
                     10 + suc (toℕ '0') ≤.≤⟨ toWitness{Q = _ Nat.≤? _} tt ⟩
                     256 ≤.∎))
      where
      module ≤ = ≤-Reasoning


module Base128 where
  Byte = Binary 7
  Dig  = Fin (2 ^ 7)


UInt6 = Fin (2 ^ 6)

module Base64 where
  Byte = Binary 6
  Dig  = Fin (2 ^ 6)

  charset : List Char
  charset = String.toList "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

  ∈charsetUnique : ∀ {c} → (c∈₁ c∈₂ : c ∈ charset) → c∈₁ ≡ c∈₂
  ∈charsetUnique = ∈-unique (toWitness{Q = List.unique? _≟_ charset} tt)

  isByteRep : ∀ c → Dec (c ∈ charset)
  isByteRep c = Any.any (c ≟_) charset

  toDig : Char → Maybe Dig
  toDig c
    with isByteRep c
  ... | no  c∉charset = nothing
  ... | yes c∈charset = just (Any.index c∈charset)

  toByte : Char → Maybe Byte
  toByte c = do
    d ← toDig c
    return (toBinary d)

  isPad : ∀ c → Dec (c ≡ '=')
  isPad = _≟ '='

  data Pad : Set where
    pad2 : Vec Byte 2 → Pad
    pad1 : Vec Byte 3 → Pad

  toDigs : List Char → Maybe (List Dig)
  toDigs [] = just []
  toDigs (c ∷ []) =
    if ⌊ isPad c ⌋ then just []
    else Maybe.map [_] (toDig c)
  toDigs (c₀ ∷ c₁ ∷ []) =
    if ⌊ isPad c₀ ⌋ then just []
    else do
      d₀ ← toDig c₀
      d₁ ← toDig c₁
      return (d₀ ∷ [ d₁ ])
  toDigs (c₀ ∷ cs'@(c₁ ∷ c₂ ∷ cs)) = do
    d₀ ← toDig c₀
    ds ← toDigs cs'
    return (d₀ ∷ ds)

  record EncodedString (@0 es : List Char) : Set where
    constructor mkEncodedString
    field
      contents : List Char
      contents∈charset : All (λ x → x ∈ charset) contents
      padding : List Char
      @0 es≡ : es ≡ contents ++ padding

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

  pad64To256 : Base64.Pad → List Base256.Byte
  pad64To256 (Base64.pad2 (
      (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ [])
    ∷ (b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ [])
    ∷ []))
    = [ b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ b₂₁ ∷ b₂₂ ∷ [] ]
  pad64To256 (Base64.pad1 (
      (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ [])
    ∷ (b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ [])
    ∷ (b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ b₃₅ ∷ b₃₆ ∷ [])
    ∷ []))
    =   (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ b₂₁ ∷ b₂₂ ∷ [])
      ∷ (b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ [])
      ∷ []

module Digs where

  base64To256 : List Base64.Dig → Maybe (List Base256.Dig)
  base64To256 [] = just []
  base64To256 (x ∷ []) = nothing
    -- a single base64 digit is not enough to encode a base256 digi
  base64To256 (c₀ ∷ c₁ ∷ []) = do
    let bs = Bytes.pad64To256 (Base64.pad2 (toBinary c₀ ∷ toBinary c₁ ∷ []))
    return (map fromBinary bs)
  base64To256 (c₀ ∷ c₁ ∷ c₂ ∷ []) = do
    let bs = Bytes.pad64To256 (Base64.pad1 (toBinary c₀ ∷ toBinary c₁ ∷ toBinary c₂ ∷ []))
    return (map fromBinary bs)
  base64To256 (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ cs) = do
    let bs = Bytes.base64To256 (toBinary c₀ ∷ toBinary c₁ ∷ toBinary c₂ ∷ toBinary c₃ ∷ [])
    ds ← base64To256 cs
    return (map fromBinary (Vec.toList bs) ++ ds)

  -- base64To256 : ∀ {n} → Vec Base64.Dig (4 * n) → Vec Base256.Dig (3 * n)
  -- base64To256 {zero} cs = []
  -- base64To256 {suc n} cs
  --   with *-distribˡ-+ 4 1 n
  -- ...| pf
  --   with 4 * (1 + n)
  -- base64To256 {suc n} cs | refl | ._
  --   with *-distribˡ-+ 3 1 n
  -- ...| pf'
  --   with 3 * (1 + n)
  -- base64To256 {suc n} cs | refl | ._ | refl | ._ =
  --   Vec._++_ {m = 3}{3 * n}
  --     (Vec.map fromBinary (Bytes.base64To256 (Vec.take 4 (Vec.map toBinary cs))))
  --     (base64To256{n} (Vec.drop 4 cs))

module Decode where

  base64 : List Char → Maybe (List UInt8)
  base64 cs = do
    ds ← Base64.toDigs cs
    Digs.base64To256 ds

  -- private
  --   test₀ : String
  --   test₀ = String.fromList (map (Char.fromℕ ∘ toℕ) (from-just foo))
  --     where
  --     foo = base64 (String.toList "TWFueSBoYW5kcyBtYWtlIGxpZ2h0IHdvcmsu")
