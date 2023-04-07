{-# OPTIONS --inversion-max-depth=100 #-}

open import Aeres.Arith
open import Aeres.Prelude
open import Data.Fin.Properties as Fin
  renaming (≤-refl to Fin-≤-refl ; ≤-trans to Fin-≤-trans ; suc-injective to Fin-suc-injective)
  hiding   (_≟_)
open import Data.Nat.Induction
  hiding (Acc)
open import Data.Nat.Properties as Nat
  hiding (_≟_)
import      Data.Sign
import      Data.Vec.Properties as Vec

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

-- TODO: satisfy termination checker
{-# TERMINATING #-}
toBinary-injective : ∀ {n} → (i₁ i₂ : Fin (2 ^ n)) → toBinary{n} i₁ ≡ toBinary{n} i₂ → i₁ ≡ i₂
toBinary-injective{n} i₁ i₂ i≡ =
  help{n} i₁ i₂ self self (Lemmas.Vec-reverse-injective _ _ i≡)
  where
  open ≡-Reasoning
  module ≤ = ≤-Reasoning

  help : ∀ {n} (i₁ i₂ : Fin (2 ^ n))
         → (n₁ : Singleton (toℕ i₁)) (n₂ : Singleton (toℕ i₂))
         → ToBinary.help n (↑ n₁) ≡ ToBinary.help n (↑ n₂)
         → i₁ ≡ i₂
  help {zero} Fin.zero Fin.zero n₁ n₂ toB≡ = refl
  help {suc n} i₁ i₂ (singleton n₁ n₁≡) (singleton n₂ n₂≡) toB≡ =
    toℕ-injective
      (begin
        (toℕ i₁ ≡⟨ ‼ sym n₁≡ ⟩
        n₁ ≡⟨ sym (divmod2-*2 n₁) ⟩
        toℕ (mod2 n₁) + 2 * (div2 n₁) ≡⟨ cong (_+ (2 * (div2 n₁))) (cong toℕ (Vec.∷-injectiveˡ toB≡)) ⟩
        toℕ (mod2 n₂) + 2 * (div2 n₁) ≡⟨ cong (toℕ (mod2 n₂) +_) (cong (2 *_) i₁'≡) ⟩
        toℕ (mod2 n₂) + 2 * (toℕ i₁') ≡⟨ cong (toℕ (mod2 n₂) +_) (cong ((2 *_) ∘ toℕ) ih) ⟩
        toℕ (mod2 n₂) + 2 * (toℕ i₂') ≡⟨ cong (toℕ (mod2 n₂) +_) (cong (2 *_) (sym i₂'≡)) ⟩
        toℕ (mod2 n₂) + 2 * (div2 n₂) ≡⟨ divmod2-*2 n₂ ⟩
        n₂ ≡⟨ ‼ n₂≡ ⟩
        toℕ i₂ ∎))
    where
    i₁'< : div2 n₁ < 2 ^ n
    i₁'< = divmod2-mono-<' n₁ (2 ^ n) (subst₀ (_< (2 ^ (1 + n))) (sym n₁≡) (Fin.toℕ<n i₁))

    i₁' : Fin (2 ^ n)
    i₁' = Fin.fromℕ< i₁'<

    i₁'≡ : div2 n₁ ≡ toℕ i₁'
    i₁'≡ = sym (toℕ-fromℕ< i₁'<)

    i₂'< : div2 n₂ < 2 ^ n
    i₂'< = divmod2-mono-<' n₂ (2 ^ n) (subst₀ ((_< (2 ^ (1 + n)))) (sym n₂≡) (Fin.toℕ<n i₂))

    i₂' : Fin (2 ^ n)
    i₂' = Fin.fromℕ< i₂'<

    i₂'≡ : div2 n₂ ≡ toℕ i₂'
    i₂'≡ = sym (toℕ-fromℕ< i₂'<)

    ih = help{n} i₁' i₂' (singleton (div2 n₁) i₁'≡) (singleton (div2 n₂) i₂'≡) (Vec.∷-injectiveʳ toB≡)

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
  test₂ = refl


UInt8 = Fin (2 ^ 8)

module Base256 where
  Byte  = Binary 8
  Dig   = Fin (2 ^ 8)

  fromℕ : (m : ℕ) {_ : True (suc (toℕ m) Nat.≤? 256)} → UInt8
  fromℕ m {m<} = #_ m {m<n = m<}

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
  asciiNum₁ : UInt8 → ℕ
  asciiNum₁ = (_- toℕ '0') ∘ toℕ

  asciiNum₁-injective
    : ∀ b₁ b₂ → All (((toℕ '0') ≤_) ∘ toℕ) (b₁ ∷ [ b₂ ])
      → asciiNum₁ b₁ ≡ asciiNum₁ b₂
      → b₁ ≡ b₂
  asciiNum₁-injective b₁ b₂ (p₁ ∷ p₂ ∷ []) ascii≡ =
    toℕ-injective (∸-cancelʳ-≡ p₁ p₂ ascii≡)
    where
    open ≡-Reasoning

  asciiNum-help : List UInt8 → ℕ
  asciiNum-help [] = 0
  asciiNum-help (x ∷ xs) = asciiNum₁ x + 10 * asciiNum-help xs

  asciiNum : List UInt8 → ℕ
  asciiNum xs = asciiNum-help (reverse xs)

  asciiNum-injective
    : (xs₁ xs₂ : List UInt8) → All (InRange '0' '9') xs₁ → All (InRange '0' '9') xs₂
      → length xs₁ ≡ length xs₂
      → asciiNum xs₁ ≡ asciiNum xs₂
      → xs₁ ≡ xs₂
  asciiNum-injective xs₁ xs₂ inr₁ inr₂ len≡ ascii≡ =
    reverse-injective
      (help _ _
        (Lemmas.All-reverse xs₁ inr₁)
        (Lemmas.All-reverse xs₂ inr₂)
        (length (reverse xs₁) ≡⟨ length-reverse xs₁ ⟩
        length xs₁ ≡⟨ len≡ ⟩
        length xs₂ ≡⟨ sym (length-reverse xs₂) ⟩
        length (reverse xs₂) ∎)
        ascii≡)
    where
    open ≡-Reasoning

    help : (xs₁ xs₂ : List UInt8) → All (InRange '0' '9') xs₁ → All (InRange '0' '9') xs₂
      → length xs₁ ≡ length xs₂
      → asciiNum-help xs₁ ≡ asciiNum-help xs₂
      → xs₁ ≡ xs₂
    help [] [] inr₁ inr₂ len≡ ascii≡ = refl
    help (x₁ ∷ xs₁) (x₂ ∷ xs₂) (p₁ ∷ inr₁) (p₂ ∷ inr₂) len≡ ascii≡ =
      cong₂ _∷_ x₁≡x₂ (help xs₁ xs₂ inr₁ inr₂ (suc-injective len≡) xs₁≡xs₂an)
      where
      open import Data.Nat.DivMod
      module ≤ = ≤-Reasoning

      x₁an : asciiNum₁ x₁ ≤ 9
      x₁an = ≤.begin
        (asciiNum₁ x₁ ≤.≡⟨ refl ⟩
        toℕ x₁ - toℕ '0' ≤.≤⟨ ∸-monoˡ-≤ 48 (proj₂ p₁) ⟩
        9 ≤.∎)

      x₂an : asciiNum₁ x₂ ≤ 9
      x₂an = ≤.begin
        (asciiNum₁ x₂ ≤.≡⟨ refl ⟩
        toℕ x₂ - toℕ '0' ≤.≤⟨ ∸-monoˡ-≤ 48 (proj₂ p₂) ⟩
        9 ≤.∎)

      xan≡ : asciiNum₁ x₁ ≡ asciiNum₁ x₂
      xan≡ = begin
        asciiNum₁ x₁      ≡⟨ sym (m≤n⇒m%n≡m x₁an) ⟩
        asciiNum₁ x₁ % 10 ≡⟨ sym ([m+kn]%n≡m%n (asciiNum₁ x₁) (asciiNum-help xs₁) 9) ⟩
        (asciiNum₁ x₁ + asciiNum-help xs₁ * 10) % 10
          ≡⟨ cong (_% 10)
               (begin (asciiNum₁ x₁ + asciiNum-help xs₁ * 10 ≡⟨ cong (asciiNum₁ x₁ +_) (*-comm (asciiNum-help xs₁) 10) ⟩
                      asciiNum₁ x₁ + 10 * asciiNum-help xs₁ ≡⟨ ascii≡ ⟩
                      asciiNum₁ x₂ + 10 * asciiNum-help xs₂ ≡⟨ cong (asciiNum₁ x₂ +_) (*-comm 10 (asciiNum-help xs₂)) ⟩
                      asciiNum₁ x₂ + asciiNum-help xs₂ * 10 ∎)) ⟩
        (asciiNum₁ x₂ + asciiNum-help xs₂ * 10) % 10 ≡⟨ [m+kn]%n≡m%n (asciiNum₁ x₂) (asciiNum-help xs₂) 9 ⟩
        asciiNum₁ x₂ % 10 ≡⟨ m≤n⇒m%n≡m x₂an ⟩
        asciiNum₁ x₂ ∎

      x₁≡x₂ : x₁ ≡ x₂
      x₁≡x₂ = asciiNum₁-injective x₁ x₂ (proj₁ p₁ ∷ proj₁ p₂ ∷ []) xan≡

      xs₁≡xs₂an : asciiNum-help xs₁ ≡ asciiNum-help xs₂
      xs₁≡xs₂an =
        *-cancelˡ-≡ 9
          (+-cancelˡ-≡ (asciiNum₁ x₁)
            (begin
              asciiNum₁ x₁ + 10 * asciiNum-help xs₁ ≡⟨ ascii≡ ⟩
              asciiNum₁ x₂ + 10 * asciiNum-help xs₂ ≡⟨ cong (_+ 10 * asciiNum-help xs₂) (sym xan≡) ⟩
              asciiNum₁ x₁ + 10 * asciiNum-help xs₂ ∎))

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

module UInt8 = Base256

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
