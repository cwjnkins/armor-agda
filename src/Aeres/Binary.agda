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

  unsigned : List UInt8 → ℕ
  unsigned [] = 0
  unsigned (x ∷ bs) = toℕ x * (256 ^ length bs) + unsigned bs

  unsigned< : ∀ bs → unsigned bs < 256 ^ length bs
  unsigned< [] = s≤s z≤n
  unsigned< (x ∷ bs) = ≤.begin
    suc (toℕ x * (256 ^ length bs)) + unsigned bs ≤.≡⟨ sym (+-suc _ (unsigned bs)) ⟩
    (toℕ x * (256 ^ length bs)) + suc (unsigned bs)
      ≤.≤⟨ +-monoʳ-≤ ((toℕ x * (256 ^ length bs))) ih ⟩
    (toℕ x * (256 ^ length bs)) + 256 ^ length bs
      ≤.≡⟨ cong (_+ (256 ^ length bs))
             (Lemmas.m*n≡[suc-m]*n∸n (toℕ x) (256 ^ length bs)
               (n≢0⇒n>0 (λ eq → contradiction (m^n≡0⇒m≡0 256 (length bs) eq) λ ()))) ⟩
    suc (toℕ x) * (256 ^ length bs) - (256 ^ length bs) + 256 ^ length bs
      ≤.≤⟨ +-monoˡ-≤ (256 ^ length bs){x = suc (toℕ x) * (256 ^ length bs) - (256 ^ length bs)}
             (∸-monoˡ-≤ {m = suc (toℕ x) * (256 ^ length bs)} (256 ^ length bs)
                (*-monoˡ-≤ (256 ^ length bs) {x = suc (toℕ x)} (Fin.toℕ<n x))) ⟩ 
    (256 ^ (1 + length bs)) - (256 ^ length bs) + 256 ^ length bs
      ≤.≡⟨ m∸n+n≡m
             ((256 ^ length bs) ≤ 256 * (256 ^ length bs)
             ∋ ≤.begin
               256 ^ length bs ≤.≡⟨ sym (*-identityˡ _) ⟩
               1 * (256 ^ length bs) ≤.≤⟨ *-monoˡ-≤ (256 ^ length bs) (s≤s{n = 255} z≤n) ⟩
               256 * 256 ^ length bs ≤.∎) ⟩
    256 ^ (1 + length bs) ≤.∎
    where
    module ≤ = ≤-Reasoning

    ih : unsigned bs < 256 ^ length bs
    ih = unsigned< bs

  unsigned-head< : ∀ b bs {n} → toℕ b < n → unsigned (b ∷ bs) < n * 256 ^ length bs
  unsigned-head< b bs {n} b≤n = ≤.begin
    suc (unsigned (b ∷ bs)) ≤.≡⟨⟩
    suc (toℕ b * 256 ^ length bs + unsigned bs) ≤.≡⟨ sym (+-suc _ _) ⟩
    toℕ b * 256 ^ length bs + suc (unsigned bs) ≤.≤⟨ +-monoʳ-≤ (toℕ b * 256 ^ length bs) (unsigned< bs) ⟩
    toℕ b * 256 ^ length bs + 256 ^ length bs ≤.≡⟨ +-comm _ (256 ^ length bs) ⟩
    256 ^ length bs + toℕ b * 256 ^ length bs ≤.≡⟨⟩
    (1 + toℕ b) * 256 ^ length bs ≤.≤⟨ *-monoˡ-≤ _ b≤n ⟩
    n * 256 ^ length bs ≤.∎
    where
    module ≤ = ≤-Reasoning

  unsigned-leading-0
    : ∀ {bs₁ bs₂} → (ne : 0 < length bs₂) (l : length bs₁ < length bs₂) → unsigned bs₁ ≡ unsigned bs₂
      → toℕ (headSafe bs₂ ne) ≡ 0
  unsigned-leading-0 {bs₁} {Fin.zero ∷ bs₂} ne l eq = refl
  unsigned-leading-0 {bs₁} {Fin.suc x ∷ bs₂} (s≤s z≤n) (s≤s l) eq =
    contradiction eq (Nat.<⇒≢ (≤.begin
      suc (unsigned bs₁) ≤.≤⟨ unsigned< bs₁ ⟩
      256 ^ length bs₁ ≤.≤⟨ Lemmas.^-monoʳ-≤ 256 (s≤s{n = 255} z≤n) l ⟩
      256 ^ length bs₂ ≤.≤⟨ m≤m+n (256 ^ length bs₂) _ ⟩
      256 ^ length bs₂ + toℕ x * (256 ^ length bs₂)
        ≤.≤⟨ m≤m+n _ (unsigned bs₂) ⟩
      256 ^ length bs₂ + toℕ x * (256 ^ length bs₂) + unsigned bs₂ ≤.∎))
    where
    module ≤ = ≤-Reasoning

  unsigned-injective : ∀ bs₁ bs₂ → length bs₁ ≡ length bs₂ → unsigned bs₁ ≡ unsigned bs₂ → bs₁ ≡ bs₂
  unsigned-injective [] [] len≡ eq = refl
  unsigned-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ eq =
    cong₂ _∷_ x₁≡x₂ bs₁≡bs₂
    where
    module ≤ = ≤-Reasoning
    open ≡-Reasoning

    len≡' = suc-injective len≡

    lem₀ : ∀ (x₁ x₂ : UInt8) bs₁ bs₂ → length bs₁ ≡ length bs₂
           → toℕ x₁ < toℕ x₂
           → toℕ x₁ * (256 ^ length bs₁) + unsigned bs₁ ≡ toℕ x₂ * (256 ^ length bs₁) + unsigned bs₂
           → ⊥
    lem₀ x₁ x₂ bs₁ bs₂ len≡ x₁<x₂ eq
      with Lemmas.m≤n⇒∃[o]o+m≡n x₁<x₂
    ... | (o , x₁+o≡x₂) rewrite sym x₁+o≡x₂ =
      contradiction eq (Nat.<⇒≢ (≤.begin
        1 + (toℕ x₁ * (256 ^ length bs₁)) + unsigned bs₁ ≤.≡⟨ sym (+-suc _ (unsigned bs₁)) ⟩
        toℕ x₁ * (256 ^ length bs₁) + suc (unsigned bs₁) ≤.≤⟨ +-monoʳ-≤ (toℕ x₁ * 256 ^ length bs₁) (unsigned< bs₁) ⟩
        toℕ x₁ * (256 ^ length bs₁) + 256 ^ (length bs₁) ≤.≡⟨ +-comm (toℕ x₁ * 256 ^ length bs₁) (256 ^ length bs₁) ⟩
        (1 + toℕ x₁) * 256 ^ length bs₁ ≤.≤⟨ *-monoˡ-≤ (256 ^ length bs₁) (m≤n+m (1 + toℕ x₁) o) ⟩
        (o + suc (toℕ x₁)) * 256 ^ length bs₁ ≤.≤⟨ m≤m+n _ (unsigned bs₂) ⟩
        (o + suc (toℕ x₁)) * 256 ^ length bs₁ + unsigned bs₂ ≤.∎))

    x₁≡x₂ : x₁ ≡ x₂
    x₁≡x₂
      with Nat.<-cmp (toℕ x₁) (toℕ x₂)
    ... | tri< x₁<x₂ _ _ =
      ⊥-elim (lem₀ x₁ x₂ bs₁ bs₂ len≡' x₁<x₂
        (subst (λ n → toℕ x₁ * (256 ^ length bs₁) + unsigned bs₁ ≡ toℕ x₂ * (256 ^ n) + unsigned bs₂)
           (sym len≡') eq))
    ... | tri> _ _ x₂<x₁ =
     ⊥-elim (lem₀ x₂ x₁ bs₂ bs₁ (sym len≡') x₂<x₁
        (subst (λ n → toℕ x₂ * (256 ^ length bs₂) + unsigned bs₂ ≡ toℕ x₁ * (256 ^ n) + unsigned bs₁)
           len≡' (sym eq)))
    ... | tri≈ _ x₁≡x₂ _ = Fin.toℕ-injective x₁≡x₂

    bs₁≡bs₂ : bs₁ ≡ bs₂
    bs₁≡bs₂ = unsigned-injective bs₁ bs₂ (suc-injective len≡)
           (+-cancelˡ-≡ (toℕ x₁ * 256 ^ length bs₁) (begin
             toℕ x₁ * 256 ^ length bs₁ + unsigned bs₁ ≡⟨ eq ⟩
             toℕ x₂ * 256 ^ length bs₂ + unsigned bs₂
               ≡⟨ cong (_+ unsigned bs₂)
                    (cong₂ _*_
                      (cong Fin.toℕ (sym x₁≡x₂))
                      (cong (256 ^_) (sym $ suc-injective len≡))) ⟩
             toℕ x₁ * 256 ^ length bs₁ + unsigned bs₂ ∎))

  twosComplement- : UInt8 → List UInt8 → ℤ
  twosComplement- b bs =
    Sign.- ℤ.◃ (128 * 256 ^ length bs - unsigned (Fin.fromℕ<{m = toℕ b - 128}{n = 256} (≤-trans (s≤s (m∸n≤m (toℕ b) 128)) (Fin.toℕ<n b)) ∷ bs))

  twosComplement : List UInt8 → ℤ
  twosComplement [] = ℤ.+ 0
  twosComplement xs@(b₁ ∷ bs) with toℕ b₁ Nat.≤? 127
  ... | no ¬p = twosComplement- b₁ bs
  ... | yes p = ℤ.+ unsigned xs

  TwosComplementMinRep : UInt8 → List UInt8 → Set
  TwosComplementMinRep bₕ [] = ⊤
  TwosComplementMinRep bₕ (b ∷ bₜ) =
    (toℕ bₕ ≡ 0 → toℕ b ≥ 128) × (toℕ bₕ ≡ 255 → toℕ b ≤ 127)

  twosComplementMinRep? : ∀ bₕ bₜ → Dec (TwosComplementMinRep bₕ bₜ)
  twosComplementMinRep? bₕ [] = yes tt
  twosComplementMinRep? bₕ (b ∷ bₜ) =
          (toℕ bₕ ≟ 0 →-dec toℕ b ≥? 128)
    ×-dec (toℕ bₕ ≟ 255 →-dec toℕ b Nat.≤? 127)
    where
    open import Relation.Nullary.Implication

  twosComplement<0 : ∀ b bs → ∃ λ n → twosComplement- b bs ≡ ℤ.-[1+ n ]
  twosComplement<0 b bs = _ , cong (λ x → Sign.- ℤ.◃ x) (begin
      128 * 256 ^ length bs - (toℕ b' * 256 ^ length bs + unsigned bs)
        ≡⟨ sym (∸-+-assoc (128 * 256 ^ length bs) (toℕ b' * 256 ^ length bs) (unsigned bs)) ⟩
      128 * 256 ^ length bs - (toℕ b' * 256 ^ length bs) - unsigned bs
        ≡⟨ cong (_- (unsigned bs)) (sym (Nat.*-distribʳ-∸ (256 ^ length bs) 128 (toℕ b'))) ⟩
      (128 - toℕ b') * 256 ^ length bs - unsigned bs
        ≡⟨ cong (λ x → x * (256 ^ length bs) ∸ unsigned bs) (proj₂ diff) ⟩
      suc (proj₁ diff) * 256 ^ length bs - unsigned bs
        ≡⟨⟩
      256 ^ length bs + (proj₁ diff * 256 ^ length bs) - unsigned bs
        ≡⟨ cong (_∸ unsigned bs) (+-comm (256 ^ length bs) (proj₁ diff * 256 ^ length bs)) ⟩
      (proj₁ diff * 256 ^ length bs) + 256 ^ length bs - unsigned bs
        ≡⟨ +-∸-assoc (proj₁ diff * (256 ^ length bs)){n = 256 ^ length bs}{o = unsigned bs} (<⇒≤ (unsigned< bs)) ⟩
      (proj₁ diff * 256 ^ length bs) + (256 ^ length bs - unsigned bs)
        ≡⟨ cong (proj₁ diff * (256 ^ length bs) +_) (proj₂ diff') ⟩
      (proj₁ diff * 256 ^ length bs) + suc (proj₁ diff')
        ≡⟨ +-suc _ (proj₁ diff') ⟩
      suc (proj₁ diff * 256 ^ length bs) + proj₁ diff' ∎)
    where
    open ≡-Reasoning
    module ≤ = ≤-Reasoning

    b-128<256 : toℕ b - 128 < 256
    b-128<256 = ≤-trans (s≤s (m∸n≤m (toℕ b) 128)) (Fin.toℕ<n b)

    b' : UInt8
    b' = Fin.fromℕ< b-128<256

    b'≤127 : toℕ b' ≤ 127
    b'≤127 = ≤.begin
      toℕ b' ≤.≡⟨⟩
      toℕ (Fin.fromℕ< b-128<256) ≤.≡⟨ toℕ-fromℕ< b-128<256 ⟩
      toℕ b - 128 ≤.≤⟨ ∸-monoˡ-≤ {m = toℕ b} {n = 255} 128 (+-cancelˡ-≤ 1 (Fin.toℕ<n b)) ⟩
      127 ≤.∎

    diff : ∃ λ n → 128 - toℕ b' ≡ suc n
    diff with Lemmas.m≤n⇒∃[o]o+m≡n b'≤127
    ... | (o , o+b≡127) = o , (begin
      128 - toℕ b' ≡⟨ cong (λ x → suc x - toℕ b') (sym o+b≡127) ⟩
      suc o + toℕ b' - toℕ b' ≡⟨ m+n∸n≡m (suc o) (toℕ b') ⟩
      suc o ∎)

    diff' : ∃ λ n → 256 ^ length bs - unsigned bs ≡ suc n
    diff' with Lemmas.m≤n⇒∃[o]o+m≡n (unsigned< bs)
    ... | (o , o+[1+u]≡) = o , (begin
      256 ^ length bs - unsigned bs ≡⟨ cong (_- (unsigned bs)) (sym o+[1+u]≡) ⟩
      o + suc (unsigned bs) - unsigned bs ≡⟨ cong (_∸ unsigned bs) (+-suc o (unsigned bs)) ⟩
      suc o + unsigned bs - unsigned bs ≡⟨ m+n∸n≡m (suc o) (unsigned bs) ⟩
      suc o ∎)

  ¬twosComplementMinRep : ∀ bₕ₁ bₜ₁ bₕ₂ bₜ₂ → length bₜ₁ < length bₜ₂ → twosComplement (bₕ₁ ∷ bₜ₁) ≡ twosComplement (bₕ₂ ∷ bₜ₂)
                          → ¬ TwosComplementMinRep bₕ₂ bₜ₂
  ¬twosComplementMinRep bₕ₁ bₜ₁ bₕ₂ (b ∷ bₜ₂) (s≤s bs₁<bs₂) eq (mr₂₁ , mr₂₂)
    with toℕ bₕ₁ Nat.≤? 127
  ... | yes bₕ₁≤127
    with toℕ bₕ₂ Nat.≤? 127
  ... | no ¬bₕ₂≤127 =
    contradiction {P = ℤ.+ _ ≡ ℤ.-[1+ _ ]} (trans eq (proj₂ (twosComplement<0 bₕ₂ (b ∷ bₜ₂)))) (λ ())
  ... | yes bₕ₂≤127 =
    contradiction lem₀ (Nat.<⇒≢ (≤.begin
      suc (toℕ bₕ₁ * 256 ^ length bₜ₁) + unsigned bₜ₁
        ≤.≡⟨ sym (+-suc _ (unsigned bₜ₁)) ⟩
      toℕ bₕ₁ * 256 ^ length bₜ₁ + suc (unsigned bₜ₁)
        ≤.≤⟨ +-monoʳ-≤ _ (unsigned< bₜ₁) ⟩
      toℕ bₕ₁ * 256 ^ length bₜ₁ + 256 ^ length bₜ₁
        ≤.≡⟨ +-comm _ (256 ^ length bₜ₁) ⟩
      suc (toℕ bₕ₁) * 256 ^ length bₜ₁
        ≤.≤⟨ Nat.*-monoʳ-≤ (suc (toℕ bₕ₁)) (Lemmas.^-monoʳ-≤ 256 (s≤s z≤n) bs₁<bs₂) ⟩
      suc (toℕ bₕ₁) * 256 ^ length bₜ₂
        ≤.≤⟨ (case singleton (toℕ bₕ₂) refl ret (const _) of λ where
          (singleton (suc n) n≡) → ≤.begin
            suc (toℕ bₕ₁) * 256 ^ length bₜ₂
              ≤.≤⟨ *-monoˡ-≤ (256 ^ length bₜ₂) (Fin.toℕ<n bₕ₁) ⟩
            256 ^ (1 + length bₜ₂)
              ≤.≤⟨ Nat.m≤n*m (256 ^ (1 + length bₜ₂)) {toℕ bₕ₂} (n≢0⇒n>0 (λ eq → case trans (‼ n≡) eq of λ ())) ⟩
            toℕ bₕ₂ * 256 ^ (1 + length bₜ₂)
              ≤.≤⟨ m≤m+n _ _ ⟩
            toℕ bₕ₂ * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)
              ≤.∎
          (singleton zero    n≡) → ≤.begin
            suc (toℕ bₕ₁) * 256 ^ length bₜ₂
              ≤.≤⟨ *-monoˡ-≤ (256 ^ length bₜ₂) (≤-trans (s≤s bₕ₁≤127) (mr₂₁ (‼ sym n≡))) ⟩
            toℕ b * 256 ^ length bₜ₂
              ≤.≤⟨ m≤m+n _ (unsigned bₜ₂) ⟩
            toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂
              ≤.≡⟨ cong (λ x → x * 256 ^ (1 + length bₜ₂) + (toℕ b * (256 ^ length bₜ₂) + unsigned bₜ₂))
                     (‼ n≡) ⟩
            toℕ bₕ₂ * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)
              ≤.∎)⟩
      toℕ bₕ₂ * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂) ≤.∎))
    where
    module ≤ = ≤-Reasoning
    import Data.Integer.Properties as ℤ

    lem₀ : toℕ bₕ₁ * (256 ^ length bₜ₁) + unsigned bₜ₁ ≡ toℕ bₕ₂ * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)
    lem₀ = ℤ.+-injective eq
  ¬twosComplementMinRep bₕ₁ bₜ₁ bₕ₂ (b ∷ bₜ₂) (s≤s bs₁<bs₂) eq (mr₂₁ , mr₂₂) | no ¬bₕ₁≤127
    with toℕ bₕ₂ Nat.≤? 127
  ... | yes bₕ₂≤127 =
    contradiction {P = ℤ.+ _ ≡ ℤ.-[1+ _ ]} (trans (sym eq) (proj₂ (twosComplement<0 bₕ₁ bₜ₁))) (λ ())
  ... | no ¬bₕ₂≤127 =
    contradiction lem₀ (Nat.<⇒≢ (≤.begin
      suc (128 * 256 ^ length bₜ₁ - unsigned (bₕ₁' ∷ bₜ₁))
        ≤.≤⟨ +-monoʳ-≤ 1 (≤.begin
               128 * 256 ^ length bₜ₁ - unsigned (bₕ₁' ∷ bₜ₁) ≤.≤⟨ m∸n≤m _ (unsigned (bₕ₁' ∷ bₜ₁)) ⟩
               128 * 256 ^ length bₜ₁ ≤.≤⟨ *-monoʳ-≤ 128 (Lemmas.^-monoʳ-≤ 256 (s≤s z≤n) bs₁<bs₂) ⟩
               128 * 256 ^ length bₜ₂ ≤.≡⟨ *-distribʳ-∸ (256 ^ length bₜ₂) 256 128 ⟩
               256 ^ (1 + length bₜ₂) - 128 * 256 ^ length bₜ₂
                 ≤.≡⟨ cong (_∸ 128 * (256 ^ length bₜ₂)) (begin
                   256 ^ (1 + length bₜ₂) ≡⟨ sym (*-identityˡ (256 ^ (1 + length bₜ₂))) ⟩
                   1 * 256 ^ (1 + length bₜ₂) ≡⟨⟩
                   (128 - 127) * 256 ^ (1 + length bₜ₂) ≡⟨ *-distribʳ-∸ (256 ^ (1 + length bₜ₂) ) 128 127 ⟩
                   128 * 256 ^ (1 + length bₜ₂) - 127 * 256 ^ (1 + length bₜ₂) ∎) ⟩
               (128 * 256 ^ (1 + length bₜ₂) - 127 * 256 ^ (1 + length bₜ₂)) - 128 * 256 ^ length bₜ₂
                 ≤.≡⟨ ∸-+-assoc (128 * 256 ^ (1 + length bₜ₂)) (127 * 256 ^ (1 + length bₜ₂)) (128 * 256 ^ length bₜ₂) ⟩
               128 * 256 ^ (1 + length bₜ₂) - (127 * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂) ≤.∎) ⟩
      suc (128 * 256 ^ (1 + length bₜ₂) - (127 * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂))
        ≤.≤⟨ ∸-monoʳ-<
               {128 * 256 ^ (1 + length bₜ₂)}
               {(127 * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂)}
               {toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)}
               (case toℕ bₕ₂ ≟ 255 ret (const _) of λ where
                 (yes bₕ₂≡255) → lem₂ bₕ₂≡255
                 (no  bₕ₂≢255) → lem₁ (+-cancelˡ-≤ 1 (Nat.≤∧≢⇒< (+-cancelˡ-≤ 1 (Fin.toℕ<n bₕ₂)) bₕ₂≢255)))
               (≤.begin
                 127 * 256 ^ (1 + length bₜ₂) + 128 * (256 ^ length bₜ₂)
                   ≤.≤⟨ +-monoʳ-≤ (127 * 256 ^ (1 + length bₜ₂)) (*-monoˡ-≤ (256 ^ length bₜ₂) (toWitness{Q = 128 Nat.≤? 256} tt)) ⟩
                 127 * 256 ^ (1 + length bₜ₂) + 256 ^ (1 + length bₜ₂)
                   ≤.≡⟨ +-comm (127 * 256 ^ (1 + length bₜ₂)) (256 ^ (1 + length bₜ₂)) ⟩
                 128 * 256 ^ (1 + length bₜ₂) ≤.∎) ⟩
      128 * 256 ^ (1 + length bₜ₂) - (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)) ≤.∎))
    where
    open ≡-Reasoning
    module ≤ = ≤-Reasoning
    bₕ₁∸128<256 = ≤-trans (s≤s (m∸n≤m (toℕ bₕ₁) 128)) (Fin.toℕ<n bₕ₁)
    bₕ₂∸128<256 = ≤-trans (s≤s (m∸n≤m (toℕ bₕ₂) 128)) (Fin.toℕ<n bₕ₂)

    bₕ₁' = Fin.fromℕ<{m = toℕ bₕ₁ - 128}{n = 256} bₕ₁∸128<256
    bₕ₂' = Fin.fromℕ<{m = toℕ bₕ₂ - 128}{n = 256} bₕ₂∸128<256

    bₕ₂'≤127 : toℕ bₕ₂' ≤ 127
    bₕ₂'≤127 = ≤.begin
      toℕ bₕ₂' ≤.≡⟨⟩
      toℕ (Fin.fromℕ<{m = toℕ bₕ₂ - 128}{n = 256} bₕ₂∸128<256) ≤.≡⟨ Fin.toℕ-fromℕ< bₕ₂∸128<256 ⟩
      toℕ bₕ₂ - 128 ≤.≤⟨ ∸-monoˡ-≤ 128 (+-cancelˡ-≤ 1 (Fin.toℕ<n bₕ₂)) ⟩
      127 ≤.∎

    lem₀ :   128 * 256 ^ length bₜ₁ - unsigned (bₕ₁' ∷ bₜ₁)
           ≡ 128 * 256 ^ (1 + length bₜ₂) - (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂))
    lem₀ = Lemmas.neg◃-injective eq

    lem₁ : toℕ bₕ₂ ≤ 254 →   toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + unsigned (b ∷ bₜ₂)
                           < 127      * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂
    lem₁ bₕ₂≤254 = ≤.begin
      suc (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + unsigned (b ∷ bₜ₂))
        ≤.≡⟨ sym (+-suc (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂)) _) ⟩
      toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + suc (unsigned (b ∷ bₜ₂))
        ≤.≤⟨ +-monoʳ-≤ (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂)) (unsigned< (b ∷ bₜ₂)) ⟩
      toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + 256 ^ (1 + length bₜ₂)
        ≤.≤⟨ +-monoˡ-≤ (256 ^ (1 + length bₜ₂)) (*-monoˡ-≤ (256 ^ (1 + length bₜ₂))
               (≤.begin
                 toℕ (Fin.fromℕ<{m = toℕ bₕ₂ - 128}{n = 256} bₕ₂∸128<256) ≤.≡⟨ Fin.toℕ-fromℕ< bₕ₂∸128<256 ⟩
                 toℕ bₕ₂ - 128 ≤.≤⟨ ∸-monoˡ-≤ 128 bₕ₂≤254 ⟩
                 126 ≤.∎)) ⟩
      126 * 256 ^ (1 + length bₜ₂) + 256 ^ (1 + length bₜ₂) ≤.≡⟨ +-comm (126 * 256 ^ (1 + length bₜ₂)) _ ⟩
      127 * 256 ^ (1 + length bₜ₂) ≤.≤⟨ m≤m+n (127 * 256 ^ (1 + length bₜ₂)) _ ⟩
      127 * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂ ≤.∎

    lem₂ : toℕ bₕ₂ ≡ 255 →    toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + unsigned (b ∷ bₜ₂)
                           < 127      * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂
    lem₂ bₕ₂≡255 = ≤.begin
      suc (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + unsigned (b ∷ bₜ₂)) ≤.≡⟨ sym (+-suc (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂)) _) ⟩
      toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + suc (unsigned (b ∷ bₜ₂)) ≤.≡⟨⟩
      toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + suc (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)
        ≤.≡⟨ cong ((toℕ bₕ₂' * 256 ^ (1 + length bₜ₂)) +_) (sym (+-suc _ (unsigned bₜ₂))) ⟩
      toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + suc (unsigned bₜ₂))
        ≤.≤⟨ +-monoʳ-≤ (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂))
               (+-mono-≤ (*-monoˡ-≤ (256 ^ length bₜ₂) (mr₂₂ bₕ₂≡255)) (unsigned< bₜ₂)) ⟩
      toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + (127 * 256 ^ length bₜ₂ + 256 ^ length bₜ₂)
        ≤.≤⟨ +-monoˡ-≤ ((127 * 256 ^ length bₜ₂ + 256 ^ length bₜ₂))
               (*-monoˡ-≤ (256 ^ (1 + length bₜ₂)) bₕ₂'≤127) ⟩
      127 * 256 ^ (1 + length bₜ₂) + (127 * 256 ^ length bₜ₂ + 256 ^ length bₜ₂)
        ≤.≡⟨ cong (127 * (256 ^ (1 + length bₜ₂)) +_) (+-comm (127 * 256 ^ length bₜ₂) _) ⟩
      127 * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂ ≤.∎

    {- 128 * 256 ^ length bₜ₁ - unsigned (bₕ₁' ∷ bₜ₁) ≤
    -- 128 * 256 ^ length bₜ₁ ≤
    -- 128 * 256 ^ length bₜ₂ ≡
    -- 256 ^ (1 + length bₜ₂) - 128 * length bₜ₂
    -}

  twosComplement-injective : (bs₁ bs₂ : List UInt8) → length bs₁ ≡ length bs₂ → twosComplement bs₁ ≡ twosComplement bs₂ → bs₁ ≡ bs₂
  twosComplement-injective [] [] len≡ twos≡ = refl
  twosComplement-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ twos≡
    with toℕ x₁ Nat.≤? 127 | toℕ x₂ Nat.≤? 127
  twosComplement-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ twos≡ | no ¬x₁≤127 | no ¬x₂≤127 =
    cong₂ _∷_ lem₄ (∷-injectiveʳ lem₃)
    where
    open ≡-Reasoning
    module ≤ = ≤-Reasoning

    x₁∸128<256 = ≤-trans (s≤s (m∸n≤m (toℕ x₁) 128)) (Fin.toℕ<n x₁)
    x₂∸128<256 = ≤-trans (s≤s (m∸n≤m (toℕ x₂) 128)) (Fin.toℕ<n x₂)

    x₁' = Fin.fromℕ<{m = toℕ x₁ - 128}{n = 256} x₁∸128<256
    x₂' = Fin.fromℕ<{m = toℕ x₂ - 128}{n = 256} x₂∸128<256

    x₁'≤127 : toℕ x₁' ≤ 127
    x₁'≤127 = ≤.begin
      toℕ x₁' ≤.≡⟨⟩
      toℕ (Fin.fromℕ<{m = toℕ x₁ - 128}{n = 256} x₁∸128<256) ≤.≡⟨ Fin.toℕ-fromℕ< x₁∸128<256 ⟩
      toℕ x₁ - 128 ≤.≤⟨ ∸-monoˡ-≤ 128 (+-cancelˡ-≤ 1 (Fin.toℕ<n x₁)) ⟩
      127 ≤.∎

    x₂'≤127 : toℕ x₂' ≤ 127
    x₂'≤127 = ≤.begin
      toℕ x₂' ≤.≡⟨⟩
      toℕ (Fin.fromℕ<{m = toℕ x₂ - 128}{n = 256} x₂∸128<256) ≤.≡⟨ Fin.toℕ-fromℕ< x₂∸128<256 ⟩
      toℕ x₂ - 128 ≤.≤⟨ ∸-monoˡ-≤ 128 (+-cancelˡ-≤ 1 (Fin.toℕ<n x₂)) ⟩
      127 ≤.∎

    lem₀ = Lemmas.neg◃-injective twos≡

    lem₁ :   128 * 256 ^ length bs₁ - unsigned (x₁' ∷ bs₁)
           ≡ 128 * 256 ^ length bs₁ - unsigned (x₂' ∷ bs₂)
    lem₁ = subst₀ (λ x → 128 * 256 ^ length bs₁ - unsigned (x₁' ∷ bs₁) ≡ 128 * 256 ^ x - unsigned (x₂' ∷ bs₂)){x = length bs₂}{y = length bs₁} (sym (suc-injective len≡)) lem₀

    lem₂ = ∸-cancelˡ-≡{m = 128 * 256 ^ length bs₁}{n = unsigned (x₁' ∷ bs₁)}{o = unsigned (x₂' ∷ bs₂)}
             (<⇒≤ (unsigned-head< x₁' bs₁{128} (s≤s x₁'≤127)))
             (subst₀ (λ x → unsigned (x₂' ∷ bs₂) ≤ 128 * (256 ^ x)) (sym $ suc-injective len≡)
               (<⇒≤ (unsigned-head< x₂' bs₂{128} (s≤s x₂'≤127))))
             lem₁

    lem₃ = unsigned-injective (x₁' ∷ bs₁) (x₂' ∷ bs₂) len≡ lem₂

    lem₄ : x₁ ≡ x₂
    lem₄ =
      toℕ-injective
        (∸-cancelʳ-≡ {o = 128} (≰⇒> ¬x₁≤127) (≰⇒> ¬x₂≤127) (begin
          toℕ x₁ - 128 ≡⟨ sym (Fin.toℕ-fromℕ< x₁∸128<256) ⟩
          toℕ x₁' ≡⟨ cong Fin.toℕ (∷-injectiveˡ lem₃) ⟩
          toℕ x₂' ≡⟨ Fin.toℕ-fromℕ< x₂∸128<256 ⟩
          toℕ x₂ - 128 ∎))
  twosComplement-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ twos≡ | no ¬x₁≤127 | yes x₂≤127 =
    contradiction {P = ℤ.-[1+ _ ] ≡ ℤ.+ _}
      (trans (sym (proj₂ (twosComplement<0 x₁ bs₁))) twos≡)
      λ ()
  twosComplement-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ twos≡ | yes x₁≤127 | no ¬x₂≤127 =
    contradiction {P = ℤ.-[1+ _ ] ≡ ℤ.+ _}
      (trans (sym (proj₂ (twosComplement<0 x₂ bs₂))) (sym twos≡))
      λ ()
  twosComplement-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ twos≡ | yes x₁≤127 | yes x₂≤127 =
    unsigned-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ (ℤ.+-injective twos≡)
    where
    import Data.Integer.Properties as ℤ
  
  -- private
  --   tc₁ : twosComplement ([ # 255 ]) ≡ ℤ.- (ℤ.+ 1)
  --   tc₁ = refl

  --   tc₂ : twosComplement (# 252 ∷ [ # 24 ]) ≡ ℤ.- (ℤ.+ 1000)
  --   tc₂ = refl

  --   tc₃ : twosComplement (# 125 ∷ [ # 1 ]) ≡ ℤ.+ 32001
  --   tc₃ = refl

  --   tc₄ : twosComplement (# 128 ∷ [ # 0 ]) ≡ Sign.- ℤ.◃ 32768
  --   tc₄ = refl

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

  asciiNum : List UInt8 → ℕ
  asciiNum [] = 0
  asciiNum (x ∷ xs) = asciiNum₁ x * (10 ^ length xs) + asciiNum xs

  asciiNum< : ∀ bs → All (InRange '0' '9') bs → asciiNum bs < 10 ^ length bs
  asciiNum< [] allIR = s≤s z≤n
  asciiNum< (x ∷ bs) (px ∷ allIR) = ≤.begin-strict
    asciiNum (x ∷ bs) ≤.≡⟨⟩
    asciiNum₁ x * 10 ^ length bs + asciiNum bs ≤.≡⟨⟩
    (toℕ x - 48) * 10 ^ length bs + asciiNum bs
      ≤.<⟨ +-monoʳ-< ((toℕ x - 48) * 10 ^ length bs) (asciiNum< bs allIR) ⟩
    (toℕ x - 48) * 10 ^ length bs + 10 ^ length bs
      ≤.≤⟨ +-monoˡ-≤ (10 ^ length bs)
             (*-monoˡ-≤ (10 ^ length bs)
               (∸-monoˡ-≤ 48 (proj₂ px))) ⟩
    9 * 10 ^ length bs + 10 ^ length bs
      ≤.≡⟨ cong (_+ (10 ^ length bs)) -- {(10 - 1) * 10 ^ length bs}{10 * 10 ^ length bs - 1 * 10 ^ length bs}
             (begin
               (10 - 1) * 10 ^ length bs ≡⟨ *-distribʳ-∸ (10 ^ length bs) 10 1 ⟩
               10 ^ (1 + length bs) - 1 * 10 ^ length bs ≡⟨ cong ((10 ^ (1 + length bs)) ∸_) (*-identityˡ (10 ^ length bs)) ⟩
               10 ^ (1 + length bs) - 10 ^ length bs ∎)
      ⟩
    (10 ^ (1 + length bs) - 10 ^ length bs) + 10 ^ length bs
      ≤.≡⟨ m∸n+n≡m (Lemmas.^-monoʳ-≤ 10 (s≤s z≤n) (n≤1+n (length bs))) ⟩
    10 ^ (1 + length bs) ≤.∎
    where
    module ≤ = ≤-Reasoning
    open ≡-Reasoning

  showFixed₁ : ℕ → Σ UInt8 (InRange '0' '9')
  showFixed₁ n = c₁“ , ir'
    where
    module ≤ = ≤-Reasoning

    c₁ : Fin 10
    c₁ = n mod 10

    c₁' = Fin.raise (toℕ '0') c₁

    c₁“ : UInt8
    c₁“ = Fin.inject≤ c₁' (toWitness{Q = _ Nat.≤? _} tt)

    ir : InRange '0' '9' c₁'
    proj₁ ir = ≤.begin
      48 ≤.≤⟨ m≤m+n 48 (toℕ c₁) ⟩
      48 + toℕ c₁ ≤.≡⟨⟩
      toℕ c₁' ≤.∎
    proj₂ ir = ≤.begin
      toℕ c₁' ≤.≡⟨⟩
      48 + toℕ c₁ ≤.≤⟨ +-monoʳ-≤ 48 (toℕ≤pred[n] c₁) ⟩
      57 ≤.∎

    ir' : InRange '0' '9' c₁“
    ir' = subst₀ (λ x → toℕ '0' ≤ x × x ≤ toℕ '9') (sym (toℕ-inject≤ c₁' (toWitness{Q = _ Nat.≤? _} tt))) ir

  showFixed' : (w n : ℕ) → Σ (List UInt8) λ bs → length bs ≡ w × All (InRange '0' '9') bs
  showFixed' zero n = [] , (refl , All.[])
  showFixed' w@(suc w') n =
    let (c₁ , ir) = showFixed₁ quotient in
    (c₁ ∷ cs) , (cong suc len≡) , (ir ∷ irs)
    where
    open DivMod ((n divMod 10 ^ w'){fromWitnessFalse (>⇒≢ (1≤10^n w'))})
    ih = showFixed' w' (toℕ remainder)
    cs = proj₁ ih
    len≡ = proj₁ (proj₂ ih)
    irs  = proj₂ (proj₂ ih)

  showFixed : (w n : ℕ) → List UInt8
  showFixed w n = proj₁ (showFixed' w n)

  private
    sf₁ : showFixed 4 1 ≡ (# '0') ∷ (# '0') ∷ (# '0') ∷ [ # '1' ]
    sf₁ = refl

    sf₂ : showFixed 4 9999 ≡ (# '9') ∷ (# '9') ∷ (# '9') ∷ [ # '9' ]
    sf₂ = refl

  asciiNum₁∘showFixed₁≗id : ∀ n → n < 10 → asciiNum₁ (proj₁ (showFixed₁ n)) ≡ n
  asciiNum₁∘showFixed₁≗id n (s≤s n≤9) =
    let (b , ir) = showFixed₁ n in
    begin
      asciiNum₁ b ≡⟨⟩
      toℕ b - toℕ '0' ≡⟨⟩
      toℕ (Fin.inject≤ (Fin.raise (toℕ '0') (n mod 10)) pf) - toℕ '0'
        ≡⟨ cong (_∸ toℕ '0')
             (begin
               toℕ (Fin.inject≤ (Fin.raise (toℕ '0') (n mod 10)) pf) ≡⟨ toℕ-inject≤ _ pf ⟩
               toℕ (Fin.raise (toℕ '0') (n mod 10)) ≡⟨ toℕ-raise (toℕ '0') (n mod 10) ⟩
               toℕ '0' + toℕ (n mod 10) ∎) ⟩
      toℕ '0' + toℕ (n mod 10) - toℕ '0' ≡⟨ m+n∸m≡n (toℕ '0') (toℕ (n mod 10)) ⟩
      toℕ (n mod 10) ≡⟨⟩
      toℕ (Fin.fromℕ< (m%n<n n 9) ) ≡⟨ toℕ-fromℕ< (m%n<n n 9) ⟩
      n % 10 ≡⟨ m≤n⇒m%n≡m n≤9 ⟩
      n ∎
    where
    open ≡-Reasoning

    pf : 58 ≤ 256
    pf = toWitness{Q = _ Nat.≤? _} tt

  showFixed₁∘asciiNum₁≗id : ∀ b → InRange '0' '9' b → proj₁ (showFixed₁ (asciiNum₁ b)) ≡ b
  showFixed₁∘asciiNum₁≗id b ir = Fin.toℕ-injective
    (begin
      toℕ (proj₁ (showFixed₁ (asciiNum₁ b))) ≡⟨⟩
      toℕ (proj₁ (showFixed₁ (toℕ b - toℕ '0'))) ≡⟨⟩
      toℕ c‴ ≡⟨ Fin.toℕ-inject≤ c“ pf ⟩
      toℕ c“ ≡⟨ Fin.toℕ-raise (toℕ '0') c' ⟩
      toℕ '0' + toℕ c'
        ≡⟨ cong (toℕ '0' +_)
             (begin
               (toℕ (Fin.fromℕ< (m%n<n (toℕ b - toℕ '0') 9)) ≡⟨ Fin.toℕ-fromℕ< ((m%n<n (toℕ b - toℕ '0') 9)) ⟩
               (toℕ b - toℕ '0') % 10 ≡⟨ m≤n⇒m%n≡m b-0<10 ⟩
               toℕ b - toℕ '0' ∎)) ⟩
      toℕ '0' + (toℕ b - toℕ '0') ≡⟨ m+[n∸m]≡n (proj₁ ir) ⟩
      toℕ b ∎)
    where
    module ≤ = ≤-Reasoning
    open ≡-Reasoning
    pf : 57 < 256
    pf = toWitness{Q = _ Nat.≤? _} tt

    c = toℕ b - toℕ '0'
    c' = c mod 10
    c“ = Fin.raise (toℕ '0') c'
    c‴ = Fin.inject≤ c“ pf

    ir' : InRange '0' '9' c‴
    ir' = proj₂ (showFixed₁ c)

    b-0<10 : toℕ b - toℕ '0' ≤ 9
    b-0<10 = ≤.begin
      toℕ b - toℕ '0' ≤.≤⟨ ∸-monoˡ-≤ (toℕ '0') (proj₂ ir) ⟩
      9 ≤.∎

  asciiNum∘showFixed≗id : ∀ w n → n < 10 ^ w → asciiNum (showFixed w n) ≡ n
  asciiNum∘showFixed≗id zero .zero (s≤s z≤n) = refl
  asciiNum∘showFixed≗id (suc w) n n<10^w =
    let
      (c₁ , ir) = showFixed₁ quotient
      (cs , len≡ , irs) = showFixed' w (toℕ remainder)
    in
    begin
      asciiNum (showFixed (suc w) n) ≡⟨⟩
      asciiNum (c₁ ∷ cs) ≡⟨⟩
      asciiNum₁ c₁ * 10 ^ length cs + asciiNum cs
        ≡⟨ cong₂ _+_
             (cong (λ x → asciiNum₁ c₁ * (10 ^ x)) len≡)
             (asciiNum∘showFixed≗id w (toℕ remainder) (toℕ<n _)) ⟩
      asciiNum₁ c₁ * 10 ^ w + toℕ remainder
        ≡⟨ cong (λ x → x * (10 ^ w) + toℕ remainder)
             (asciiNum₁∘showFixed₁≗id quotient q<10) ⟩
      quotient * 10 ^ w + toℕ remainder ≡⟨ +-comm _ (toℕ remainder) ⟩
      toℕ remainder + quotient * 10 ^ w ≡˘⟨ property ⟩
      n ∎
    where
    module ≤ = ≤-Reasoning
    open ≡-Reasoning

    pf : False (10 ^ w ≟ 0)
    pf = fromWitnessFalse (>⇒≢ (1≤10^n w))

    dm : DivMod n (10 ^ w)
    dm = (n divMod (10 ^ w)){pf}

    open DivMod dm

    q<10 : quotient < 10
    q<10 = *-cancelʳ-<{10 ^ w} quotient 10 (≤.begin-strict
      quotient * 10 ^ w ≤.≤⟨ m≤n+m _ _ ⟩
      toℕ remainder + quotient * 10 ^ w ≤.≡⟨ sym property ⟩
      n ≤.<⟨ n<10^w ⟩
      10 ^ (suc w) ≤.∎)

  showFixed∘asciiNum≗id : ∀ bs → All (InRange '0' '9') bs → showFixed (length bs) (asciiNum bs) ≡ bs
  showFixed∘asciiNum≗id [] irs = refl
  showFixed∘asciiNum≗id (b ∷ bs) (ir ∷ irs) =
    showFixed (suc (length bs)) (asciiNum₁ b * 10 ^ length bs + asciiNum bs)
      ≡⟨ cong (showFixed (1 + length bs)) (+-comm (asciiNum₁ b * 10 ^ length bs) (asciiNum bs)) ⟩
    showFixed (suc (length bs)) (asciiNum bs + asciiNum₁ b * 10 ^ length bs) ≡⟨⟩
    proj₁ (showFixed₁ quotient) ∷ showFixed (length bs) (toℕ remainder)
      ≡⟨ cong₂ _∷_ b≡ ih ⟩
    b ∷ bs ∎
    where
    open ≡-Reasoning
    module ≤ = ≤-Reasoning

    pf = fromWitnessFalse (>⇒≢ (1≤10^n (length bs)))
    n = asciiNum bs + asciiNum₁ b * 10 ^ length bs

    open DivMod ((n divMod (10 ^ length bs)){pf})

    q≡ : quotient ≡ asciiNum₁ b
    q≡ = begin
      quotient
        ≡⟨ Lemmas.+-distrib-/-divMod (asciiNum bs) (asciiNum₁ b * 10 ^ length bs){10 ^ length bs}
             (≤.begin-strict
               (asciiNum bs % 10 ^ length bs + asciiNum₁ b * 10 ^ length bs % 10 ^ length bs
                 ≤.≡⟨ cong₂ _+_{u = asciiNum₁ b * 10 ^ length bs % 10 ^ length bs}
                        (Lemmas.m≤n⇒m%n≡m-mod' (asciiNum< bs irs))
                        (Lemmas.m*n%n≡0-mod (asciiNum₁ b) (10 ^ length bs){pf}) ⟩
               asciiNum bs + 0 ≤.≡⟨ +-identityʳ (asciiNum bs) ⟩
               asciiNum bs ≤.<⟨ asciiNum< bs irs ⟩
               _ ≤.∎)) ⟩
      asciiNum bs / 10 ^ length bs + asciiNum₁ b * 10 ^ length bs / 10 ^ length bs
        ≡⟨ cong₂ _+_ {x = asciiNum bs / 10 ^ length bs}
             (m<n⇒m/n≡0 (asciiNum< bs irs))
             (m*n/n≡m (asciiNum₁ b) (10 ^ length bs)) ⟩
      asciiNum₁ b ∎

    b≡ : proj₁ (showFixed₁ quotient) ≡ b
    b≡ = begin
      proj₁ (showFixed₁ quotient) ≡⟨ cong (λ x → proj₁ (showFixed₁ x)) q≡ ⟩
      proj₁ (showFixed₁ (asciiNum₁ b)) ≡⟨ showFixed₁∘asciiNum₁≗id b ir ⟩
      b ∎

    ≡asciiNum : toℕ remainder ≡ asciiNum bs
    ≡asciiNum = begin
      toℕ remainder ≡⟨ cong Fin.toℕ (Lemmas.[m+kn]%n≡m%n-divMod (asciiNum bs) (asciiNum₁ b) (10 ^ length bs)) ⟩
      toℕ ((asciiNum bs mod 10 ^ length bs){pf}) ≡⟨ Lemmas.m≤n⇒m%n≡m-mod (asciiNum< bs irs) ⟩
      asciiNum bs ∎

    ih : showFixed (length bs) (toℕ remainder) ≡ bs
    ih = trans (cong (showFixed (length bs)) ≡asciiNum) (showFixed∘asciiNum≗id bs irs)

  asciiNum-injective
    : (xs₁ xs₂ : List UInt8) → All (InRange '0' '9') xs₁ → All (InRange '0' '9') xs₂
      → length xs₁ ≡ length xs₂
      → asciiNum xs₁ ≡ asciiNum xs₂
      → xs₁ ≡ xs₂
  asciiNum-injective xs₁ xs₂ ir₁ ir₂ len≡ ascii≡ = begin
    xs₁ ≡˘⟨ showFixed∘asciiNum≗id xs₁ ir₁ ⟩
    showFixed (length xs₁) (asciiNum xs₁)
      ≡⟨ cong₂ showFixed len≡ ascii≡ ⟩
    showFixed (length xs₂) (asciiNum xs₂)
      ≡⟨ showFixed∘asciiNum≗id xs₂ ir₂ ⟩
    xs₂ ∎
    where
    open ≡-Reasoning


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
  isByteRep c = Any.any? (c ≟_) charset

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
