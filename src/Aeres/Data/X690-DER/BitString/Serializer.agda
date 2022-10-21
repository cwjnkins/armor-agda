{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Serializer
open import Aeres.Prelude
import      Data.Nat.Properties as Nat

module Aeres.Data.X690-DER.BitString.Serializer where

open Aeres.Grammar.Serializer UInt8

private
  serializeValueRaw : List Bool → UInt8 × List UInt8
  serializeValueRaw [] = # 0 , []
  serializeValueRaw (x₀ ∷ [])                                = # 7 , [ fromBinary (                              Vec.[ x₀ ] Vec.++ Vec.replicate{n = 7} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ [])                           = # 6 , [ fromBinary (x₀ ∷                          Vec.[ x₁ ] Vec.++ Vec.replicate{n = 6} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ [])                      = # 5 , [ fromBinary (x₀ ∷ x₁ ∷                     Vec.[ x₂ ] Vec.++ Vec.replicate{n = 5} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])                 = # 4 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷                Vec.[ x₃ ] Vec.++ Vec.replicate{n = 4} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ [])            = # 3 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷           Vec.[ x₄ ] Vec.++ Vec.replicate{n = 3} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])       = # 2 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷      Vec.[ x₅ ] Vec.++ Vec.replicate{n = 2} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ [])  = # 1 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ Vec.[ x₆ ] Vec.++ Vec.replicate{n = 1} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ xs) =
    let b         = fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ Vec.[ x₇ ])
        (bₕ , bₜ) = serializeValueRaw xs
    in bₕ , b ∷ bₜ

  @0 serializeValueRaw≡ : ∀ (bits : List Bool) {bₕ bₜ} → (bₕ<8 : toℕ bₕ < 8) (bits≡ : bits ≡ toBitRep bₕ bₜ) (u : UnusedBits bₕ bₜ)
                          → let (bₕ' , bₜ') = serializeValueRaw bits in _≡_{A = List UInt8} (bₕ' ∷ bₜ') (bₕ ∷ bₜ)
  serializeValueRaw≡ [] {bₕ} {[]} bₕ<8 bits≡ u =
    cong₂ _∷_ (Fin.toℕ-injective (sym u)) refl
  serializeValueRaw≡ [] {bₕ} {x ∷ []} bₕ<8 bits≡ u =
    contradiction{P = length xs' ≡ 0}
      (cong length (sym bits≡))
      (Nat.>⇒≢ xs'Len>)
    where
    open ≡-Reasoning
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x)
    xs' = take (8 - toℕ bₕ) xs

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x)

    xs'Len : length xs' ≡ 8 - toℕ bₕ
    xs'Len = begin
      length xs' ≡⟨ length-take (8 - toℕ bₕ) xs ⟩
      (8 - toℕ bₕ) ⊓ length xs ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) xsLen ⟩
      (8 - toℕ bₕ) ⊓ 8 ≡⟨ Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m 8 (toℕ bₕ)) ⟩
      8 - toℕ bₕ ∎

    xs'Len> : length xs' > 0
    xs'Len> = ≤.begin
      (1 ≤.≤⟨ Nat.m<n⇒0<n∸m bₕ<8 ⟩
      8 - toℕ bₕ ≤.≡⟨ sym xs'Len ⟩
      length xs' ≤.∎)

  serializeValueRaw≡ [] {bₕ} {x ∷ x₁ ∷ bₜ} bₕ<8 bits≡ u =
    contradiction{P = 0 ≥ 8}
      (Nat.≤-trans xsLen> (Lemmas.≡⇒≤ (sym $ cong length bits≡)))
      λ ()
    where
    module ≤ = Nat.≤-Reasoning

    xs₁ = Vec.toList (toBinary{8} x)
    xs₂ = toBitRep bₕ (x₁ ∷ bₜ)

    xs = xs₁ ++ xs₂

    xs₁Len : length xs₁ ≡ 8
    xs₁Len = Lemmas.toListLength (toBinary{8} x)

    xsLen> : length xs ≥ 8
    xsLen> = ≤.begin
      8 ≤.≡⟨ sym xs₁Len ⟩
      length xs₁ ≤.≤⟨ Nat.m≤m+n (length xs₁) (length xs₂) ⟩
      length xs₁ + length xs₂ ≤.≡⟨ sym (length-++ xs₁) ⟩
      length (xs₁ ++ xs₂) ≤.∎

  serializeValueRaw≡ (x ∷ []) {bₕ} {x₁ ∷ []} bₕ<8 bits≡ u =
    cong₂ _∷_ (Fin.toℕ-injective (sym bₕ≡7))
      (cong [_] (sym (begin
        (x₁ ≡⟨ sym (fromBinary∘toBinary{8} x₁) ⟩
        fromBinary (toBinary{8} x₁)
          ≡⟨ cong fromBinary (Lemmas.toList-injective (toBinary{8} x₁) (x ∷ Vec.replicate #0) (begin
               xs ≡⟨ sym (take++drop (8 - toℕ bₕ) xs) ⟩
               take (8 - toℕ bₕ) xs ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
               x ∷ replicate (toℕ bₕ) #0 ≡⟨ cong (λ y → x ∷ replicate y #0) bₕ≡7 ⟩
               x ∷ replicate 7 #0 ∎))
           ⟩
        _ ∎))))
    where
    open ≡-Reasoning

    xs  = Vec.toList (toBinary{8} x₁)
    xs' = take (8 - toℕ bₕ) xs

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₁)

    8-bₕ≡1 : 8 - toℕ bₕ ≡ 1
    8-bₕ≡1 = begin
      (8 - toℕ bₕ ≡⟨ sym (Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m _ (toℕ bₕ))) ⟩
      (8 - toℕ bₕ) ⊓ 8 ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) (sym xsLen) ⟩
      (8 - toℕ bₕ) ⊓ length xs ≡⟨ (sym $ length-take (8 - toℕ bₕ) xs) ⟩
      length xs' ≡⟨ sym (cong length bits≡) ⟩
      1 ∎)

    bₕ≡7 : toℕ bₕ ≡ 7
    bₕ≡7 = Nat.∸-cancelˡ-≡ (Nat.<⇒≤ bₕ<8) (toWitness{Q = _ ≤? _} tt) 8-bₕ≡1

    xs≡ : xs ≡ x ∷ replicate 7 #0
    xs≡ = begin
      xs ≡⟨ sym (take++drop 1 xs) ⟩
      take 1 xs ++ drop 1 xs ≡⟨ cong (λ x → take (8 - x) xs ++ drop (8 - x) xs) (sym bₕ≡7) ⟩
      xs' ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
      x ∷ replicate (toℕ bₕ) #0 ≡⟨ cong (λ y → x ∷ replicate y #0) bₕ≡7 ⟩
      x ∷ replicate 7 #0 ∎

  serializeValueRaw≡ (x ∷ []) {bₕ} {x₁ ∷ x₂ ∷ bₜ} bₕ<8 bits≡ u =
    contradiction{P = 1 ≥ 8}
      (≤.begin
        8 ≤.≡⟨ sym xsLen ⟩
        length xs ≤.≤⟨ Nat.m≤m+n (length xs) _ ⟩
        length xs + length (toBitRep bₕ (x₂ ∷ bₜ)) ≤.≡⟨ sym (length-++ xs) ⟩
        length (xs ++ toBitRep bₕ (x₂ ∷ bₜ)) ≤.≡⟨ cong length (sym bits≡) ⟩
        (length [ x ]) ≤.≡⟨⟩
        1 ≤.∎)
      λ where (s≤s ())
    where
    import Data.Nat.Properties as Nat
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x₁)

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₁)

    
  serializeValueRaw≡ (x ∷ x₁ ∷ []) {bₕ} {x₂ ∷ []} bₕ<8 bits≡ u =
    cong₂ _∷_ (Fin.toℕ-injective (sym bₕ≡6))
      (cong [_] (sym (begin
        (x₂ ≡⟨ sym (fromBinary∘toBinary{8} x₂) ⟩
        fromBinary (toBinary{8} x₂)
          ≡⟨ cong fromBinary (Lemmas.toList-injective (toBinary{8} x₂) (x ∷ x₁ ∷ Vec.replicate #0)
               (begin
                 xs ≡⟨ sym (take++drop (8 - toℕ bₕ) xs) ⟩
                 take (8 - toℕ bₕ) xs ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
                 x ∷ x₁ ∷ replicate (toℕ bₕ) #0 ≡⟨ cong (λ y → x ∷ x₁ ∷ replicate y #0) bₕ≡6 ⟩
                 x ∷ x₁ ∷ replicate 6 #0 ∎))
           ⟩
        _ ∎))))
    where
    open ≡-Reasoning

    xs = Vec.toList (toBinary{8} x₂)
    xs' = take (8 - toℕ bₕ) xs

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₂)

    8-bₕ≡2 : 8 - toℕ bₕ ≡ 2
    8-bₕ≡2 = begin
      (8 - toℕ bₕ ≡⟨ sym (Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m _ (toℕ bₕ))) ⟩
      (8 - toℕ bₕ) ⊓ 8 ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) (sym xsLen) ⟩
      (8 - toℕ bₕ) ⊓ length xs ≡⟨ (sym $ length-take (8 - toℕ bₕ) xs) ⟩
      length xs' ≡⟨ sym (cong length bits≡) ⟩
      2 ∎)

    bₕ≡6 : toℕ bₕ ≡ 6
    bₕ≡6 = Nat.∸-cancelˡ-≡ (Nat.<⇒≤ bₕ<8) (toWitness{Q = _ ≤? _} tt) 8-bₕ≡2

    xs≡ : xs ≡ x ∷ x₁ ∷ replicate 6 #0
    xs≡ = begin
      xs ≡⟨ sym (take++drop 2 xs) ⟩
      take 2 xs ++ drop 2 xs ≡⟨ cong (λ x → take (8 - x) xs ++ drop (8 - x) xs) (sym bₕ≡6) ⟩
      xs' ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
      x ∷ x₁ ∷ replicate (toℕ bₕ) #0 ≡⟨ cong (λ y → x ∷ x₁ ∷ replicate y #0) bₕ≡6 ⟩
      x ∷ x₁ ∷ replicate 6 #0 ∎

  serializeValueRaw≡ (x ∷ x₁ ∷ []) {bₕ} {x₂ ∷ x₃ ∷ bₜ} bₕ<8 bits≡ u =
    contradiction{P = 2 ≥ 8}
      (≤.begin
        8 ≤.≡⟨ sym xsLen ⟩
        length xs ≤.≤⟨ Nat.m≤m+n (length xs) _ ⟩
        length xs + length (toBitRep bₕ (x₃ ∷ bₜ)) ≤.≡⟨ sym (length-++ xs) ⟩
        length (xs ++ toBitRep bₕ (x₃ ∷ bₜ)) ≤.≡⟨ cong length (sym bits≡) ⟩
        length (x ∷ [ x₁ ]) ≤.≡⟨⟩
        2 ≤.∎)
      λ where (s≤s (s≤s ()))
    where
    import Data.Nat.Properties as Nat
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x₂)

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₂)

  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ []) {bₕ} {x₃ ∷ []} bₕ<8 bits≡ u = {!!}
  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ []) {bₕ} {x₃ ∷ x₄ ∷ bₜ} bₕ<8 bits≡ u = {!!}
  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ bits) {bₕ} {bₜ} bₕ<8 bits≡ u = {!!}

serializeValue : Serializer BitStringValue
Singleton.x (serializeValue x) =
  let (bₕ , bₜ) = serializeValueRaw ∘ Singleton.x ∘ BitStringValue.bits $ x
  in bₕ ∷ bₜ
Singleton.x≡ (serializeValue (mkBitStringValue bₕ bₜ bₕ<8 (singleton bits bits≡) unusedBits refl)) =
  serializeValueRaw≡ bits bₕ<8 bits≡ unusedBits

serialize : Serializer BitString
serialize = TLV.serialize serializeValue
