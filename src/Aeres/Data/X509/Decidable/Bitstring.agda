{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.Bitstring where

open Base256

module parseBitstring where

  open import Aeres.Data.X509.Decidable.Length
  open ≡-Reasoning

  here' = "parseBitstring"

  parseBitstring : Parser Dig (Logging ∘ Dec) Generic.Bitstring
  runParser parseBitstring [] = do
    tell $ here' String.++ ": underflow"
    return ∘ no $ λ where
      (success .(Tag.Bitstring ∷ _ ++ val) read read≡ (Generic.mkBitString len val _ refl) suffix ())
  runParser parseBitstring (x ∷ xs)
    with x ≟ Tag.Bitstring
  ... | no  x≢ = do
    tell $ here' String.++ ": tag mis-match"
    return ∘ no $ λ where
      (success .(Tag.Bitstring ∷ _ ++ val) read read≡ (Generic.mkBitString len val _ refl) suffix ps≡) →
        contradiction (∷-injectiveˡ (sym ps≡)) x≢
  ... | yes refl = do
    yes (success pre₀ r₀ r₀≡ len suf₀ ps≡₀) ← runParser parseLen xs
      where no ¬parse → do
        tell here'
        return ∘ no $ λ where
          (success .(Tag.Bitstring ∷ _ ++ val) read read≡ (Generic.mkBitString{l} len val _ refl) suffix ps≡) →
            contradiction
              (success l _ refl len (val ++ suffix)
                (∷-injectiveʳ
                  (begin (Tag.Bitstring ∷ l ++ val ++ suffix  ≡⟨ cong (Tag.Bitstring ∷_) (solve (++-monoid Dig)) ⟩
                         Tag.Bitstring ∷ (l ++ val) ++ suffix ≡⟨ ps≡ ⟩
                         Tag.Bitstring ∷ xs                   ∎))))
              ¬parse
    yes (success pre₁ r₁ r₁≡ (bs , refl , bsLen) suf₁ ps≡₁) ← runParser (parseN Dig (getLength len) (tell $ here' String.++ ": underflow")) suf₀
      where no ¬parse → do
        tell here'
        return ∘ no $ ‼ λ where
          (success .(Tag.Bitstring ∷ _ ++ val) read read≡ (Generic.mkBitString{l} len' val len≡ refl) suffix ps≡) → ‼
            let @0 xs≡ : pre₀ ++ suf₀ ≡ l ++ val ++ suffix
                xs≡ = begin (pre₀ ++ suf₀ ≡⟨ ps≡₀ ⟩
                           xs ≡⟨ (sym $ ∷-injectiveʳ ps≡ ) ⟩
                           (l ++ val) ++ suffix ≡⟨ solve (++-monoid Dig) ⟩
                           l ++ val ++ suffix ∎)
                @0 pre₀≡ : pre₀ ≡ l
                pre₀≡ = NonNesting.LengthNN xs≡ len len'
                @0 len'≡ : getLength len' ≡ getLength len
                len'≡ = begin
                  (getLength len' ≡⟨ ≡-elim (λ eq → getLength len' ≡ getLength (subst Length eq len')) refl (sym pre₀≡) ⟩
                  getLength (subst (λ i → Length i) (sym pre₀≡) len') ≡⟨ cong getLength (Unambiguous.LengthUA (subst (λ i → Length i) (sym pre₀≡) len') len) ⟩
                  getLength len ∎)
            in
            contradiction
              (success val _ refl (val , refl , trans (sym len≡) len'≡) suffix
                (++-cancelˡ pre₀
                  (begin (pre₀ ++ val ++ suffix ≡⟨ cong (λ x → x ++ val ++ suffix) pre₀≡ ⟩
                         l ++ val ++ suffix ≡⟨ solve (++-monoid Dig) ⟩
                         (l ++ val) ++ suffix ≡⟨ ∷-injectiveʳ ps≡ ⟩
                         xs ≡⟨ sym ps≡₀ ⟩
                         pre₀ ++ suf₀ ∎))))
              ¬parse
    return (yes
      (success (Tag.Bitstring ∷ pre₀ ++ pre₁)
        (1 + r₀ + r₁)
        (cong suc
          (begin (r₀ + r₁ ≡⟨ cong (_+ r₁) r₀≡ ⟩
                 length pre₀ + r₁ ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
                 length pre₀ + length pre₁ ≡⟨ sym (length-++ pre₀) ⟩
                 length (pre₀ ++ pre₁) ∎)))
        (Generic.mkBitString len bs (sym bsLen) refl) suf₁
        (cong (Tag.Bitstring ∷_)
          (begin ((pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Dig) ⟩
                 pre₀ ++ pre₁ ++ suf₁ ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                 pre₀ ++ suf₀ ≡⟨ ps≡₀ ⟩
                 xs ∎)))))
