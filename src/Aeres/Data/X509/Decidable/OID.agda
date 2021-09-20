{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Parser
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.OID where

open Base256

module parseOIDSub where
  here' = "parseOIDSub"

  parseOIDSub : Parser Dig (Logging ∘ Dec) Generic.OIDSub
  runParser parseOIDSub xs
    with runParser (parseWhileₜ Dig ((_≥? 128) ∘ toℕ)) xs
  ... | no  ¬parse = do
    tell $ here' String.++ ": underflow"
    return ∘ no $ ‼ go
    where
    @0 go : ¬ Success Dig Generic.OIDSub xs
    go (success ._ read@._ refl (Generic.mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl) suffix refl) =
      contradiction (success (lₚ ∷ʳ lₑ) read refl (mkParseWhile lₚ lₑ lₚ≥128 (<⇒≱ lₑ<128) refl) suffix refl) ¬parse
  ... | yes (success ._ _ read≡ (mkParseWhile lₚ lₑ lₚ≥128 ¬lₑ≥128 refl) suffix refl)
    with lₚ
  ... | [] = return (yes (success [ lₑ ] _ read≡ (Generic.mkOIDSub [] All.[] lₑ (≰⇒> ¬lₑ≥128) tt refl) suffix refl))
  ... | lₚ'@(l ∷ lₚ)
    with toℕ l >? 128
  ... | no  l≯128 = do
    tell $ here' String.++ ": leading byte has value 0 (non-minimal repr.)"
    return ∘ no $ ‼ go
    where
    @0 go : ¬ Success Dig Generic.OIDSub (lₚ' ∷ʳ lₑ ++ suffix)
    go (success .([] ∷ʳ lₑ1) _ read≡ (Generic.mkOIDSub [] lₚ1≥128 lₑ1 lₑ1<128 leastDigs1 refl) .((lₚ ++ [ lₑ ]) ++ suffix) refl) =
      contradiction lₑ1<128 (≤⇒≯ (proj₁ (All.uncons lₚ≥128)))
    go (success .((x ∷ lₚ1) ∷ʳ lₑ1) _ read≡ (Generic.mkOIDSub (x ∷ lₚ1) lₚ1≥128 lₑ1 lₑ1<128 leastDigs1 refl) suffix1 ps≡1) =
      contradiction (subst (λ y → 128 < toℕ y) (∷-injectiveˡ ps≡1) leastDigs1) l≯128
  ... | yes l>128 =
    return (yes (success (lₚ' ∷ʳ lₑ) _ read≡ (Generic.mkOIDSub lₚ' lₚ≥128 lₑ (≰⇒> ¬lₑ≥128) l>128 refl) suffix refl))

open parseOIDSub public using (parseOIDSub)

module parseOIDField where
  here' = "parseOIDField"

  open ≡-Reasoning

  parseOIDFieldWF : ∀ n → ParserWF Dig (Logging ∘ Dec) (_×ₚ_ Dig Generic.OIDField ((_≡ n) ∘ length))
  runParser (parseOIDFieldWF n) xs (WellFounded.acc rs) = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ r₀≤len refl) suf₀ ps≡₀) ← runParser (parse≤ _ n parseOIDSub NonNesting.OIDSub (tell $ here' String.++ ": overflow")) xs
      where no ¬parse → do
        return ∘ no $ ‼ λ where
          (success prefix r r≡ (mk×ₚ Generic.[ sub ]OID r≡n refl) suffix ps≡) →
            contradiction (success prefix r r≡ (mk×ₚ sub (subst₀ (λ i → i ≤ n) (sym r≡n) ≤-refl) refl) suffix ps≡) ¬parse
          (success .(bs₁ ++ bs₂) r r≡ (mk×ₚ (Generic.cons (Generic.mkOIDFieldₐ{bs₁}{bs₂} sub rest refl)) r≡n refl) suffix ps≡) →
            contradiction
              (success bs₁ (length bs₁) refl (mk×ₚ sub (m+n≤o⇒m≤o _ {length bs₂} (subst (λ i → i ≤ n) (trans (sym r≡n) (length-++ bs₁)) ≤-refl)) refl) (bs₂ ++ suffix)
                (begin (bs₁ ++ bs₂   ++ suffix ≡⟨ solve (++-monoid Dig) ⟩
                        (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                        xs                     ∎)))
              ¬parse
    case <-cmp r₀ n of λ where
      (tri> r₀≮n r₀≢n r₀>n) →
        contradiction (r₀ ≤ n ∋ subst (λ i → i ≤ n) (sym r₀≡) r₀≤len) (<⇒≱ r₀>n)
      (tri≈ _ r₀≡n _) →
        return (yes (success pre₀ r₀ r₀≡ (mk×ₚ Generic.[ v₀ ]OID (trans₀ (sym r₀≡) r₀≡n) refl) suf₀ ps≡₀))
      (tri< r₀<n _ _) → do
        let @0 suf₀<xs : length suf₀ < length xs
            suf₀<xs = subst₀ (λ x → length suf₀ < length x) ps≡₀ (Lemmas.length-++-< pre₀ suf₀ (NonEmpty.OIDSub v₀))
        yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ r₁≡len-pre₁ refl) suf₁ ps≡₁) ← runParser (parseOIDFieldWF (n - r₀)) suf₀ (rs _ suf₀<xs)
          where no ¬parse → do
            return ∘ no $ ‼ λ where
              (success prefix read read≡ (mk×ₚ Generic.[ sub ]OID r≡n refl) suffix ps≡) →
                <⇒≢ r₀<n (‼ (begin (r₀            ≡⟨ r₀≡ ⟩
                                    length pre₀   ≡⟨ cong length (NonNesting.OIDSub (trans ps≡₀ (sym ps≡)) v₀ sub) ⟩
                                    length prefix ≡⟨ r≡n ⟩
                                    n             ∎)))
              (success .(bs₁ ++ bs₂) read read≡ (mk×ₚ (Generic.cons (Generic.mkOIDFieldₐ{bs₁}{bs₂} sub rest refl)) r≡n refl) suffix ps≡) → ‼
                let @0 xs≡ : pre₀ ++ suf₀ ≡ bs₁ ++ bs₂ ++ suffix
                    xs≡ = begin (pre₀ ++ suf₀           ≡⟨ ps≡₀ ⟩
                                 xs                     ≡⟨ sym ps≡ ⟩
                                 (bs₁ ++ bs₂) ++ suffix ≡⟨ solve (++-monoid Dig) ⟩
                                 bs₁ ++ bs₂ ++ suffix   ∎)
                    @0 pre₀≡bs₁ : pre₀ ≡ bs₁
                    pre₀≡bs₁ = NonNesting.OIDSub xs≡ v₀ sub
                in contradiction
                  (success bs₂ (length bs₂) refl
                    (mk×ₚ rest (+-cancelˡ-≡ r₀
                                 (begin (r₀ + length bs₂ ≡⟨ cong (_+ length bs₂) r₀≡ ⟩
                                        length pre₀ + length bs₂ ≡⟨ cong (λ x → length x + length bs₂) pre₀≡bs₁ ⟩
                                        length bs₁ + length bs₂ ≡⟨ sym (length-++ bs₁) ⟩
                                        length (bs₁ ++ bs₂) ≡⟨ r≡n ⟩
                                        n ≡⟨ sym (+-identityʳ _) ⟩
                                        n + 0 ≡⟨ cong (n +_) (sym (n∸n≡0 r₀)) ⟩
                                        n + (r₀ - r₀) ≡⟨ sym (+-∸-assoc n {r₀} ≤-refl) ⟩
                                        (n + r₀) - r₀ ≡⟨ cong (_∸ r₀) (+-comm n _) ⟩
                                        (r₀ + n) - r₀ ≡⟨ +-∸-assoc r₀ {n} (<⇒≤ r₀<n) ⟩
                                        r₀ + (n - r₀) ∎)))
                      refl)
                    suffix (++-cancelˡ bs₁ (trans (sym xs≡) (cong (_++ suf₀) pre₀≡bs₁))))
                  ¬parse
        return (yes (success (pre₀ ++ pre₁) (r₀ + r₁)
                      (begin (r₀ + r₁ ≡⟨ cong (_+ r₁) r₀≡ ⟩
                             length pre₀ + r₁ ≡⟨ cong (_ +_) r₁≡ ⟩
                             length pre₀ + length pre₁ ≡⟨ sym (length-++ pre₀) ⟩
                             length (pre₀ ++ pre₁) ∎))
                      (mk×ₚ (Generic.cons (Generic.mkOIDFieldₐ v₀ v₁ refl))
                        (‼ (begin (length (pre₀ ++ pre₁)    ≡⟨ length-++ pre₀ ⟩
                                  length pre₀ + length pre₁ ≡⟨ cong (_+ _) (sym r₀≡) ⟩
                                  r₀ + length pre₁          ≡⟨ cong (r₀ +_) r₁≡len-pre₁ ⟩
                                  r₀ + (n - r₀)             ≡⟨ sym (+-∸-assoc r₀ (<⇒≤ r₀<n)) ⟩
                                  r₀ + n - r₀               ≡⟨ cong (_∸ r₀) (+-comm r₀ n) ⟩
                                  n + r₀ - r₀               ≡⟨ +-∸-assoc n {n = r₀} ≤-refl ⟩
                                  n + (r₀ - r₀)             ≡⟨ cong (n +_) (n∸n≡0 r₀) ⟩
                                  n + 0                     ≡⟨ +-identityʳ n ⟩
                                  n                         ∎)))
                        refl)
                      suf₁
                      (begin ((pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Dig) ⟩
                             pre₀ ++ pre₁ ++ suf₁    ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                             pre₀ ++ suf₀            ≡⟨ ps≡₀ ⟩
                             xs                      ∎))))

parseOIDField : ∀ n → Parser Dig (Logging ∘ Dec) (_×ₚ_ Dig Generic.OIDField ((_≡ n) ∘ length))
runParser (parseOIDField n) xs =
  runParser (parseOIDField.parseOIDFieldWF n) xs (<-wellFounded (length xs))
  where
  open import Data.Nat.Induction

module parseOID where
  here' = "parseOID"

  open ≡-Reasoning

  parseOID : Parser Dig (Logging ∘ Dec) Generic.OID
  runParser parseOID [] = do
    tell $ here' String.++ ": underflow"
    return ∘ no $ λ where
      (success .(Tag.ObjectIdentifier ∷ l ++ o) read read≡ (Generic.mkOid{l}{o} len oid len≡ refl) suffix ())
  runParser parseOID (x ∷ xs)
    with x ≟ Tag.ObjectIdentifier
  ... | no  x≢ = do
    tell $ here' String.++ ": tag mismatch"
    return ∘ no $ λ where
      (success .(Tag.ObjectIdentifier ∷ l ++ o) read read≡ (Generic.mkOid {l} {o} len oid len≡ refl) suffix ps≡) →
        contradiction (∷-injectiveˡ (sym ps≡)) x≢
  ... | yes refl = do
    yes (success pre₀ r₀ r₀≡ len₀ suf₀ ps≡₀) ← runParser parseLen xs
      where no ¬parse → do
        tell here'
        return ∘ no $ λ where
          (success .(Tag.ObjectIdentifier ∷ l ++ o) read read≡ (Generic.mkOid{l}{o} len oid len≡ refl) suffix ps≡) →
            contradiction
              (success l _ refl len (o ++ suffix)
                (∷-injectiveʳ{x = Tag.ObjectIdentifier}{Tag.ObjectIdentifier}
                  (begin (Tag.ObjectIdentifier ∷ l ++ o ++ suffix   ≡⟨ cong (Tag.ObjectIdentifier ∷_) (solve (++-monoid Dig)) ⟩
                          Tag.ObjectIdentifier ∷ (l ++ o) ++ suffix ≡⟨ ps≡ ⟩
                          Tag.ObjectIdentifier ∷ xs                 ∎))))
              ¬parse
    yes (success pre₁ r₁ r₁≡ (mk×ₚ oidₑ ≡n refl) suf₁ ps≡₁) ← runParser (parseOIDField (getLength len₀)) suf₀
      where no ¬parse → do
        tell here'
        return ∘ no $ λ where
          (success .(Tag.ObjectIdentifier ∷ l ++ o) read read≡ (Generic.mkOid{l}{o} len oid len≡ refl) suffix ps≡) → ‼
            let @0 l≡ : l ≡ pre₀
                l≡ = NonNesting.LengthNN
                       (begin (l ++ (o ++ suffix) ≡⟨ solve (++-monoid Dig) ⟩
                               (l ++ o) ++ suffix ≡⟨ ∷-injectiveʳ ps≡ ⟩
                               xs ≡⟨ sym ps≡₀ ⟩
                               pre₀ ++ suf₀ ∎))
                       len len₀
                @0 len₀≡ : getLength len ≡ getLength len₀
                len₀≡ = (begin (getLength len ≡⟨ sym $
                                                 ≡-elim (λ {bs'} (eq : l ≡ bs') → (len' : Length l) → getLength (subst Length eq len) ≡ getLength len)
                                                   (λ _ → refl) l≡ len ⟩
                               getLength (subst Length l≡ len) ≡⟨ cong getLength (Unambiguous.LengthUA (subst (λ x → Length x) l≡ len) len₀) ⟩
                               getLength len₀ ∎))
            in contradiction
              (success o _ refl
                (mk×ₚ oid (begin (length o      ≡⟨ sym len≡ ⟩
                                 getLength len  ≡⟨ len₀≡ ⟩
                                 getLength len₀ ∎))
                  refl)
                suffix
                (++-cancelˡ (Tag.ObjectIdentifier ∷ pre₀)
                  (begin (Tag.ObjectIdentifier ∷ pre₀ ++ o ++ suffix ≡⟨ cong (λ i → Tag.ObjectIdentifier ∷ i ++ o ++ suffix) (sym l≡) ⟩
                         Tag.ObjectIdentifier ∷ l ++ o ++ suffix ≡⟨ cong (Tag.ObjectIdentifier ∷_) (solve (++-monoid Dig)) ⟩
                         Tag.ObjectIdentifier ∷ (l ++ o) ++ suffix ≡⟨ ps≡ ⟩
                         Tag.ObjectIdentifier ∷ xs ≡⟨ cong (Tag.ObjectIdentifier ∷_) (sym ps≡₀) ⟩
                         Tag.ObjectIdentifier ∷ pre₀ ++ suf₀ ∎))))
              ¬parse
    return (yes
      (success (Tag.ObjectIdentifier ∷ pre₀ ++ pre₁) (1 + r₀ + r₁)
        (cong suc
          (begin (r₀ + r₁ ≡⟨ cong (_+ r₁) r₀≡ ⟩
                 length pre₀ + r₁ ≡⟨ cong (_ +_) r₁≡ ⟩
                 length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀ ) ⟩
                 length (pre₀ ++ pre₁) ∎)))
        (Generic.mkOid len₀ oidₑ (sym ≡n) refl) suf₁ (cong (Tag.ObjectIdentifier ∷_)
          (begin ((pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Dig) ⟩
                  pre₀ ++ pre₁ ++ suf₁ ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                  pre₀ ++ suf₀ ≡⟨ ps≡₀ ⟩
                  xs ∎)))))
