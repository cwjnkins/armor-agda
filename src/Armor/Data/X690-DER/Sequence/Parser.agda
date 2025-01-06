open import Armor.Binary
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Sequence.Properties
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X690-DER.Sequence.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Seq         UInt8

module _ {A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ {@0 bs' : List UInt8} (default : A bs') (loc : String) where
  parseDefault₁
    : ∀ {B} → @0 Unambiguous A → @0 NoSubstrings A → @0 NoConfusion A B
      → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B
      → Parser (Logging ∘ Dec) (&ₚ (Default A default) B)
  runParser (parseDefault₁ ua₁ ns₁ nc p₁ p₂) xs = do
    (yes (success pre r r≡ (mk&ₚ{pre₁}{pre₂} oa b refl) suf ps≡)) ← runParser (parseOption₁ loc ns₁ p₁ p₂) xs
      where no ¬p → do
        return ∘ no $ λ where
          (success pre r r≡ (mk&ₚ (mkDefault oa _) b refl) suf ps≡) →
            contradiction (success pre r r≡ (mk&ₚ oa b refl) suf ps≡)
            ¬p
    case Default.notDefault? {bs' = bs'} default oa ret (const _) of λ where
      (no ¬p) → do
        let
          a : Σ (A pre₁) ((oa ≡_) ∘ some)
          a = case (singleton oa refl) ret (const _) of λ where
            (singleton none refl) → contradiction tt ¬p
            (singleton (some x) refl) → x ,e refl{A = Option A pre₁}
        tell $ loc String.++ ": explicit default value"
        return ∘ no $ λ where
          (success pre' r' r'≡ (mk&ₚ (mkDefault none nd) b' refl) suf' ps≡') →
            let
              @0 ++≡ : pre₁ ++ pre₂ ++ suf ≡ pre' ++ suf'
              ++≡ = begin
                pre₁ ++ pre₂ ++ suf ≡⟨ sym (++-assoc pre₁ pre₂ suf) ⟩
                (pre₁ ++ pre₂) ++ suf ≡⟨ ps≡ ⟩
                _ ≡⟨ sym ps≡' ⟩
                pre' ++ suf' ∎
            in
            contradiction
              b'
              (nc ++≡ (proj₁ a))
          (success pre' r' r'≡ (mk&ₚ{pre₁'}{pre₂'} (mkDefault (some a') nd) b' refl) suf' ps≡') →
            let
              @0 ++≡ : pre₁ ++ pre₂ ++ suf ≡ pre₁' ++ pre₂' ++ suf'
              ++≡ = begin
                pre₁ ++ pre₂ ++ suf ≡⟨ sym (++-assoc pre₁ pre₂ suf) ⟩
                (pre₁ ++ pre₂) ++ suf ≡⟨ ps≡ ⟩
                _ ≡⟨ sym ps≡' ⟩
                (pre₁' ++ pre₂') ++ suf' ≡⟨ ++-assoc pre₁' pre₂' suf' ⟩
                _ ∎
            in
            ‼
            (case ns₁ ++≡ (proj₁ a) a' ret (const _) of λ where
              refl →
                contradiction
                  (subst (Default.NotDefault default)
                    (some a' ≡ oa ∋ (trans (cong some (ua₁ a' (proj₁ a))) (sym (proj₂ a))))
                    nd)
                  ¬p)
      (yes p) → return (yes
        (success pre r r≡ (mk&ₚ (mkDefault oa p) b refl) suf ps≡))
    where
    open ≡-Reasoning

  parseDefaultOption
    : ∀ {B}
      → @0 Unambiguous A → @0 NoSubstrings A → @0 NoSubstrings B
      → @0 NoConfusion A B
      → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B
      → ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Default A default) (Option B)) n)
  runParser (parseDefaultOption ua₁ ns₁ ns₂ nc p₁ p₂ 0) xs =
    return (yes (success [] _ refl (mk×ₚ (mk&ₚ (mkDefault none tt) none refl) (─ refl)) xs refl))
  runParser (parseDefaultOption ua₁ ns₁ ns₂ nc p₁ p₂ n@(suc _)) xs = do
    (yes (success pre₁ r₁ r₁≡ (mk×ₚ (mk&ₚ{bs₁}{bs₂} oa ob refl) abLen) suf₁ ps≡₁)) ← runParser (parseOption₂ loc ns₁ ns₂ nc p₁ p₂ n) xs
      where no ¬p₁₂ → do
        tell $ loc String.++ ": failed to parse"
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (mk&ₚ (mkDefault oa _) ob refl) abLen) suffix ps≡) →
            contradiction
              (success prefix _ read≡ (mk×ₚ (mk&ₚ oa ob refl) abLen) suffix ps≡)
              ¬p₁₂
    case Default.notDefault? default oa ret (const _) of λ where
      (no ¬p) → do
        let
          a : Σ (A bs₁) λ a → oa ≡ some a
          a =
            case (singleton oa refl) ret (const _) of λ where
              (singleton none refl) → contradiction tt ¬p
              (singleton (some x) refl) → _,e_{A = A bs₁}{B = λ a → some x ≡ some a} x refl
        tell $ loc String.++ ": explicit encoding of default value"
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁'}{bs₂'} (mkDefault (some a') nd') ob' refl) abLen) suffix ps≡) →
            let
              @0 ++≡ : bs₁ ++ bs₂ ++ suf₁ ≡ bs₁' ++ bs₂' ++ suffix
              ++≡ = begin
                bs₁ ++ bs₂ ++ suf₁ ≡⟨ sym (++-assoc bs₁ bs₂ suf₁) ⟩
                (bs₁ ++ bs₂) ++ suf₁ ≡⟨ ps≡₁ ⟩
                xs ≡⟨ sym ps≡ ⟩
                (bs₁' ++ bs₂') ++ suffix ≡⟨ ++-assoc bs₁' bs₂' suffix ⟩
                bs₁' ++ bs₂' ++ suffix ∎
            in
            case ‼ ns₁ ++≡ (proj₁ a) a' ret (const _) of λ where
              refl → case some a' ≡ oa ∋ trans₀{y = some (proj₁ a)} (cong (some{xs = bs₁}) (ua₁ a' (proj₁ a))) (sym (proj₂ a)) ret (const _) of λ where
                refl → contradiction nd' ¬p
          (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁'}{bs₂'} (mkDefault none nd') none refl) (─ ())) suffix ps≡)
          (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁'}{bs₂'} (mkDefault none nd') (some b') refl) abLen) suffix ps≡) →
            contradiction
              b'
              (nc
                (begin
                  bs₁ ++ bs₂ ++ suf₁ ≡⟨ sym (++-assoc bs₁ bs₂ suf₁) ⟩
                  (bs₁ ++ bs₂) ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  prefix ++ suffix ∎)
                (proj₁ a))
      (yes p) →
        return (yes
          (success pre₁ _ r₁≡ (mk×ₚ (mk&ₚ (mkDefault oa p) ob refl) abLen) suf₁ ps≡₁))
    where
    open ≡-Reasoning


module _ {B C E F : @0 List UInt8 → Set} ⦃ _ : Eq≋ B ⦄  ⦃ _ : Eq≋ C ⦄ ⦃ _ : Eq≋ E ⦄ ⦃ _ : Eq≋ F ⦄ {@0 bs' bs'' bs''' bs'''' : List UInt8}
  (default₂ : B bs') (default₃ : C bs'') (default₅ : E bs''') (default₆ : F bs'''') (loc : String) where

  parseOption₂Default₄
      : ∀ {A D : @0 List UInt8 → Set}
      → @0 Unambiguous A → @0 NoSubstrings A
      → @0 Unambiguous B → @0 NoSubstrings B
      → @0 Unambiguous C → @0 NoSubstrings C
      → @0 Unambiguous D → @0 NoSubstrings D
      → @0 Unambiguous E → @0 NoSubstrings E
      → @0 Unambiguous F → @0 NoSubstrings F
      → @0 NoConfusion A B → @0 NoConfusion A C → @0 NoConfusion A D → @0 NoConfusion A E → @0 NoConfusion A F
      → @0 NoConfusion B C → @0 NoConfusion B D → @0 NoConfusion B E → @0 NoConfusion B F
      → @0 NoConfusion C D → @0 NoConfusion C E → @0 NoConfusion C F
      → @0 NoConfusion D E → @0 NoConfusion D F
      → @0 NoConfusion E F
      → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B → Parser (Logging ∘ Dec) C
      → Parser (Logging ∘ Dec) D → Parser (Logging ∘ Dec) E → Parser (Logging ∘ Dec) F
      → ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option A) (&ₚ (Default B default₂) (&ₚ(Default C default₃)
                                   (&ₚ (Option D) (&ₚ (Default E default₅) (Default F default₆)))))) n)
  runParser (parseOption₂Default₄ ua ns₁ ub ns₂ uc ns₃ ud ns₄ ue ns₅ uf ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf zero) xs =
    return (yes (success [] _ refl (mk×ₚ (mk&ₚ none (mk&ₚ (mkDefault none tt) (mk&ₚ (mkDefault none tt) (mk&ₚ none (mk&ₚ (mkDefault none tt) (mkDefault none tt)
                refl) refl) refl) refl) refl) (─ refl)) xs refl))
  runParser (parseOption₂Default₄{A}{D} ua ns₁ ub ns₂ uc ns₃ ud ns₄ ue ns₅ uf ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf n@(suc _)) xs = do
    (yes mine@(success pre₁ r₁ r₁≡ (mk×ₚ  (mk&ₚ {bs₁}{bs₂'} oa (mk&ₚ {bs₂}{bs₃'} ob (mk&ₚ {bs₃}{bs₄'} oc (mk&ₚ {bs₄}{bs₅'} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf₁ ps≡₁)) ←
      runParser (parse₂Option₆ loc ns₁ ns₂ ns₃ ns₄ ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf n) xs
      where no ¬p₁₂' → do
        tell $ loc String.++ ": failed to parse"
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ  (mk&ₚ oa (mk&ₚ (mkDefault ob _) (mk&ₚ (mkDefault oc _) (mk&ₚ od (mk&ₚ (mkDefault oe _) (mkDefault of _) refl) refl) refl) refl) refl) abcdefLen) suffix ps≡) →
            contradiction
              (success prefix _ read≡ (mk×ₚ  (mk&ₚ oa (mk&ₚ ob (mk&ₚ oc (mk&ₚ od (mk&ₚ oe of refl) refl) refl) refl) refl) abcdefLen) suffix ps≡)
              ¬p₁₂'
    case (Default.notDefault? default₂ ob)  ,′e (Default.notDefault?  default₃ oc ,′e (Default.notDefault?  default₅ oe ,′e Default.notDefault? default₆ of))
      ret const _ of λ where
        (no ¬pb , c , e , f) → return ∘ no $ λ where
          theirs@(success prefix read read≡
            (mk×ₚ
              (mk&ₚ {bs₁ = bs₁'} {bs₂ = bs₂₃₄₅₆'} oa'
              (mk&ₚ {bs₁ = bs₂'} {bs₂ = bs₃₄₅₆'} (mkDefault ob' obnd)
              (mk&ₚ {bs₁ = bs₃'} {bs₂ = bs₄₅₆'} (mkDefault oc' ocnd)
              (mk&ₚ {bs₁ = bs₄'} {bs₂ = bs₅₆'} od'
              (mk&ₚ {bs₁ = bs₅'} {bs₂ = bs₆'} (mkDefault oe' oend)
                     (mkDefault of' ofnd) refl) refl) refl) refl) refl) abcdefLen)
            suffix ps≡) →
            let b : Σ (B bs₂) (λ b → ¬ Default.NotDefault default₂ (some b))
                b = case (Singleton ob ∋ singleton ob refl) ret (const _) of λ where
                  (singleton none refl) → contradiction tt ¬pb
                  (singleton (some x) refl) → (x , ¬pb)

                isSomeB : T (isSome ob)
                isSomeB = case (Singleton ob ∋ singleton ob refl) ret (const _) of λ where
                  (singleton none refl) → contradiction tt ¬pb
                  (singleton (some x) refl) → tt
            in
            case ((singleton oa refl) ,′e (singleton oa' refl)) ret (const _) of λ where
              ((singleton none refl) , (singleton none refl)) →
                let @0 xs≡₀ : (bs₂' ++ bs₃₄₅₆') ++ suffix ≡ (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                    xs≡₀ = trans ps≡ (sym ps≡₁)

                    @0 xs≡₁ : bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                    xs≡₁ = (begin
                            bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
                            ≡⟨ xs≡₀ ⟩
                            (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                            ∎ )                         
                in
                case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                  ret (const _) of λ where
                    (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        let
                          @0 bs₂≡ : bs₂' ≡ bs₂
                          bs₂≡ =
                            ns₂
                            (begin
                              bs₂' ++ (bs₃₄₅₆' ++ suffix)
                             ≡⟨ sym (++-assoc bs₂' _ _) ⟩
                              (bs₂' ++ bs₃₄₅₆') ++ suffix
                             ≡⟨ xs≡₀ ⟩
                               (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                             ≡⟨ ++-assoc bs₂ (bs₃ ++ bs₄ ++ bs₅ ++ bs₆) suf₁  ⟩
                               bs₂ ++ ((bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁)
                             ∎ )
                            b' (proj₁  b)
                        in
                        case (‼ bs₂≡) ret (const _) of λ where
                          refl →
                            let @0 b≡ : proj₁ b ≡ b'
                                b≡ = ub (proj₁ b) b'
                            in
                            contradiction
                              (subst₀ (λ x → Default.NotDefault default₂ x) (cong some (sym (‼ b≡))) obnd)
                              (proj₂ b)
                    (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        contradiction c' (nc₂₃ (sym xs≡₁) (proj₁ b))
                    (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                        contradiction d' (nc₂₄ (sym xs≡₁) (proj₁ b))
                    (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
                        contradiction e' (nc₂₅ (sym xs≡₁) (proj₁ b))
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                        contradiction f' (nc₂₆ (sym xs≡₁) (proj₁ b))
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
                      contradiction (¡ abcdefLen) λ ()
              ((singleton none refl) , (singleton (some a') refl)) → helperNoBexplicit mine theirs isSomeB (tt , tt)
              ((singleton (some a) refl) , (singleton none refl)) → helperNoBexplicit mine theirs isSomeB (tt , tt)
              ((singleton (some a) refl) , (singleton (some a') refl)) →
                let
                  @0 xs≡₁ : bs₁' ++ bs₂' ++ bs₃₄₅₆' ++ suffix ≡ bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                  xs≡₁ = (begin
                              bs₁' ++ bs₂' ++ bs₃₄₅₆' ++ suffix
                             ≡⟨ solve (++-monoid UInt8) ⟩
                              (bs₁' ++ bs₂' ++ bs₃₄₅₆') ++ suffix
                             ≡⟨ trans ps≡ (sym ps≡₁) ⟩
                              (bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                             ≡⟨ solve (++-monoid UInt8) ⟩
                              bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                              ∎ )

                  @0 bs₁≡ : bs₁' ≡ bs₁
                  bs₁≡ = ns₁ xs≡₁ a' a

                  @0 xs≡₂ : bs₂' ++ bs₃₄₅₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                  xs≡₂ = ++-cancelˡ bs₁'
                             (begin
                              bs₁' ++ bs₂' ++ bs₃₄₅₆' ++ suffix
                             ≡⟨ xs≡₁ ⟩
                              bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                             ≡⟨ cong (_++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₁≡) ⟩
                              bs₁' ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                              ∎ )
                in
                case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                  ret (const _) of λ where
                    (singleton (some b') refl , singleton ob' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                      let                                           
                        @0 bs₂≡ : bs₂' ≡ bs₂
                        bs₂≡ = ns₂ xs≡₂ b' (proj₁  b)
                      in
                      case (‼ bs₂≡) ret (const _) of λ where
                        refl →
                          let @0 b≡ : proj₁ b ≡ b'
                              b≡ = ub (proj₁ b) b'
                          in
                          contradiction
                            (subst₀ (λ x → Default.NotDefault default₂ x) (cong some (sym (‼ b≡))) obnd)
                            (proj₂ b)
                    (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        let
                          @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                          bs≡ = (begin
                            bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                            ≡⟨ sym xs≡₂ ⟩
                            bs₂' ++ bs₃₄₅₆' ++ suffix
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
                            bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ∎ )
                        in
                        contradiction c' (nc₂₃ bs≡ (proj₁ b))
                    (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                        let
                          @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                          bs≡ = (begin
                            bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                            ≡⟨ sym xs≡₂ ⟩
                            bs₂' ++ bs₃₄₅₆' ++ suffix
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
                            bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ≡⟨ ++-identityˡ (bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
                            bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ∎ )
                        in
                        contradiction d' (nc₂₄ bs≡ (proj₁ b))
                    (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
                        let
                          @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₅' ++ bs₆' ++ suffix
                          bs≡ = (begin
                            bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                            ≡⟨ sym xs≡₂ ⟩
                            bs₂' ++ bs₃₄₅₆' ++ suffix
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
                            bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ≡⟨ ++-identityˡ (bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
                            bs₅' ++ bs₆' ++ suffix
                            ∎ )
                        in
                        contradiction e' (nc₂₅ bs≡ (proj₁ b))
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                        let
                           @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₆' ++ suffix
                           bs≡ = (begin
                            bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                            ≡⟨ sym xs≡₂ ⟩
                            bs₂' ++ bs₃₄₅₆' ++ suffix
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
                            bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ≡⟨ ++-identityˡ (bs₆' ++ suffix)  ⟩
                            bs₆' ++ suffix
                            ∎ )
                        in
                        contradiction f' (nc₂₆ bs≡ (proj₁ b))
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
                      contradiction (¡ abcdefLen) (λ ())
        (yes pb , no ¬pc , e , f) → return ∘ no $ λ where
          theirs@(success prefix read read≡
            (mk×ₚ
              (mk&ₚ {bs₁ = bs₁'} {bs₂ = bs₂₃₄₅₆'} oa'
              (mk&ₚ {bs₁ = bs₂'} {bs₂ = bs₃₄₅₆'} (mkDefault ob' obnd)
              (mk&ₚ {bs₁ = bs₃'} {bs₂ = bs₄₅₆'} (mkDefault oc' ocnd)
              (mk&ₚ {bs₁ = bs₄'} {bs₂ = bs₅₆'} od'
              (mk&ₚ {bs₁ = bs₅'} {bs₂ = bs₆'} (mkDefault oe' oend)
                     (mkDefault of' ofnd) refl) refl) refl) refl) refl) abcdefLen)
            suffix ps≡) →
            let
                c : Σ (C bs₃) (λ c → ¬ Default.NotDefault default₃ (some c))
                c = case (Singleton oc ∋ singleton oc refl) ret (const _) of λ where
                  (singleton none refl) → contradiction tt ¬pc
                  (singleton (some x) refl) → (x , ¬pc)

                isSomeC : T (isSome oc)
                isSomeC = case (Singleton oc ∋ singleton oc refl) ret (const _) of λ where
                  (singleton none refl) → contradiction tt ¬pc
                  (singleton (some x) refl) → tt
            in
            case ((singleton oa refl) ,′e (singleton oa' refl)) ret (const _) of λ where
              ((singleton none refl) , (singleton none refl)) →
                let @0 xs≡₀ : (bs₂' ++ bs₃₄₅₆') ++ suffix ≡ (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                    xs≡₀ = trans ps≡ (sym ps≡₁)

                    @0 xs≡₁ : bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                    xs≡₁ = (begin
                            bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
                            ≡⟨ xs≡₀ ⟩
                            (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                            ∎ )                         
                in
                case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                  ret (const _) of λ where
                    (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                      case (singleton ob refl) of λ where
                          (singleton none refl) → contradiction (proj₁ c) (nc₂₃ xs≡₁ b')
                          (singleton (some b) refl) →
                            let
                              @0 bs₂≡ : bs₂' ≡ bs₂
                              bs₂≡ = ns₂ xs≡₁ b' b

                              @0 xs≡₂ : bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                              xs≡₂ = ++-cancelˡ bs₂'
                               (begin
                               bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                               ≡⟨ xs≡₁ ⟩
                               bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                               ≡⟨ cong (_++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₂≡) ⟩
                               bs₂' ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                               ∎ )
                            in
                            case ((singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                              ret (const _) of λ where
                                (singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                                  let
                                    @0 bs₃≡ : bs₃' ≡ bs₃
                                    bs₃≡ =
                                      ns₃
                                      (begin
                                      bs₃' ++ (bs₄₅₆' ++ suffix)
                                      ≡⟨ solve (++-monoid UInt8) ⟩
                                      bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                      ≡⟨ xs≡₂ ⟩
                                      bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                      ≡⟨ solve (++-monoid UInt8)  ⟩
                                      bs₃ ++ ((bs₄ ++ bs₅ ++ bs₆) ++ suf₁)
                                      ∎ )
                                      c' (proj₁  c)
                                  in
                                  case (‼ bs₃≡) ret (const _) of λ where
                                    refl →
                                      let @0 c≡ : proj₁ c ≡ c'
                                          c≡ = uc (proj₁ c) c'
                                      in
                                      contradiction
                                        (subst₀ (λ x → Default.NotDefault default₃ x) (cong some (sym (‼ c≡))) ocnd)
                                        (proj₂ c)
                                (singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → contradiction d' (nc₃₄ (sym xs≡₂) (proj₁ c))
                                (singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → contradiction e' (nc₃₅ (sym xs≡₂) (proj₁ c))
                                (singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → contradiction f' (nc₃₆ (sym xs≡₂) (proj₁ c))
                                (singleton none refl , singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                    (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            let
                              @0 bs₃≡ : bs₃' ≡ bs₃
                              bs₃≡ =
                                ns₃
                                (begin
                                  bs₃' ++ (bs₄₅₆' ++ suffix)
                                 ≡⟨ sym (++-assoc bs₃' _ _) ⟩
                                  (bs₃' ++ bs₄₅₆') ++ suffix
                                 ≡⟨ xs≡₀ ⟩
                                  (bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                                 ≡⟨ ++-assoc bs₃ (bs₄ ++ bs₅ ++ bs₆) suf₁  ⟩
                                   bs₃ ++ ((bs₄ ++ bs₅ ++ bs₆) ++ suf₁)
                                 ∎ )
                                c' (proj₁  c)
                            in
                            case (‼ bs₃≡) ret (const _) of λ where
                              refl →
                                let @0 c≡ : proj₁ c ≡ c'
                                    c≡ = uc (proj₁ c) c'
                                in
                                contradiction
                                  (subst₀ (λ x → Default.NotDefault default₃ x) (cong some (sym (‼ c≡))) ocnd)
                                  (proj₂ c)
                          (singleton (some b) refl) → contradiction c' (nc₂₃ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →  contradiction d' (nc₃₄ (sym xs≡₁) (proj₁ c))
                          (singleton (some b) refl) →  contradiction d' (nc₂₄ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →  contradiction e' (nc₃₅ (sym xs≡₁) (proj₁ c))
                          (singleton (some b) refl) →  contradiction e' (nc₂₅ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →  contradiction f' (nc₃₆ (sym xs≡₁) (proj₁ c))
                          (singleton (some b) refl) →  contradiction f' (nc₂₆ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
                      contradiction (¡ abcdefLen) (λ ())
              ((singleton none refl) , (singleton (some a') refl)) → helperNoCexplicit mine theirs isSomeC (tt , tt)
              ((singleton (some a) refl) , (singleton none refl)) → helperNoCexplicit mine theirs isSomeC (tt , tt)
              ((singleton (some a) refl) , (singleton (some a') refl)) →
                let
                  @0 xs≡₁ : bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                  xs≡₁ = (begin
                              bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                             ≡⟨ solve (++-monoid UInt8) ⟩
                              (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
                             ≡⟨ trans ps≡ (sym ps≡₁) ⟩
                              (bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                             ≡⟨ solve (++-monoid UInt8) ⟩
                              bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                              ∎ )

                  @0 bs₁≡ : bs₁' ≡ bs₁
                  bs₁≡ = ns₁ xs≡₁ a' a

                  @0 xs≡₂ : bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                  xs≡₂ = ++-cancelˡ bs₁'
                             (begin
                              bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                             ≡⟨ xs≡₁ ⟩
                              bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                             ≡⟨ cong (_++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₁≡) ⟩
                              bs₁' ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                              ∎ )
                in
                case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                  ret (const _) of λ where
                    (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                      case (singleton ob refl) of λ where
                          (singleton none refl) → contradiction (proj₁ c) (nc₂₃ xs≡₂ b')
                          (singleton (some b) refl) →
                            let
                              @0 bs₂≡ : bs₂' ≡ bs₂
                              bs₂≡ = ns₂ xs≡₂ b' b

                              @0 xs≡₃ : bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                              xs≡₃ = ++-cancelˡ bs₂'
                               (begin
                               bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                               ≡⟨ xs≡₂ ⟩
                               bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                               ≡⟨ cong (_++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₂≡) ⟩
                               bs₂' ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                               ∎ )
                            in
                            case ((singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                              ret (const _) of λ where
                                (singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                                  let
                                    @0 bs₃≡ : bs₃' ≡ bs₃
                                    bs₃≡ =
                                      ns₃
                                      (begin
                                      bs₃' ++ (bs₄₅₆' ++ suffix)
                                      ≡⟨ solve (++-monoid UInt8) ⟩
                                      bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                      ≡⟨ xs≡₃ ⟩
                                      bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                      ≡⟨ solve (++-monoid UInt8)  ⟩
                                      bs₃ ++ ((bs₄ ++ bs₅ ++ bs₆) ++ suf₁)
                                      ∎ )
                                      c' (proj₁  c)
                                  in
                                  case (‼ bs₃≡) ret (const _) of λ where
                                    refl →
                                      let @0 c≡ : proj₁ c ≡ c'
                                          c≡ = uc (proj₁ c) c'
                                      in
                                      contradiction
                                        (subst₀ (λ x → Default.NotDefault default₃ x) (cong some (sym (‼ c≡))) ocnd)
                                        (proj₂ c)
                                (singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → contradiction d' (nc₃₄ (sym xs≡₃) (proj₁ c))
                                (singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → contradiction e' (nc₃₅ (sym xs≡₃) (proj₁ c))
                                (singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → contradiction f' (nc₃₆ (sym xs≡₃) (proj₁ c))
                                (singleton none refl , singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                    (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                      case (singleton ob refl) of λ where
                          (singleton none refl) →
                            let
                              @0 bs₃≡ : bs₃' ≡ bs₃
                              bs₃≡ = 
                                ns₃
                                (begin
                                   bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                 ≡⟨ xs≡₂ ⟩
                                   bs₃ ++ bs₄ ++ bs₅ ++ bs₆  ++ suf₁
                                 ≡⟨ solve (++-monoid UInt8) ⟩
                                   bs₃ ++ ((bs₄ ++ bs₅ ++ bs₆) ++ suf₁)
                                 ∎ )
                                c' (proj₁  c)
                            in
                            case (‼ bs₃≡) ret (const _) of λ where
                              refl →
                                let @0 c≡ : proj₁ c ≡ c'
                                    c≡ = uc (proj₁ c) c'
                                in
                                contradiction
                                  (subst₀ (λ x → Default.NotDefault default₃ x) (cong some (sym (‼ c≡))) ocnd)
                                  (proj₂ c)
                          (singleton (some b) refl) → contradiction c' (nc₂₃ (sym xs≡₂) b)
                    (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                      case (singleton ob refl) of λ where
                          (singleton none refl) →  contradiction d' (nc₃₄ (sym xs≡₂) (proj₁ c))
                          (singleton (some b) refl) →  contradiction d' (nc₂₄ (sym xs≡₂) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
                      case (singleton ob refl) of λ where
                          (singleton none refl) →  contradiction e' (nc₃₅ (sym xs≡₂) (proj₁ c))
                          (singleton (some b) refl) →  contradiction e' (nc₂₅ (sym xs≡₂) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                      case (singleton ob refl) of λ where
                          (singleton none refl) →  contradiction f' (nc₃₆ (sym xs≡₂) (proj₁ c))
                          (singleton (some b) refl) →  contradiction f' (nc₂₆ (sym xs≡₂) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
                      contradiction (¡ abcdefLen) (λ ())
        (yes pb , yes pc , no ¬pe , f) → return ∘ no $ λ where
          theirs@(success prefix read read≡
            (mk×ₚ
              (mk&ₚ {bs₁ = bs₁'} {bs₂ = bs₂₃₄₅₆'} oa'
              (mk&ₚ {bs₁ = bs₂'} {bs₂ = bs₃₄₅₆'} (mkDefault ob' obnd)
              (mk&ₚ {bs₁ = bs₃'} {bs₂ = bs₄₅₆'} (mkDefault oc' ocnd)
              (mk&ₚ {bs₁ = bs₄'} {bs₂ = bs₅₆'} od'
              (mk&ₚ {bs₁ = bs₅'} {bs₂ = bs₆'} (mkDefault oe' oend)
                     (mkDefault of' ofnd) refl) refl) refl) refl) refl) abcdefLen)
            suffix ps≡) →
            let
                e : Σ (E bs₅) (λ e → ¬ Default.NotDefault default₅ (some e))
                e = case (Singleton oe ∋ singleton oe refl) ret (const _) of λ where
                  (singleton none refl) → contradiction tt ¬pe
                  (singleton (some x) refl) → (x , ¬pe)

                isSomeE : T (isSome oe)
                isSomeE = case (Singleton oe ∋ singleton oe refl) ret (const _) of λ where
                  (singleton none refl) → contradiction tt ¬pe
                  (singleton (some x) refl) → tt
            in
            case ((singleton oa refl) ,′e (singleton oa' refl)) ret (const _) of λ where
              ((singleton none refl) , (singleton none refl)) →
                let @0 xs≡₀ : (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix ≡ (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                    xs≡₀ = trans ps≡ (sym ps≡₁)

                    @0 xs≡₁ : bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                    xs≡₁ = (begin
                            bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
                            ≡⟨ xs≡₀ ⟩
                            (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                            ∎ ) 
                in
                case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                  ret (const _) of λ where
                    (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) → contradiction (proj₁ e) (nc₂₅ xs≡₁ b')
                                  (singleton (some d) refl) →  contradiction d (nc₂₄ xs≡₁ b')
                              (singleton (some c) refl) →  contradiction c (nc₂₃ xs≡₁ b')
                          (singleton (some b) refl) →
                                let
                                  @0 bs₂≡ : bs₂' ≡ bs₂
                                  bs₂≡ = ns₂ xs≡₁ b' b

                                  @0 xs≡₃ : bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                  xs≡₃ = ++-cancelˡ bs₂'
                                           (begin
                                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                           ≡⟨ xs≡₁ ⟩
                                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ≡⟨ cong (_++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₂≡) ⟩
                                           bs₂' ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ∎ )
                                in
                                case ((singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) of λ where
                                  (singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) → contradiction (proj₁ e) (nc₃₅ xs≡₃ c')
                                          (singleton (some d) refl) → contradiction d (nc₃₄ xs≡₃ c')
                                      (singleton (some c) refl) →
                                        let
                                          @0 bs₃≡ : bs₃' ≡ bs₃
                                          bs₃≡ = ns₃ xs≡₃ c' c

                                          @0 xs≡₄ : bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                          xs≡₄ = ++-cancelˡ bs₃'
                                            (begin
                                            bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                            ≡⟨ xs≡₃ ⟩
                                            bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                            ≡⟨ cong (_++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₃≡) ⟩
                                            bs₃' ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                            ∎ )
                                        in
                                        case ((singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                                        ret (const _) of λ where
                                          (singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) → contradiction (proj₁ e) (nc₄₅ xs≡₄ d')
                                              (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₄ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₄ ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    let
                                                    @0 bs₅≡ : bs₅' ≡ bs₅
                                                    bs₅≡ =
                                                      ns₅
                                                      (begin
                                                      bs₅' ++ (bs₆' ++ suffix)
                                                      ≡⟨ solve (++-monoid UInt8) ⟩
                                                      bs₅' ++ bs₆' ++ suffix
                                                      ≡⟨ xs≡₅ ⟩
                                                      bs₅ ++ bs₆ ++ suf₁
                                                      ≡⟨ solve (++-monoid UInt8)  ⟩
                                                      bs₅ ++ (bs₆ ++ suf₁)
                                                      ∎ )
                                                      e' (proj₁  e)
                                                    in
                                                    case (‼ bs₅≡) ret (const _) of λ where
                                                      refl →
                                                        let @0 e≡ : proj₁ e ≡ e'
                                                            e≡ = ue (proj₁ e) e'
                                                        in
                                                        contradiction
                                                        (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                                        (proj₂ e)
                                                  (singleton none refl , singleton (some f') refl) → contradiction f' (nc₅₆ (sym xs≡₅) (proj₁ e))
                                                  (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                          (singleton none refl , singleton (some e') refl , singleton of' refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) →
                                                 let
                                                    @0 bs₅≡ : bs₅' ≡ bs₅
                                                    bs₅≡ =
                                                      ns₅
                                                      (begin
                                                      bs₅' ++ (bs₆' ++ suffix)
                                                      ≡⟨ solve (++-monoid UInt8) ⟩
                                                      bs₅' ++ bs₆' ++ suffix
                                                      ≡⟨ xs≡₄ ⟩
                                                      bs₅ ++ bs₆ ++ suf₁
                                                      ≡⟨ solve (++-monoid UInt8)  ⟩
                                                      bs₅ ++ (bs₆ ++ suf₁)
                                                      ∎ )
                                                      e' (proj₁  e)
                                                    in
                                                    case (‼ bs₅≡) ret (const _) of λ where
                                                      refl →
                                                        let @0 e≡ : proj₁ e ≡ e'
                                                            e≡ = ue (proj₁ e) e'
                                                        in
                                                        contradiction
                                                        (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                                        (proj₂ e)
                                              (singleton (some d) refl) → contradiction e' (nc₄₅ (sym xs≡₄) d)
                                          (singleton none refl , singleton none refl , singleton (some f') refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) → contradiction f' (nc₅₆ (sym xs≡₄) (proj₁ e))
                                              (singleton (some d) refl) → contradiction f' (nc₄₆ (sym xs≡₄) d)
                                          (singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                  (singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) → contradiction (proj₁ e) (nc₄₅ xs≡₃ d')
                                          (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₃ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₃ ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    let
                                                    @0 bs₅≡ : bs₅' ≡ bs₅
                                                    bs₅≡ =
                                                      ns₅
                                                      (begin
                                                      bs₅' ++ (bs₆' ++ suffix)
                                                      ≡⟨ solve (++-monoid UInt8) ⟩
                                                      bs₅' ++ bs₆' ++ suffix
                                                      ≡⟨ xs≡₅ ⟩
                                                      bs₅ ++ bs₆ ++ suf₁
                                                      ≡⟨ solve (++-monoid UInt8)  ⟩
                                                      bs₅ ++ (bs₆ ++ suf₁)
                                                      ∎ )
                                                      e' (proj₁  e)
                                                    in
                                                    case (‼ bs₅≡) ret (const _) of λ where
                                                      refl →
                                                        let @0 e≡ : proj₁ e ≡ e'
                                                            e≡ = ue (proj₁ e) e'
                                                        in
                                                        contradiction
                                                        (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                                        (proj₂ e)
                                                  (singleton none refl , singleton (some f') refl) → contradiction f' (nc₅₆ (sym xs≡₅) (proj₁ e))
                                                  (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                      (singleton (some c) refl) → contradiction d' (nc₃₄ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) →
                                            let
                                              @0 bs₅≡ : bs₅' ≡ bs₅
                                              bs₅≡ =
                                                ns₅
                                                (begin
                                                bs₅' ++ (bs₆' ++ suffix)
                                                ≡⟨ solve (++-monoid UInt8) ⟩
                                                bs₅' ++ bs₆' ++ suffix
                                                ≡⟨ xs≡₃ ⟩
                                                bs₅ ++ bs₆ ++ suf₁
                                                ≡⟨ solve (++-monoid UInt8)  ⟩
                                                bs₅ ++ (bs₆ ++ suf₁)
                                                ∎ )
                                                e' (proj₁  e)
                                            in
                                            case (‼ bs₅≡) ret (const _) of λ where
                                            refl →
                                              let @0 e≡ : proj₁ e ≡ e'
                                                  e≡ = ue (proj₁ e) e'
                                              in
                                              contradiction
                                              (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                              (proj₂ e)
                                          (singleton (some d) refl) → contradiction e' (nc₄₅ (sym xs≡₃) d)
                                      (singleton (some c) refl) → contradiction e' (nc₃₅ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) → contradiction f' (nc₅₆ (sym xs≡₃) (proj₁ e))
                                          (singleton (some d) refl) →  contradiction f' (nc₄₆ (sym xs≡₃) d)
                                      (singleton (some c) refl) →  contradiction f' (nc₃₆ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                    (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) → contradiction (proj₁ e) (nc₃₅ xs≡₁ c')
                                  (singleton (some d) refl) →  contradiction d (nc₃₄ xs≡₁ c')
                              (singleton (some c) refl) →
                                let
                                  @0 bs₃≡ : bs₃' ≡ bs₃
                                  bs₃≡ = ns₃ xs≡₁ c' c

                                  @0 xs≡₃ : bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                  xs≡₃ = ++-cancelˡ bs₃'
                                           (begin
                                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                           ≡⟨ xs≡₁ ⟩
                                           bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ≡⟨ cong (_++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₃≡) ⟩
                                           bs₃' ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ∎ )
                                in
                                case ((singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) of λ where
                                  (singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                    case (singleton od refl) of λ where
                                      (singleton none refl) → contradiction (proj₁ e) (nc₄₅ xs≡₃ d')
                                      (singleton (some d) refl) →
                                        let
                                          @0 bs₄≡ : bs₄' ≡ bs₄
                                          bs₄≡ = ns₄ xs≡₃ d' d

                                          @0 xs≡₄ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                          xs≡₄ = ++-cancelˡ bs₄'
                                            (begin
                                            bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                            ≡⟨ xs≡₃ ⟩
                                            bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                            ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                            bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                            ∎ )
                                        in
                                        case ((singleton oe' refl) ,′e (singleton of' refl)) 
                                        ret (const _) of λ where
                                          (singleton (some e') refl , singleton of' refl) →
                                            let
                                            @0 bs₅≡ : bs₅' ≡ bs₅
                                            bs₅≡ =
                                              ns₅
                                              (begin
                                              bs₅' ++ (bs₆' ++ suffix)
                                              ≡⟨ solve (++-monoid UInt8) ⟩
                                              bs₅' ++ bs₆' ++ suffix
                                              ≡⟨ xs≡₄ ⟩
                                              bs₅ ++ bs₆ ++ suf₁
                                              ≡⟨ solve (++-monoid UInt8)  ⟩
                                              bs₅ ++ (bs₆ ++ suf₁)
                                              ∎ )
                                              e' (proj₁  e)
                                            in
                                            case (‼ bs₅≡) ret (const _) of λ where
                                              refl →
                                                let @0 e≡ : proj₁ e ≡ e'
                                                    e≡ = ue (proj₁ e) e'
                                                in
                                                contradiction
                                                (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                                (proj₂ e)
                                          (singleton none refl , singleton (some f') refl) → contradiction f' (nc₅₆ (sym xs≡₄) (proj₁ e))
                                          (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                  (singleton none refl , singleton (some e') refl , singleton of' refl) →
                                    case (singleton od refl) of λ where
                                      (singleton none refl) →
                                        let
                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                          bs₅≡ =
                                            ns₅
                                            (begin
                                            bs₅' ++ (bs₆' ++ suffix)
                                            ≡⟨ solve (++-monoid UInt8) ⟩
                                            bs₅' ++ bs₆' ++ suffix
                                            ≡⟨ xs≡₃ ⟩
                                            bs₅ ++ bs₆ ++ suf₁
                                            ≡⟨ solve (++-monoid UInt8)  ⟩
                                            bs₅ ++ (bs₆ ++ suf₁)
                                            ∎ )
                                            e' (proj₁  e)
                                        in
                                        case (‼ bs₅≡) ret (const _) of λ where
                                          refl →
                                            let @0 e≡ : proj₁ e ≡ e'
                                                e≡ = ue (proj₁ e) e'
                                            in
                                            contradiction
                                            (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                            (proj₂ e)
                                      (singleton (some d) refl) → contradiction e' (nc₄₅ (sym xs≡₃) d)
                                  (singleton none refl , singleton none refl , singleton (some f') refl) →
                                    case (singleton od refl) of λ where
                                      (singleton none refl) → contradiction f' (nc₅₆ (sym xs≡₃) (proj₁ e))
                                      (singleton (some d) refl) → contradiction f' (nc₄₆ (sym xs≡₃) d)
                                  (singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                          (singleton (some b) refl) → contradiction c' (nc₂₃ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) → contradiction (proj₁ e) (nc₄₅ xs≡₁ d')
                                  (singleton (some d) refl) →
                                    let
                                    @0 bs₄≡ : bs₄' ≡ bs₄
                                    bs₄≡ = ns₄ xs≡₁ d' d

                                    @0 xs≡₂ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                    xs≡₂ = ++-cancelˡ bs₄'
                                      (begin
                                      bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                      ≡⟨ xs≡₁ ⟩
                                      bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                      ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                      bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                      ∎ )
                                    in
                                    case ((singleton oe' refl) ,′e (singleton of' refl)) 
                                    ret (const _) of λ where
                                      (singleton (some e') refl , singleton of' refl) →
                                        let
                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                          bs₅≡ =
                                            ns₅
                                            (begin
                                            bs₅' ++ (bs₆' ++ suffix)
                                            ≡⟨ solve (++-monoid UInt8) ⟩
                                            bs₅' ++ bs₆' ++ suffix
                                            ≡⟨ xs≡₂ ⟩
                                            bs₅ ++ bs₆ ++ suf₁
                                            ≡⟨ solve (++-monoid UInt8)  ⟩
                                            bs₅ ++ (bs₆ ++ suf₁)
                                            ∎ )
                                            e' (proj₁  e)
                                        in
                                        case (‼ bs₅≡) ret (const _) of λ where
                                          refl →
                                            let @0 e≡ : proj₁ e ≡ e'
                                                e≡ = ue (proj₁ e) e'
                                            in
                                            contradiction
                                            (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                            (proj₂ e)
                                      (singleton none refl , singleton (some f') refl) → contradiction f' (nc₅₆ (sym xs≡₂) (proj₁ e))
                                      (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                              (singleton (some c) refl) →  contradiction d' (nc₃₄ (sym xs≡₁) c)
                          (singleton (some b) refl) →  contradiction d' (nc₂₄ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    let
                                      @0 bs₅≡ : bs₅' ≡ bs₅
                                      bs₅≡ =
                                        ns₅
                                        (begin
                                        bs₅' ++ (bs₆' ++ suffix)
                                        ≡⟨ sym (++-assoc bs₅' _ _) ⟩
                                        (bs₅' ++ bs₆') ++ suffix
                                        ≡⟨ xs≡₀ ⟩
                                        (bs₅ ++ bs₆) ++ suf₁
                                        ≡⟨ ++-assoc bs₅ bs₆ suf₁  ⟩
                                        bs₅ ++ (bs₆ ++ suf₁)
                                        ∎ )
                                        e' (proj₁  e)
                                    in
                                    case (‼ bs₅≡) ret (const _) of λ where
                                      refl →
                                        let @0 e≡ : proj₁ e ≡ e'
                                            e≡ = ue (proj₁ e) e'
                                        in
                                        contradiction
                                          (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                          (proj₂ e)
                                  (singleton (some d) refl) →  contradiction e' (nc₄₅ (sym xs≡₁) d)
                              (singleton (some c) refl) →  contradiction e' (nc₃₅ (sym xs≡₁) c)
                          (singleton (some b) refl) →  contradiction e' (nc₂₅ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) → contradiction f' (nc₅₆ (sym xs≡₁) (proj₁ e))
                                  (singleton (some d) refl) →  contradiction f' (nc₄₆ (sym xs≡₁) d)
                              (singleton (some c) refl) →  contradiction f' (nc₃₆ (sym xs≡₁) c)
                          (singleton (some b) refl) →  contradiction f' (nc₂₆ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
                      contradiction (¡ abcdefLen) (λ ())
              ((singleton none refl) , (singleton (some a') refl)) → helperNoEexplicit mine theirs isSomeE (tt , tt)
              ((singleton (some a) refl) , (singleton none refl)) → helperNoEexplicit mine theirs isSomeE (tt , tt)
              ((singleton (some a) refl) , (singleton (some a') refl)) →
                let
                  @0 xs≡₁ : bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                  xs≡₁ = (begin
                              bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                             ≡⟨ solve (++-monoid UInt8) ⟩
                              (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
                             ≡⟨ trans ps≡ (sym ps≡₁) ⟩
                              (bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                             ≡⟨ solve (++-monoid UInt8) ⟩
                              bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                              ∎ )

                  @0 bs₁≡ : bs₁' ≡ bs₁
                  bs₁≡ = ns₁ xs≡₁ a' a

                  @0 xs≡₂ : bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                  xs≡₂ = ++-cancelˡ bs₁'
                             (begin
                              bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                             ≡⟨ xs≡₁ ⟩
                              bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                             ≡⟨ cong (_++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₁≡) ⟩
                              bs₁' ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                              ∎ )
                in
                case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                  ret (const _) of λ where
                    (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) → contradiction (proj₁ e) (nc₂₅ xs≡₂ b')
                                  (singleton (some d) refl) →  contradiction d (nc₂₄ xs≡₂ b')
                              (singleton (some c) refl) →  contradiction c (nc₂₃ xs≡₂ b')
                          (singleton (some b) refl) →
                                let
                                  @0 bs₂≡ : bs₂' ≡ bs₂
                                  bs₂≡ = ns₂ xs≡₂ b' b

                                  @0 xs≡₃ : bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                  xs≡₃ = ++-cancelˡ bs₂'
                                           (begin
                                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                           ≡⟨ xs≡₂ ⟩
                                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ≡⟨ cong (_++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₂≡) ⟩
                                           bs₂' ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ∎ )
                                in
                                case ((singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) of λ where
                                  (singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) → contradiction (proj₁ e) (nc₃₅ xs≡₃ c')
                                          (singleton (some d) refl) → contradiction d (nc₃₄ xs≡₃ c')
                                      (singleton (some c) refl) →
                                        let
                                          @0 bs₃≡ : bs₃' ≡ bs₃
                                          bs₃≡ = ns₃ xs≡₃ c' c

                                          @0 xs≡₄ : bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                          xs≡₄ = ++-cancelˡ bs₃'
                                            (begin
                                            bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                            ≡⟨ xs≡₃ ⟩
                                            bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                            ≡⟨ cong (_++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₃≡) ⟩
                                            bs₃' ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                            ∎ )
                                        in
                                        case ((singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                                        ret (const _) of λ where
                                          (singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) → contradiction (proj₁ e) (nc₄₅ xs≡₄ d')
                                              (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₄ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₄ ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    let
                                                    @0 bs₅≡ : bs₅' ≡ bs₅
                                                    bs₅≡ =
                                                      ns₅
                                                      (begin
                                                      bs₅' ++ (bs₆' ++ suffix)
                                                      ≡⟨ solve (++-monoid UInt8) ⟩
                                                      bs₅' ++ bs₆' ++ suffix
                                                      ≡⟨ xs≡₅ ⟩
                                                      bs₅ ++ bs₆ ++ suf₁
                                                      ≡⟨ solve (++-monoid UInt8)  ⟩
                                                      bs₅ ++ (bs₆ ++ suf₁)
                                                      ∎ )
                                                      e' (proj₁  e)
                                                    in
                                                    case (‼ bs₅≡) ret (const _) of λ where
                                                      refl →
                                                        let @0 e≡ : proj₁ e ≡ e'
                                                            e≡ = ue (proj₁ e) e'
                                                        in
                                                        contradiction
                                                        (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                                        (proj₂ e)
                                                  (singleton none refl , singleton (some f') refl) → contradiction f' (nc₅₆ (sym xs≡₅) (proj₁ e))
                                                  (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                          (singleton none refl , singleton (some e') refl , singleton of' refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) →
                                                 let
                                                    @0 bs₅≡ : bs₅' ≡ bs₅
                                                    bs₅≡ =
                                                      ns₅
                                                      (begin
                                                      bs₅' ++ (bs₆' ++ suffix)
                                                      ≡⟨ solve (++-monoid UInt8) ⟩
                                                      bs₅' ++ bs₆' ++ suffix
                                                      ≡⟨ xs≡₄ ⟩
                                                      bs₅ ++ bs₆ ++ suf₁
                                                      ≡⟨ solve (++-monoid UInt8)  ⟩
                                                      bs₅ ++ (bs₆ ++ suf₁)
                                                      ∎ )
                                                      e' (proj₁  e)
                                                    in
                                                    case (‼ bs₅≡) ret (const _) of λ where
                                                      refl →
                                                        let @0 e≡ : proj₁ e ≡ e'
                                                            e≡ = ue (proj₁ e) e'
                                                        in
                                                        contradiction
                                                        (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                                        (proj₂ e)
                                              (singleton (some d) refl) → contradiction e' (nc₄₅ (sym xs≡₄) d)
                                          (singleton none refl , singleton none refl , singleton (some f') refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) → contradiction f' (nc₅₆ (sym xs≡₄) (proj₁ e))
                                              (singleton (some d) refl) → contradiction f' (nc₄₆ (sym xs≡₄) d)
                                          (singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                  (singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) → contradiction (proj₁ e) (nc₄₅ xs≡₃ d')
                                          (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₃ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₃ ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    let
                                                    @0 bs₅≡ : bs₅' ≡ bs₅
                                                    bs₅≡ =
                                                      ns₅
                                                      (begin
                                                      bs₅' ++ (bs₆' ++ suffix)
                                                      ≡⟨ solve (++-monoid UInt8) ⟩
                                                      bs₅' ++ bs₆' ++ suffix
                                                      ≡⟨ xs≡₅ ⟩
                                                      bs₅ ++ bs₆ ++ suf₁
                                                      ≡⟨ solve (++-monoid UInt8)  ⟩
                                                      bs₅ ++ (bs₆ ++ suf₁)
                                                      ∎ )
                                                      e' (proj₁  e)
                                                    in
                                                    case (‼ bs₅≡) ret (const _) of λ where
                                                      refl →
                                                        let @0 e≡ : proj₁ e ≡ e'
                                                            e≡ = ue (proj₁ e) e'
                                                        in
                                                        contradiction
                                                        (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                                        (proj₂ e)
                                                  (singleton none refl , singleton (some f') refl) → contradiction f' (nc₅₆ (sym xs≡₅) (proj₁ e))
                                                  (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                      (singleton (some c) refl) → contradiction d' (nc₃₄ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) →
                                            let
                                              @0 bs₅≡ : bs₅' ≡ bs₅
                                              bs₅≡ =
                                                ns₅
                                                (begin
                                                bs₅' ++ (bs₆' ++ suffix)
                                                ≡⟨ solve (++-monoid UInt8) ⟩
                                                bs₅' ++ bs₆' ++ suffix
                                                ≡⟨ xs≡₃ ⟩
                                                bs₅ ++ bs₆ ++ suf₁
                                                ≡⟨ solve (++-monoid UInt8)  ⟩
                                                bs₅ ++ (bs₆ ++ suf₁)
                                                ∎ )
                                                e' (proj₁  e)
                                            in
                                            case (‼ bs₅≡) ret (const _) of λ where
                                            refl →
                                              let @0 e≡ : proj₁ e ≡ e'
                                                  e≡ = ue (proj₁ e) e'
                                              in
                                              contradiction
                                              (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                              (proj₂ e)
                                          (singleton (some d) refl) → contradiction e' (nc₄₅ (sym xs≡₃) d)
                                      (singleton (some c) refl) → contradiction e' (nc₃₅ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) → contradiction f' (nc₅₆ (sym xs≡₃) (proj₁ e))
                                          (singleton (some d) refl) →  contradiction f' (nc₄₆ (sym xs≡₃) d)
                                      (singleton (some c) refl) →  contradiction f' (nc₃₆ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                    (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) → contradiction (proj₁ e) (nc₃₅ xs≡₂ c')
                                  (singleton (some d) refl) →  contradiction d (nc₃₄ xs≡₂ c')
                              (singleton (some c) refl) →
                                let
                                  @0 bs₃≡ : bs₃' ≡ bs₃
                                  bs₃≡ = ns₃ xs≡₂ c' c

                                  @0 xs≡₃ : bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                  xs≡₃ = ++-cancelˡ bs₃'
                                           (begin
                                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                           ≡⟨ xs≡₂ ⟩
                                           bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ≡⟨ cong (_++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₃≡) ⟩
                                           bs₃' ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ∎ )
                                in
                                case ((singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) of λ where
                                  (singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                    case (singleton od refl) of λ where
                                      (singleton none refl) → contradiction (proj₁ e) (nc₄₅ xs≡₃ d')
                                      (singleton (some d) refl) →
                                        let
                                          @0 bs₄≡ : bs₄' ≡ bs₄
                                          bs₄≡ = ns₄ xs≡₃ d' d

                                          @0 xs≡₄ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                          xs≡₄ = ++-cancelˡ bs₄'
                                            (begin
                                            bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                            ≡⟨ xs≡₃ ⟩
                                            bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                            ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                            bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                            ∎ )
                                        in
                                        case ((singleton oe' refl) ,′e (singleton of' refl)) 
                                        ret (const _) of λ where
                                          (singleton (some e') refl , singleton of' refl) →
                                            let
                                            @0 bs₅≡ : bs₅' ≡ bs₅
                                            bs₅≡ =
                                              ns₅
                                              (begin
                                              bs₅' ++ (bs₆' ++ suffix)
                                              ≡⟨ solve (++-monoid UInt8) ⟩
                                              bs₅' ++ bs₆' ++ suffix
                                              ≡⟨ xs≡₄ ⟩
                                              bs₅ ++ bs₆ ++ suf₁
                                              ≡⟨ solve (++-monoid UInt8)  ⟩
                                              bs₅ ++ (bs₆ ++ suf₁)
                                              ∎ )
                                              e' (proj₁  e)
                                            in
                                            case (‼ bs₅≡) ret (const _) of λ where
                                              refl →
                                                let @0 e≡ : proj₁ e ≡ e'
                                                    e≡ = ue (proj₁ e) e'
                                                in
                                                contradiction
                                                (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                                (proj₂ e)
                                          (singleton none refl , singleton (some f') refl) → contradiction f' (nc₅₆ (sym xs≡₄) (proj₁ e))
                                          (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                  (singleton none refl , singleton (some e') refl , singleton of' refl) →
                                    case (singleton od refl) of λ where
                                      (singleton none refl) →
                                        let
                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                          bs₅≡ =
                                            ns₅
                                            (begin
                                            bs₅' ++ (bs₆' ++ suffix)
                                            ≡⟨ solve (++-monoid UInt8) ⟩
                                            bs₅' ++ bs₆' ++ suffix
                                            ≡⟨ xs≡₃ ⟩
                                            bs₅ ++ bs₆ ++ suf₁
                                            ≡⟨ solve (++-monoid UInt8)  ⟩
                                            bs₅ ++ (bs₆ ++ suf₁)
                                            ∎ )
                                            e' (proj₁  e)
                                        in
                                        case (‼ bs₅≡) ret (const _) of λ where
                                          refl →
                                            let @0 e≡ : proj₁ e ≡ e'
                                                e≡ = ue (proj₁ e) e'
                                            in
                                            contradiction
                                            (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                            (proj₂ e)
                                      (singleton (some d) refl) → contradiction e' (nc₄₅ (sym xs≡₃) d)
                                  (singleton none refl , singleton none refl , singleton (some f') refl) →
                                    case (singleton od refl) of λ where
                                      (singleton none refl) → contradiction f' (nc₅₆ (sym xs≡₃) (proj₁ e))
                                      (singleton (some d) refl) → contradiction f' (nc₄₆ (sym xs≡₃) d)
                                  (singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                          (singleton (some b) refl) →  contradiction c' (nc₂₃ (sym xs≡₂) b)                          
                    (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) → contradiction (proj₁ e) (nc₄₅ xs≡₂ d')
                                  (singleton (some d) refl) →
                                    let
                                    @0 bs₄≡ : bs₄' ≡ bs₄
                                    bs₄≡ = ns₄ xs≡₂ d' d

                                    @0 xs≡₄ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                    xs≡₄ = ++-cancelˡ bs₄'
                                      (begin
                                      bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                      ≡⟨ xs≡₂ ⟩
                                      bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                      ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                      bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                      ∎ )
                                    in
                                    case ((singleton oe' refl) ,′e (singleton of' refl)) 
                                    ret (const _) of λ where
                                      (singleton (some e') refl , singleton of' refl) →
                                        let
                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                          bs₅≡ =
                                            ns₅
                                            (begin
                                            bs₅' ++ (bs₆' ++ suffix)
                                            ≡⟨ solve (++-monoid UInt8) ⟩
                                            bs₅' ++ bs₆' ++ suffix
                                            ≡⟨ xs≡₄ ⟩
                                            bs₅ ++ bs₆ ++ suf₁
                                            ≡⟨ solve (++-monoid UInt8)  ⟩
                                            bs₅ ++ (bs₆ ++ suf₁)
                                            ∎ )
                                            e' (proj₁  e)
                                        in
                                        case (‼ bs₅≡) ret (const _) of λ where
                                          refl →
                                            let @0 e≡ : proj₁ e ≡ e'
                                                e≡ = ue (proj₁ e) e'
                                            in
                                            contradiction
                                            (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                            (proj₂ e)
                                      (singleton none refl , singleton (some f') refl) → contradiction f' (nc₅₆ (sym xs≡₄) (proj₁ e))
                                      (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                              (singleton (some c) refl) →  contradiction d' (nc₃₄ (sym xs≡₂) c)
                          (singleton (some b) refl) →  contradiction d' (nc₂₄ (sym xs≡₂) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    let
                                      @0 bs₅≡ : bs₅' ≡ bs₅
                                      bs₅≡ = 
                                        ns₅
                                        (begin
                                        bs₅' ++ bs₆' ++ suffix
                                        ≡⟨ xs≡₂ ⟩
                                        bs₅ ++ bs₆  ++ suf₁
                                        ≡⟨ solve (++-monoid UInt8) ⟩
                                        bs₅ ++ (bs₆ ++ suf₁)
                                        ∎ )
                                        e' (proj₁  e)
                                    in
                                    case (‼ bs₅≡) ret (const _) of λ where
                                      refl →
                                        let @0 e≡ : proj₁ e ≡ e'
                                            e≡ = ue (proj₁ e) e'
                                        in
                                        contradiction
                                          (subst₀ (λ x → Default.NotDefault default₅ x) (cong some (sym (‼ e≡))) oend)
                                          (proj₂ e)
                                  (singleton (some d) refl) →  contradiction e' (nc₄₅ (sym xs≡₂) d)
                              (singleton (some c) refl) →  contradiction e' (nc₃₅ (sym xs≡₂) c)
                          (singleton (some b) refl) →  contradiction e' (nc₂₅ (sym xs≡₂) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) → contradiction f' (nc₅₆ (sym xs≡₂) (proj₁ e))
                                  (singleton (some d) refl) →  contradiction f' (nc₄₆ (sym xs≡₂) d)
                              (singleton (some c) refl) →  contradiction f' (nc₃₆ (sym xs≡₂) c)
                          (singleton (some b) refl) →  contradiction f' (nc₂₆ (sym xs≡₂) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
                      contradiction (¡ abcdefLen) (λ ())
        (yes pb , yes pc , yes pe , no ¬pf) → return ∘ no $ λ where
          theirs@(success prefix read read≡
            (mk×ₚ
              (mk&ₚ {bs₁ = bs₁'} {bs₂ = bs₂₃₄₅₆'} oa'
              (mk&ₚ {bs₁ = bs₂'} {bs₂ = bs₃₄₅₆'} (mkDefault ob' obnd)
              (mk&ₚ {bs₁ = bs₃'} {bs₂ = bs₄₅₆'} (mkDefault oc' ocnd)
              (mk&ₚ {bs₁ = bs₄'} {bs₂ = bs₅₆'} od'
              (mk&ₚ {bs₁ = bs₅'} {bs₂ = bs₆'} (mkDefault oe' oend)
                     (mkDefault of' ofnd) refl) refl) refl) refl) refl) abcdefLen)
            suffix ps≡) →
            let
                f : Σ (F bs₆) (λ f → ¬ Default.NotDefault default₆ (some f))
                f = case (Singleton of ∋ singleton of refl) ret (const _) of λ where
                  (singleton none refl) → contradiction tt ¬pf
                  (singleton (some x) refl) → (x , ¬pf)

                isSomeF : T (isSome of)
                isSomeF = case (Singleton of ∋ singleton of refl) ret (const _) of λ where
                  (singleton none refl) → contradiction tt ¬pf
                  (singleton (some x) refl) → tt
            in
            case ((singleton oa refl) ,′e (singleton oa' refl)) ret (const _) of λ where
              ((singleton none refl) , (singleton none refl)) →
                let @0 xs≡₀ : (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix ≡ (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                    xs≡₀ = trans ps≡ (sym ps≡₁)

                    @0 xs≡₁ : bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                    xs≡₁ = (begin
                            bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
                            ≡⟨ xs≡₀ ⟩
                            (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                            ≡⟨ solve (++-monoid UInt8) ⟩
                            bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                            ∎ ) 
                in
                case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                  ret (const _) of λ where
                    (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    case (singleton oe refl) of λ where
                                      (singleton none refl) → contradiction (proj₁ f) (nc₂₆ xs≡₁ b')
                                      (singleton (some e) refl) →  contradiction e (nc₂₅ xs≡₁ b')
                                  (singleton (some d) refl) →  contradiction d (nc₂₄ xs≡₁ b')
                              (singleton (some c) refl) →  contradiction c (nc₂₃ xs≡₁ b')
                          (singleton (some b) refl) →
                                let
                                  @0 bs₂≡ : bs₂' ≡ bs₂
                                  bs₂≡ = ns₂ xs≡₁ b' b

                                  @0 xs≡₃ : bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                  xs≡₃ = ++-cancelˡ bs₂'
                                           (begin
                                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                           ≡⟨ xs≡₁ ⟩
                                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ≡⟨ cong (_++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₂≡) ⟩
                                           bs₂' ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ∎ )
                                in
                                case ((singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) of λ where
                                  (singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) →
                                            case (singleton oe refl) of λ where
                                              (singleton none refl) → contradiction (proj₁ f) (nc₃₆ xs≡₃ c')
                                              (singleton (some e) refl) → contradiction e (nc₃₅ xs≡₃ c')
                                          (singleton (some d) refl) → contradiction d (nc₃₄ xs≡₃ c')
                                      (singleton (some c) refl) →
                                        let
                                          @0 bs₃≡ : bs₃' ≡ bs₃
                                          bs₃≡ = ns₃ xs≡₃ c' c

                                          @0 xs≡₄ : bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                          xs≡₄ = ++-cancelˡ bs₃'
                                            (begin
                                            bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                            ≡⟨ xs≡₃ ⟩
                                            bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                            ≡⟨ cong (_++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₃≡) ⟩
                                            bs₃' ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                            ∎ )
                                        in
                                        case ((singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                                        ret (const _) of λ where
                                          (singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) → 
                                                case (singleton oe refl) of λ where
                                                  (singleton none refl) → contradiction (proj₁ f) (nc₄₆ xs≡₄ d')
                                                  (singleton (some e) refl) → contradiction e (nc₄₅ xs≡₄ d')
                                              (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₄ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₄ ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₅ e')
                                                      (singleton (some e) refl) →
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₅ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₅ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton none refl , singleton (some f') refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) →
                                                        let
                                                          @0 bs₆≡ : bs₆' ≡ bs₆
                                                          bs₆≡ =
                                                            ns₆
                                                              (begin
                                                              bs₆' ++ suffix
                                                              ≡⟨ xs≡₅ ⟩
                                                              bs₆ ++ suf₁
                                                              ∎ )
                                                              f' (proj₁  f)
                                                        in
                                                        case (‼ bs₆≡) ret (const _) of λ where
                                                          refl →
                                                            let @0 f≡ : proj₁ f ≡ f'
                                                                f≡ = uf (proj₁ f) f'
                                                            in
                                                            contradiction
                                                              (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                              (proj₂ f)
                                                      (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₅) e)
                                                  (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                          (singleton none refl , singleton (some e') refl , singleton of' refl) →
                                                case (singleton od refl) of λ where
                                                  (singleton none refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₄ e')
                                                      (singleton (some e) refl) → 
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₄ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₄ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton (some d) refl) →  contradiction e' (nc₄₅ (sym xs≡₄) d)
                                          (singleton none refl , singleton none refl , singleton (some f') refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) →
                                                case (singleton oe refl) of λ where
                                                  (singleton none refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₄ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₄) e)
                                              (singleton (some d) refl) → contradiction f' (nc₄₆ (sym xs≡₄) d)
                                          (singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                  (singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) →
                                            case (singleton oe refl) of λ where
                                              (singleton none refl) → contradiction (proj₁ f) (nc₄₆ xs≡₃ d')
                                              (singleton (some e) refl) → contradiction e (nc₄₅ xs≡₃ d')
                                          (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₃ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₃ ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₅ e')
                                                      (singleton (some e) refl) → 
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₅ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₅ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton none refl , singleton (some f') refl) →
                                                            case (singleton oe refl) of λ where
                                                              (singleton none refl) →
                                                                let
                                                                  @0 bs₆≡ : bs₆' ≡ bs₆
                                                                  bs₆≡ =
                                                                    ns₆
                                                                    (begin
                                                                    bs₆' ++ suffix
                                                                    ≡⟨ xs≡₅ ⟩
                                                                    bs₆ ++ suf₁
                                                                    ∎ )
                                                                    f' (proj₁  f)
                                                                in
                                                                case (‼ bs₆≡) ret (const _) of λ where
                                                                  refl →
                                                                    let @0 f≡ : proj₁ f ≡ f'
                                                                        f≡ = uf (proj₁ f) f'
                                                                    in
                                                                    contradiction
                                                                      (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                      (proj₂ f)
                                                              (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₅) e)
                                                  (singleton none refl , singleton none refl) →  contradiction (¡ abcdefLen) (λ ())
                                      (singleton (some c) refl) → contradiction d' (nc₃₄ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) →
                                            case (singleton oe refl) of λ where
                                              (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₃ e')
                                              (singleton (some e) refl) → 
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₃ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₃ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                          (singleton (some d) refl) →  contradiction e' (nc₄₅ (sym xs≡₃) d)
                                      (singleton (some c) refl) →  contradiction e' (nc₃₅ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) →
                                            case (singleton oe refl) of λ where
                                              (singleton none refl) →
                                                let
                                                  @0 bs₆≡ : bs₆' ≡ bs₆
                                                  bs₆≡ =
                                                    ns₆
                                                    (begin
                                                    bs₆' ++ suffix
                                                    ≡⟨ xs≡₃ ⟩
                                                    bs₆ ++ suf₁
                                                    ∎ )
                                                    f' (proj₁  f)
                                                in
                                                case (‼ bs₆≡) ret (const _) of λ where
                                                  refl →
                                                    let @0 f≡ : proj₁ f ≡ f'
                                                        f≡ = uf (proj₁ f) f'
                                                    in
                                                    contradiction
                                                      (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                      (proj₂ f)
                                              (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₃) e)
                                          (singleton (some d) refl) →  contradiction f' (nc₄₆ (sym xs≡₃) d)
                                      (singleton (some c) refl) →  contradiction f' (nc₃₆ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                    (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    case (singleton oe refl) of λ where
                                      (singleton none refl) → contradiction (proj₁ f) (nc₃₆ xs≡₁ c')
                                      (singleton (some e) refl) →  contradiction e (nc₃₅ xs≡₁ c')
                                  (singleton (some d) refl) →  contradiction d (nc₃₄ xs≡₁ c')
                              (singleton (some c) refl) →
                                let
                                  @0 bs₃≡ : bs₃' ≡ bs₃
                                  bs₃≡ = ns₃ xs≡₁ c' c

                                  @0 xs≡₃ : bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                  xs≡₃ = ++-cancelˡ bs₃'
                                           (begin
                                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                           ≡⟨ xs≡₁ ⟩
                                           bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ≡⟨ cong (_++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₃≡) ⟩
                                           bs₃' ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ∎ )
                                in
                                   case ((singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                                     ret (const _) of λ where
                                          (singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) → 
                                                case (singleton oe refl) of λ where
                                                  (singleton none refl) → contradiction (proj₁ f) (nc₄₆ xs≡₃ d')
                                                  (singleton (some e) refl) → contradiction e (nc₄₅ xs≡₃ d')
                                              (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₃ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₃ ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₅ e')
                                                      (singleton (some e) refl) →
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₅ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₅ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton none refl , singleton (some f') refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) →
                                                        let
                                                          @0 bs₆≡ : bs₆' ≡ bs₆
                                                          bs₆≡ =
                                                            ns₆
                                                              (begin
                                                              bs₆' ++ suffix
                                                              ≡⟨ xs≡₅ ⟩
                                                              bs₆ ++ suf₁
                                                              ∎ )
                                                              f' (proj₁  f)
                                                        in
                                                        case (‼ bs₆≡) ret (const _) of λ where
                                                          refl →
                                                            let @0 f≡ : proj₁ f ≡ f'
                                                                f≡ = uf (proj₁ f) f'
                                                            in
                                                            contradiction
                                                              (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                              (proj₂ f)
                                                      (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₅) e)
                                                  (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                          (singleton none refl , singleton (some e') refl , singleton of' refl) →
                                                case (singleton od refl) of λ where
                                                  (singleton none refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₃ e')
                                                      (singleton (some e) refl) → 
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₃ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₃ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton (some d) refl) →  contradiction e' (nc₄₅ (sym xs≡₃) d)
                                          (singleton none refl , singleton none refl , singleton (some f') refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) →
                                                case (singleton oe refl) of λ where
                                                  (singleton none refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₃ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₃) e)
                                              (singleton (some d) refl) → contradiction f' (nc₄₆ (sym xs≡₃) d)
                                          (singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                          (singleton (some b) refl) →  contradiction c' (nc₂₃ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    case (singleton oe refl) of λ where
                                      (singleton none refl) → contradiction (proj₁ f) (nc₄₆ xs≡₁ d')
                                      (singleton (some e) refl) →  contradiction e (nc₄₅ xs≡₁ d')
                                  (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₁ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₁  ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₅ e')
                                                      (singleton (some e) refl) →
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₅ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₅ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton none refl , singleton (some f') refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) →
                                                        let
                                                          @0 bs₆≡ : bs₆' ≡ bs₆
                                                          bs₆≡ =
                                                            ns₆
                                                              (begin
                                                              bs₆' ++ suffix
                                                              ≡⟨ xs≡₅ ⟩
                                                              bs₆ ++ suf₁
                                                              ∎ )
                                                              f' (proj₁  f)
                                                        in
                                                        case (‼ bs₆≡) ret (const _) of λ where
                                                          refl →
                                                            let @0 f≡ : proj₁ f ≡ f'
                                                                f≡ = uf (proj₁ f) f'
                                                            in
                                                            contradiction
                                                              (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                              (proj₂ f)
                                                      (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₅) e)
                                                  (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                              (singleton (some c) refl) →  contradiction d' (nc₃₄ (sym xs≡₁) c)
                          (singleton (some b) refl) →  contradiction d' (nc₂₄ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    case (singleton oe refl) of λ where
                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₁ e')
                                      (singleton (some e) refl) → 
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₁ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₁ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                  (singleton (some d) refl) →  contradiction e' (nc₄₅ (sym xs≡₁) d)
                              (singleton (some c) refl) →  contradiction e' (nc₃₅ (sym xs≡₁) c)
                          (singleton (some b) refl) →  contradiction e' (nc₂₅ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    case (singleton oe refl) of λ where
                                      (singleton none refl) →
                                        let
                                          @0 bs₆≡ : bs₆' ≡ bs₆
                                          bs₆≡ =
                                            ns₆
                                            (begin
                                            bs₆' ++ suffix
                                            ≡⟨ xs≡₀ ⟩
                                            bs₆ ++ suf₁
                                            ∎ )
                                            f' (proj₁  f)
                                        in
                                        case (‼ bs₆≡) ret (const _) of λ where
                                          refl →
                                            let @0 f≡ : proj₁ f ≡ f'
                                                f≡ = uf (proj₁ f) f'
                                            in
                                            contradiction
                                              (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                              (proj₂ f)
                                      (singleton (some e) refl) →  contradiction f' (nc₅₆ (sym xs≡₁) e)
                                  (singleton (some d) refl) →  contradiction f' (nc₄₆ (sym xs≡₁) d)
                              (singleton (some c) refl) →  contradiction f' (nc₃₆ (sym xs≡₁) c)
                          (singleton (some b) refl) →  contradiction f' (nc₂₆ (sym xs≡₁) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
                      contradiction (¡ abcdefLen) (λ ())
              ((singleton none refl) , (singleton (some a') refl)) → helperNoFexplicit mine theirs isSomeF (tt , tt)
              ((singleton (some a) refl) , (singleton none refl)) → helperNoFexplicit mine theirs isSomeF (tt , tt)
              ((singleton (some a) refl) , (singleton (some a') refl)) →
                let
                  @0 xs≡₁ : bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                  xs≡₁ = (begin
                              bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                             ≡⟨ solve (++-monoid UInt8) ⟩
                              (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
                             ≡⟨ trans ps≡ (sym ps≡₁) ⟩
                              (bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
                             ≡⟨ solve (++-monoid UInt8) ⟩
                              bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                              ∎ )

                  @0 bs₁≡ : bs₁' ≡ bs₁
                  bs₁≡ = ns₁ xs≡₁ a' a

                  @0 xs≡₂ : bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                  xs≡₂ = ++-cancelˡ bs₁'
                             (begin
                              bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                             ≡⟨ xs≡₁ ⟩
                              bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                             ≡⟨ cong (_++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₁≡) ⟩
                              bs₁' ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                              ∎ )
                in
                case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                  ret (const _) of λ where
                    (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    case (singleton oe refl) of λ where
                                      (singleton none refl) → contradiction (proj₁ f) (nc₂₆ xs≡₂ b')
                                      (singleton (some e) refl) →  contradiction e (nc₂₅ xs≡₂ b')
                                  (singleton (some d) refl) →  contradiction d (nc₂₄ xs≡₂ b')
                              (singleton (some c) refl) →  contradiction c (nc₂₃ xs≡₂ b')
                          (singleton (some b) refl) →
                                let
                                  @0 bs₂≡ : bs₂' ≡ bs₂
                                  bs₂≡ = ns₂ xs≡₂ b' b

                                  @0 xs≡₃ : bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                  xs≡₃ = ++-cancelˡ bs₂'
                                           (begin
                                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                           ≡⟨ xs≡₂ ⟩
                                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ≡⟨ cong (_++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₂≡) ⟩
                                           bs₂' ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ∎ )
                                in
                                case ((singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) of λ where
                                  (singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) →
                                            case (singleton oe refl) of λ where
                                              (singleton none refl) → contradiction (proj₁ f) (nc₃₆ xs≡₃ c')
                                              (singleton (some e) refl) → contradiction e (nc₃₅ xs≡₃ c')
                                          (singleton (some d) refl) → contradiction d (nc₃₄ xs≡₃ c')
                                      (singleton (some c) refl) →
                                        let
                                          @0 bs₃≡ : bs₃' ≡ bs₃
                                          bs₃≡ = ns₃ xs≡₃ c' c

                                          @0 xs≡₄ : bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                          xs≡₄ = ++-cancelˡ bs₃'
                                            (begin
                                            bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                            ≡⟨ xs≡₃ ⟩
                                            bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                            ≡⟨ cong (_++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₃≡) ⟩
                                            bs₃' ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                            ∎ )
                                        in
                                        case ((singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                                        ret (const _) of λ where
                                          (singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) → 
                                                case (singleton oe refl) of λ where
                                                  (singleton none refl) → contradiction (proj₁ f) (nc₄₆ xs≡₄ d')
                                                  (singleton (some e) refl) → contradiction e (nc₄₅ xs≡₄ d')
                                              (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₄ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₄ ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₅ e')
                                                      (singleton (some e) refl) →
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₅ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₅ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton none refl , singleton (some f') refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) →
                                                        let
                                                          @0 bs₆≡ : bs₆' ≡ bs₆
                                                          bs₆≡ =
                                                            ns₆
                                                              (begin
                                                              bs₆' ++ suffix
                                                              ≡⟨ xs≡₅ ⟩
                                                              bs₆ ++ suf₁
                                                              ∎ )
                                                              f' (proj₁  f)
                                                        in
                                                        case (‼ bs₆≡) ret (const _) of λ where
                                                          refl →
                                                            let @0 f≡ : proj₁ f ≡ f'
                                                                f≡ = uf (proj₁ f) f'
                                                            in
                                                            contradiction
                                                              (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                              (proj₂ f)
                                                      (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₅) e)
                                                  (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                          (singleton none refl , singleton (some e') refl , singleton of' refl) →
                                                case (singleton od refl) of λ where
                                                  (singleton none refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₄ e')
                                                      (singleton (some e) refl) → 
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₄ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₄ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton (some d) refl) →  contradiction e' (nc₄₅ (sym xs≡₄) d)
                                          (singleton none refl , singleton none refl , singleton (some f') refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) →
                                                case (singleton oe refl) of λ where
                                                  (singleton none refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₄ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₄) e)
                                              (singleton (some d) refl) → contradiction f' (nc₄₆ (sym xs≡₄) d)
                                          (singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                  (singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) →
                                            case (singleton oe refl) of λ where
                                              (singleton none refl) → contradiction (proj₁ f) (nc₄₆ xs≡₃ d')
                                              (singleton (some e) refl) → contradiction e (nc₄₅ xs≡₃ d')
                                          (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₃ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₃ ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₅ e')
                                                      (singleton (some e) refl) → 
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₅ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₅ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton none refl , singleton (some f') refl) →
                                                            case (singleton oe refl) of λ where
                                                              (singleton none refl) →
                                                                let
                                                                  @0 bs₆≡ : bs₆' ≡ bs₆
                                                                  bs₆≡ =
                                                                    ns₆
                                                                    (begin
                                                                    bs₆' ++ suffix
                                                                    ≡⟨ xs≡₅ ⟩
                                                                    bs₆ ++ suf₁
                                                                    ∎ )
                                                                    f' (proj₁  f)
                                                                in
                                                                case (‼ bs₆≡) ret (const _) of λ where
                                                                  refl →
                                                                    let @0 f≡ : proj₁ f ≡ f'
                                                                        f≡ = uf (proj₁ f) f'
                                                                    in
                                                                    contradiction
                                                                      (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                      (proj₂ f)
                                                              (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₅) e)
                                                  (singleton none refl , singleton none refl) →  contradiction (¡ abcdefLen) (λ ())
                                      (singleton (some c) refl) → contradiction d' (nc₃₄ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) →
                                            case (singleton oe refl) of λ where
                                              (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₃ e')
                                              (singleton (some e) refl) → 
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₃ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₃ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                          (singleton (some d) refl) →  contradiction e' (nc₄₅ (sym xs≡₃) d)
                                      (singleton (some c) refl) →  contradiction e' (nc₃₅ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                                    case (singleton oc refl) of λ where
                                      (singleton none refl) →
                                        case (singleton od refl) of λ where
                                          (singleton none refl) →
                                            case (singleton oe refl) of λ where
                                              (singleton none refl) →
                                                let
                                                  @0 bs₆≡ : bs₆' ≡ bs₆
                                                  bs₆≡ =
                                                    ns₆
                                                    (begin
                                                    bs₆' ++ suffix
                                                    ≡⟨ xs≡₃ ⟩
                                                    bs₆ ++ suf₁
                                                    ∎ )
                                                    f' (proj₁  f)
                                                in
                                                case (‼ bs₆≡) ret (const _) of λ where
                                                  refl →
                                                    let @0 f≡ : proj₁ f ≡ f'
                                                        f≡ = uf (proj₁ f) f'
                                                    in
                                                    contradiction
                                                      (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                      (proj₂ f)
                                              (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₃) e)
                                          (singleton (some d) refl) →  contradiction f' (nc₄₆ (sym xs≡₃) d)
                                      (singleton (some c) refl) →  contradiction f' (nc₃₆ (sym xs≡₃) c)
                                  (singleton none refl , singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                    (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    case (singleton oe refl) of λ where
                                      (singleton none refl) → contradiction (proj₁ f) (nc₃₆ xs≡₂ c')
                                      (singleton (some e) refl) →  contradiction e (nc₃₅ xs≡₂ c')
                                  (singleton (some d) refl) →  contradiction d (nc₃₄ xs≡₂ c')
                              (singleton (some c) refl) →
                                let
                                  @0 bs₃≡ : bs₃' ≡ bs₃
                                  bs₃≡ = ns₃ xs≡₂ c' c

                                  @0 xs≡₃ : bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                  xs≡₃ = ++-cancelˡ bs₃'
                                           (begin
                                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                           ≡⟨ xs≡₂ ⟩
                                           bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ≡⟨ cong (_++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₃≡) ⟩
                                           bs₃' ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                           ∎ )
                                in
                                   case ((singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
                                     ret (const _) of λ where
                                          (singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) → 
                                                case (singleton oe refl) of λ where
                                                  (singleton none refl) → contradiction (proj₁ f) (nc₄₆ xs≡₃ d')
                                                  (singleton (some e) refl) → contradiction e (nc₄₅ xs≡₃ d')
                                              (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₃ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₃ ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₅ e')
                                                      (singleton (some e) refl) →
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₅ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₅ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton none refl , singleton (some f') refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) →
                                                        let
                                                          @0 bs₆≡ : bs₆' ≡ bs₆
                                                          bs₆≡ =
                                                            ns₆
                                                              (begin
                                                              bs₆' ++ suffix
                                                              ≡⟨ xs≡₅ ⟩
                                                              bs₆ ++ suf₁
                                                              ∎ )
                                                              f' (proj₁  f)
                                                        in
                                                        case (‼ bs₆≡) ret (const _) of λ where
                                                          refl →
                                                            let @0 f≡ : proj₁ f ≡ f'
                                                                f≡ = uf (proj₁ f) f'
                                                            in
                                                            contradiction
                                                              (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                              (proj₂ f)
                                                      (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₅) e)
                                                  (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                          (singleton none refl , singleton (some e') refl , singleton of' refl) →
                                                case (singleton od refl) of λ where
                                                  (singleton none refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₃ e')
                                                      (singleton (some e) refl) → 
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₃ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₃ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton (some d) refl) →  contradiction e' (nc₄₅ (sym xs≡₃) d)
                                          (singleton none refl , singleton none refl , singleton (some f') refl) →
                                            case (singleton od refl) of λ where
                                              (singleton none refl) →
                                                case (singleton oe refl) of λ where
                                                  (singleton none refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₃ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₃) e)
                                              (singleton (some d) refl) → contradiction f' (nc₄₆ (sym xs≡₃) d)
                                          (singleton none refl , singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                          (singleton (some b) refl) →  contradiction c' (nc₂₃ (sym xs≡₂) b)                          
                    (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    case (singleton oe refl) of λ where
                                      (singleton none refl) → contradiction (proj₁ f) (nc₄₆ xs≡₂ d')
                                      (singleton (some e) refl) →  contradiction e (nc₄₅ xs≡₂ d')
                                  (singleton (some d) refl) →
                                                let
                                                  @0 bs₄≡ : bs₄' ≡ bs₄
                                                  bs₄≡ = ns₄ xs≡₂ d' d

                                                  @0 xs≡₅ : bs₅' ++ bs₆' ++ suffix ≡ bs₅ ++ bs₆ ++ suf₁
                                                  xs≡₅ = ++-cancelˡ bs₄'
                                                    (begin
                                                    bs₄' ++ bs₅' ++ bs₆' ++ suffix
                                                    ≡⟨ xs≡₂  ⟩
                                                    bs₄ ++ bs₅ ++ bs₆ ++ suf₁
                                                    ≡⟨ cong (_++ bs₅ ++ bs₆ ++ suf₁) (sym bs₄≡) ⟩
                                                    bs₄' ++ bs₅ ++ bs₆ ++ suf₁
                                                    ∎ )
                                                in
                                                case ((singleton oe' refl) ,′e (singleton of' refl)) ret (const _) of λ where
                                                  (singleton (some e') refl , singleton of' refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₅ e')
                                                      (singleton (some e) refl) →
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₅ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₅ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                                  (singleton none refl , singleton (some f') refl) →
                                                    case (singleton oe refl) of λ where
                                                      (singleton none refl) →
                                                        let
                                                          @0 bs₆≡ : bs₆' ≡ bs₆
                                                          bs₆≡ =
                                                            ns₆
                                                              (begin
                                                              bs₆' ++ suffix
                                                              ≡⟨ xs≡₅ ⟩
                                                              bs₆ ++ suf₁
                                                              ∎ )
                                                              f' (proj₁  f)
                                                        in
                                                        case (‼ bs₆≡) ret (const _) of λ where
                                                          refl →
                                                            let @0 f≡ : proj₁ f ≡ f'
                                                                f≡ = uf (proj₁ f) f'
                                                            in
                                                            contradiction
                                                              (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                              (proj₂ f)
                                                      (singleton (some e) refl) → contradiction f' (nc₅₆ (sym xs≡₅) e)
                                                  (singleton none refl , singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                              (singleton (some c) refl) →  contradiction d' (nc₃₄ (sym xs≡₂) c)
                          (singleton (some b) refl) →  contradiction d' (nc₂₄ (sym xs≡₂) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    case (singleton oe refl) of λ where
                                      (singleton none refl) → contradiction (proj₁ f) (nc₅₆ xs≡₂ e')
                                      (singleton (some e) refl) →
                                                        let
                                                          @0 bs₅≡ : bs₅' ≡ bs₅
                                                          bs₅≡ = ns₅ xs≡₂ e' e

                                                          @0 xs≡₆ : bs₆' ++ suffix ≡ bs₆ ++ suf₁
                                                          xs≡₆ = ++-cancelˡ bs₅'
                                                               (begin
                                                               bs₅' ++ bs₆' ++ suffix
                                                               ≡⟨ xs≡₂ ⟩
                                                               bs₅ ++ bs₆ ++ suf₁
                                                               ≡⟨ cong (_++ bs₆ ++ suf₁) (sym bs₅≡) ⟩
                                                               bs₅' ++ bs₆ ++ suf₁
                                                               ∎ )
                                                        in
                                                        case (singleton of' refl) ret (const _) of λ where
                                                            (singleton none refl) → contradiction (¡ abcdefLen) (λ ())
                                                            (singleton (some f') refl) →
                                                              let
                                                                @0 bs₆≡ : bs₆' ≡ bs₆
                                                                bs₆≡ =
                                                                  ns₆
                                                                  (begin
                                                                  bs₆' ++ suffix
                                                                  ≡⟨ xs≡₆ ⟩
                                                                  bs₆ ++ suf₁
                                                                  ∎ )
                                                                  f' (proj₁  f)
                                                              in
                                                              case (‼ bs₆≡) ret (const _) of λ where
                                                                refl →
                                                                  let @0 f≡ : proj₁ f ≡ f'
                                                                      f≡ = uf (proj₁ f) f'
                                                                  in
                                                                  contradiction
                                                                    (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                                                    (proj₂ f)
                                  (singleton (some d) refl) →  contradiction e' (nc₄₅ (sym xs≡₂) d)
                              (singleton (some c) refl) →  contradiction e' (nc₃₅ (sym xs≡₂) c)
                          (singleton (some b) refl) →  contradiction e' (nc₂₅ (sym xs≡₂) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
                        case (singleton ob refl) of λ where
                          (singleton none refl) →
                            case (singleton oc refl) of λ where
                              (singleton none refl) →
                                case (singleton od refl) of λ where
                                  (singleton none refl) →
                                    case (singleton oe refl) of λ where
                                      (singleton none refl) →
                                        let
                                          @0 bs₆≡ : bs₆' ≡ bs₆
                                          bs₆≡ = 
                                            ns₆
                                            (begin
                                            bs₆' ++ suffix
                                            ≡⟨ xs≡₂ ⟩
                                            bs₆  ++ suf₁
                                            ∎ )
                                            f' (proj₁  f)
                                        in
                                        case (‼ bs₆≡) ret (const _) of λ where
                                          refl →
                                            let @0 f≡ : proj₁ f ≡ f'
                                                f≡ = uf (proj₁ f) f'
                                            in
                                            contradiction
                                              (subst₀ (λ x → Default.NotDefault default₆ x) (cong some (sym (‼ f≡))) ofnd)
                                              (proj₂ f)
                                      (singleton (some e) refl) →  contradiction f' (nc₅₆ (sym xs≡₂) e)
                                  (singleton (some d) refl) →  contradiction f' (nc₄₆ (sym xs≡₂) d)
                              (singleton (some c) refl) →  contradiction f' (nc₃₆ (sym xs≡₂) c)
                          (singleton (some b) refl) →  contradiction f' (nc₂₆ (sym xs≡₂) b)
                    (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
                      contradiction (¡ abcdefLen) (λ ())
        (yes pb , yes pc , yes pe , yes pf) →
          return (yes (success pre₁ _ r₁≡
                   (mk×ₚ (mk&ₚ oa (mk&ₚ (mkDefault ob pb) (mk&ₚ (mkDefault oc pc)
                          (mk&ₚ od (mk&ₚ (mkDefault oe pe) (mkDefault of pf)
                          refl) refl) refl) refl) refl) abcdefLen) suf₁ ps≡₁))

    where
    open ≡-Reasoning


    helperNoBexplicit : (mine : Success (ExactLength (&ₚ(Option A) (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (&ₚ (Option E) (Option F)))))) n) xs)
                        (theirs : Success (ExactLength (&ₚ(Option A) (&ₚ (Default B default₂) (&ₚ(Default C default₃) (&ₚ (Option D) (&ₚ (Default E default₅) (Default F default₆)))))) n) xs)
                        (explicitB : T (isSome (fstₚ (sndₚ (fstₚ (Success.value mine)))))) → T (not (isNone (fstₚ (fstₚ (Success.value mine))) ∧ isNone (fstₚ (fstₚ (Success.value theirs)))))
                                                                                             × T (not ((isSome(fstₚ (fstₚ (Success.value mine))) ∧ isSome (fstₚ (fstₚ (Success.value theirs)))))) → ⊥
    helperNoBexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) xs≡') abcdeflen') suf' ps≡') explicitB (() , tt)
    helperNoBexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} (some b) (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitB x =
        contradiction b (nc₁₂ (sym bs≡) a')
        where
        @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoBexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault (some b') _) (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitB x = contradiction b' (nc₁₂ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoBexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault (some c') _) (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitB x = contradiction c' (nc₁₃ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoBexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} (some d') (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitB x = contradiction d' (nc₁₄ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoBexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault (some e') _) of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitB x = contradiction e' (nc₁₅ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoBexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault none _) (mkDefault (some f') _) refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitB x = contradiction f' (nc₁₆ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₆' ++ suf'
                ∎ )
    helperNoBexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault none _) (mkDefault none _) refl) refl) refl) refl) refl) (─ ())) suf' ps≡') explicitB x
    helperNoBexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡) (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) xs≡') abcdeflen') suf' ps≡') explicitB (tt , ())


    helperNoCexplicit : (mine : Success (ExactLength (&ₚ(Option A) (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (&ₚ (Option E) (Option F)))))) n) xs)
                        (theirs : Success (ExactLength (&ₚ(Option A) (&ₚ (Default B default₂) (&ₚ(Default C default₃) (&ₚ (Option D) (&ₚ (Default E default₅) (Default F default₆)))))) n) xs)
                        (explicitC : T (isSome (fstₚ (sndₚ (sndₚ (fstₚ (Success.value mine))))))) →
                          T (not (isNone (fstₚ (fstₚ (Success.value mine))) ∧ isNone (fstₚ (fstₚ (Success.value theirs)))))
                          × T (not ((isSome (fstₚ (fstₚ (Success.value mine))) ∧ isSome (fstₚ (fstₚ (Success.value theirs)))))) → ⊥
    helperNoCexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) xs≡') abcdeflen') suf' ps≡') explicitC (() , tt)
    helperNoCexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} none (mk&ₚ {bs₃} (some c) (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitC x =
        contradiction c (nc₁₃ (sym bs≡) a')
        where
        @0 bs≡ : bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoCexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} (some b) (mk&ₚ {bs₃} (some c) (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitC x =
        contradiction b (nc₁₂ (sym bs≡) a')
        where
        @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoCexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault (some b') _) (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitC x = contradiction b' (nc₁₂ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoCexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault (some c') _) (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitC x = contradiction c' (nc₁₃ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoCexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} (some d') (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitC x = contradiction d' (nc₁₄ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoCexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault (some e') _) of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitC x = contradiction e' (nc₁₅ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoCexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault none _) (mkDefault (some f') _) refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitC x = contradiction f' (nc₁₆ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₆' ++ suf'
                ∎ )
    helperNoCexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault none _) (mkDefault none _) refl) refl) refl) refl) refl) (─ ())) suf' ps≡') explicitC x
      
    helperNoCexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) xs≡') abcdeflen') suf' ps≡') explicitC (tt , ())


    helperNoEexplicit : (mine : Success (ExactLength (&ₚ(Option A) (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (&ₚ (Option E) (Option F)))))) n) xs)
                        (theirs : Success (ExactLength (&ₚ(Option A) (&ₚ (Default B default₂) (&ₚ(Default C default₃) (&ₚ (Option D) (&ₚ (Default E default₅) (Default F default₆)))))) n) xs)
                        (explicitE : T (isSome (fstₚ (sndₚ (sndₚ (sndₚ (sndₚ (fstₚ (Success.value mine))))))))) →
                          T (not (isNone (fstₚ (fstₚ (Success.value mine))) ∧ isNone (fstₚ (fstₚ (Success.value theirs)))))
                          × T (not ((isSome (fstₚ (fstₚ (Success.value mine))) ∧ isSome (fstₚ (fstₚ (Success.value theirs)))))) → ⊥
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) xs≡') abcdeflen') suf' ps≡') explicitE (() , tt)
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} none (mk&ₚ {bs₃} none (mk&ₚ {bs₄} none (mk&ₚ {bs₅}{bs₆} (some e) of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitE x =
      contradiction e (nc₁₅ (sym bs≡) a')
      where
        @0 bs≡ : bs₅ ++ bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} none (mk&ₚ {bs₃} none (mk&ₚ {bs₄} (some d) (mk&ₚ {bs₅}{bs₆} (some e) of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitE x =
      contradiction d (nc₁₄ (sym bs≡) a')
      where
        @0 bs≡ : bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} none (mk&ₚ {bs₃} (some c) (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} (some e) of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitE x =
      contradiction c (nc₁₃ (sym bs≡) a')
      where
        @0 bs≡ : bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} (some b) (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} (some e) of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitE x =
      contradiction b (nc₁₂ (sym bs≡) a')
      where
        @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault (some b') _) (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitE x = contradiction b' (nc₁₂ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault (some c') _) (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitE x = contradiction c' (nc₁₃ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} (some d') (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitE x = contradiction d' (nc₁₄ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault (some e') _) of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitE x = contradiction e' (nc₁₅ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault none _) (mkDefault (some f') _) refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitE x = contradiction f' (nc₁₆ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₆' ++ suf'
                ∎ )
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault none _) (mkDefault none _) refl) refl) refl) refl) refl) (─ ())) suf' ps≡') explicitE x
    helperNoEexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) xs≡') abcdeflen') suf' ps≡') explicitE (tt , ())


    helperNoFexplicit : (mine : Success (ExactLength (&ₚ(Option A) (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (&ₚ (Option E) (Option F)))))) n) xs)
                        (theirs : Success (ExactLength (&ₚ(Option A) (&ₚ (Default B default₂) (&ₚ(Default C default₃) (&ₚ (Option D) (&ₚ (Default E default₅) (Default F default₆)))))) n) xs)
                        (explicitF : T (isSome (sndₚ (sndₚ (sndₚ (sndₚ (sndₚ (fstₚ (Success.value mine))))))))) →
                          T (not (isNone (fstₚ (fstₚ (Success.value mine))) ∧ isNone (fstₚ (fstₚ (Success.value theirs)))))
                          × T (not ((isSome (fstₚ (fstₚ (Success.value mine))) ∧ isSome (fstₚ (fstₚ (Success.value theirs)))))) → ⊥
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) xs≡') abcdeflen') suf' ps≡') explicitF (() , tt)
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} none (mk&ₚ {bs₃} none (mk&ₚ {bs₄} none (mk&ₚ {bs₅}{bs₆} none (some f) refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitF x =
      contradiction f (nc₁₆ (sym bs≡) a')
      where
        @0 bs≡ : bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} none (mk&ₚ {bs₃} none (mk&ₚ {bs₄} none (mk&ₚ {bs₅}{bs₆} (some e) (some f) refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitF x =
      contradiction e (nc₁₅ (sym bs≡) a')
      where
        @0 bs≡ : bs₅ ++ bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} none (mk&ₚ {bs₃} none (mk&ₚ {bs₄} (some d) (mk&ₚ {bs₅}{bs₆} oe (some f) refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitF x =
      contradiction d (nc₁₄ (sym bs≡) a')
      where
        @0 bs≡ : bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} none (mk&ₚ {bs₃} (some c) (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe (some f) refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitF x =
      contradiction c (nc₁₃ (sym bs≡) a')
      where
        @0 bs≡ : bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} none (mk&ₚ {bs₂} (some b) (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe (some f) refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitF x =
      contradiction b (nc₁₂ (sym bs≡) a')
      where
        @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault (some b') _) (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitF x = contradiction b' (nc₁₂ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault (some c') _) (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitF x = contradiction c' (nc₁₃ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} (some d') (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitF x = contradiction d' (nc₁₄ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₄' ++ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₄' ++ bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault (some e') _) of' refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitF x = contradiction e' (nc₁₅ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₅' ++ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₅' ++ bs₆' ++ suf'
                ∎ )
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault none _) (mkDefault (some f') _) refl) refl) refl) refl) refl) abcdeflen') suf' ps≡') explicitF x = contradiction f' (nc₁₆ bs≡ a)
      where
        @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf ≡ bs₆' ++ suf'
        bs≡ = (begin
                bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf
                ≡⟨ solve (++-monoid UInt8) ⟩
                pre ++ suf
                ≡⟨ trans ps≡ (sym ps≡') ⟩
                pre' ++ suf'
                ≡⟨ solve (++-monoid UInt8) ⟩
                bs₆' ++ suf'
                ∎ )
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} none (mk&ₚ {bs₂'} (mkDefault none _) (mk&ₚ {bs₃'} (mkDefault none _) (mk&ₚ {bs₄'} none (mk&ₚ {bs₅'}{bs₆'} (mkDefault none _) (mkDefault none _) refl) refl) refl) refl) refl) (─ ())) suf' ps≡') explicitF x
    helperNoFexplicit (success pre r rlen (mk×ₚ (mk&ₚ {bs₁} (some a) (mk&ₚ {bs₂} ob (mk&ₚ {bs₃} oc (mk&ₚ {bs₄} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) xs≡) abcdefLen) suf ps≡)
      (success pre' r' rlen' (mk×ₚ (mk&ₚ {bs₁'} (some a') (mk&ₚ {bs₂'} ob' (mk&ₚ {bs₃'} oc' (mk&ₚ {bs₄'} od' (mk&ₚ {bs₅'}{bs₆'} oe' of' refl) refl) refl) refl) xs≡') abcdeflen') suf' ps≡') explicitE (tt , ())
