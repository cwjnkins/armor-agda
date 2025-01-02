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

  postulate
    parseOption₂Default₄
      : ∀ {A D : @0 List UInt8 → Set}
      → @0 Unambiguous A → @0 NoSubstrings A
      → @0 Unambiguous B → @0 NoSubstrings B
      → @0 Unambiguous C → @0 NoSubstrings C
      → @0 Unambiguous D → @0 NoSubstrings D
      → @0 Unambiguous E → @0 NoSubstrings E
      → @0 NoSubstrings F
      → @0 NoConfusion A B → @0 NoConfusion A C → @0 NoConfusion A D → @0 NoConfusion A E → @0 NoConfusion A F
      → @0 NoConfusion B C → @0 NoConfusion B D → @0 NoConfusion B E → @0 NoConfusion B F
      → @0 NoConfusion C D → @0 NoConfusion C E → @0 NoConfusion C F
      → @0 NoConfusion D E → @0 NoConfusion D F
      → @0 NoConfusion E F
      → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B → Parser (Logging ∘ Dec) C
      → Parser (Logging ∘ Dec) D → Parser (Logging ∘ Dec) E → Parser (Logging ∘ Dec) F
      → ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option A) (&ₚ (Default B default₂) (&ₚ(Default C default₃)
                                   (&ₚ (Option D) (&ₚ (Default E default₅) (Default F default₆)))))) n)
  -- runParser (parseOption₂Default₄ ua ns₁ ub ns₂ uc ns₃ ud ns₄ ue ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf zero) xs =
  --   return (yes (success [] _ refl (mk×ₚ (mk&ₚ none (mk&ₚ (mkDefault none tt) (mk&ₚ (mkDefault none tt) (mk&ₚ none (mk&ₚ (mkDefault none tt) (mkDefault none tt)
  --               refl) refl) refl) refl) refl) (─ refl)) xs refl))
  -- runParser (parseOption₂Default₄ ua ns₁ ub ns₂ uc ns₃ ud ns₄ ue ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf n@(suc _)) xs = do
  --   (yes (success pre₁ r₁ r₁≡ (mk×ₚ  (mk&ₚ {bs₁}{bs₂'} oa (mk&ₚ {bs₂}{bs₃'} ob (mk&ₚ {bs₃}{bs₄'} oc (mk&ₚ {bs₄}{bs₅'} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf₁ ps≡₁)) ←
  --     runParser (parse₂Option₆ loc ns₁ ns₂ ns₃ ns₄ ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf n) xs
  --     where no ¬p₁₂' → do
  --       tell $ loc String.++ ": failed to parse"
  --       return ∘ no $ λ where
  --         (success prefix read read≡ (mk×ₚ  (mk&ₚ oa (mk&ₚ (mkDefault ob _) (mk&ₚ (mkDefault oc _) (mk&ₚ od (mk&ₚ (mkDefault oe _) (mkDefault of _) refl) refl) refl) refl) refl) abcdefLen) suffix ps≡) →
  --           contradiction
  --             (success prefix _ read≡ (mk×ₚ  (mk&ₚ oa (mk&ₚ ob (mk&ₚ oc (mk&ₚ od (mk&ₚ oe of refl) refl) refl) refl) refl) abcdefLen) suffix ps≡)
  --             ¬p₁₂'
  --   case (Default.notDefault? default₂ ob)  ,′e (Default.notDefault?  default₃ oc ,′e (Default.notDefault?  default₅ oe ,′e Default.notDefault? default₆ of))
  --     ret const _ of λ where
  --       (no ¬pb , c , e , f) → return ∘ no $ λ where
  --         (success prefix read read≡
  --           (mk×ₚ
  --             (mk&ₚ {bs₁ = bs₁'} {bs₂ = bs₂₃₄₅₆'} oa'
  --             (mk&ₚ {bs₁ = bs₂'} {bs₂ = bs₃₄₅₆'} (mkDefault ob' obnd)
  --             (mk&ₚ {bs₁ = bs₃'} {bs₂ = bs₄₅₆'} (mkDefault oc' ocnd)
  --             (mk&ₚ {bs₁ = bs₄'} {bs₂ = bs₅₆'} od'
  --             (mk&ₚ {bs₁ = bs₅'} {bs₂ = bs₆'} (mkDefault oe' oend)
  --                    (mkDefault of' ofnd) refl) refl) refl) refl) refl) abcdefLen)
  --           suffix ps≡) →
  --           let b : Σ (B bs₂) (λ b → ¬ Default.NotDefault default₂ (some b))
  --               b = case (Singleton ob ∋ singleton ob refl) ret (const _) of λ where
  --                 (singleton none refl) → contradiction tt ¬pb
  --                 (singleton (some x) refl) → (x , ¬pb)
  --           in
  --           case (oa ,′e oa') ret (const _) of λ where
  --             (none , none) →
  --               let @0 xs≡₀ : (bs₂' ++ bs₃₄₅₆') ++ suffix ≡ (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --                   xs≡₀ = trans ps≡ (sym ps≡₁)

  --                   @0 xs≡₁ : bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                   xs≡₁ = (begin
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
  --                           ≡⟨ xs≡₀ ⟩
  --                           (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ∎ )                         
  --               in
  --               case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  --                 ret (const _) of λ where
  --                   (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
  --                       let
  --                         @0 bs₂≡ : bs₂' ≡ bs₂
  --                         bs₂≡ =
  --                           ns₂
  --                           (begin
  --                             bs₂' ++ (bs₃₄₅₆' ++ suffix)
  --                            ≡⟨ sym (++-assoc bs₂' _ _) ⟩
  --                             (bs₂' ++ bs₃₄₅₆') ++ suffix
  --                            ≡⟨ xs≡₀ ⟩
  --                              (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --                            ≡⟨ ++-assoc bs₂ (bs₃ ++ bs₄ ++ bs₅ ++ bs₆) suf₁  ⟩
  --                              bs₂ ++ ((bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁)
  --                            ∎ )
  --                           b' (proj₁  b)
  --                       in
  --                       case (‼ bs₂≡) ret (const _) of λ where
  --                         refl →
  --                           let @0 b≡ : proj₁ b ≡ b'
  --                               b≡ = ub (proj₁ b) b'
  --                           in
  --                           contradiction
  --                             (subst₀ (λ x → Default.NotDefault default₂ x) (cong some (sym (‼ b≡))) obnd)
  --                             (proj₂ b)
  --                   (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
  --                       let
  --                         @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction c' (nc₂₃ bs≡ (proj₁ b))
  --                   (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
  --                       let
  --                         @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction d' (nc₂₄ bs≡ (proj₁ b))
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
  --                       let
  --                         @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction e' (nc₂₅ bs≡ (proj₁ b))
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
  --                       let
  --                          @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                          bs≡ = (begin
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₆' ++ suffix)  ⟩
  --                           bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction f' (nc₂₆ bs≡ (proj₁ b))
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
  --                     contradiction (¡ abcdefLen) (λ ())
  --             (none , some a') →
  --               let
  --                 @0 xs≡₁ : bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                 xs≡₁ = (begin
  --                           bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
  --                           ≡⟨ trans ps≡ (sym ps≡₁) ⟩
  --                           (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ∎ )    
  --               in
  --               case ((singleton ob refl) ,′e (singleton oc refl) ,′e (singleton od refl) ,′e (singleton oe refl) ,′e (singleton of refl)) 
  --                 ret (const _) of λ where
  --                   (singleton (some b) refl , singleton oc refl , singleton od refl , singleton oe refl , singleton of refl) →
  --                     let
  --                       @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       bs≡ = (begin
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                         contradiction b (nc₁₂ (sym bs≡) a')
  --                   (singleton none refl , singleton (some c) refl , singleton od refl , singleton oe refl , singleton of refl) →
  --                       let
  --                         @0 bs≡ : bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction c (nc₁₃ (sym bs≡) a')
  --                   (singleton none refl , singleton none refl , singleton (some d) refl , singleton oe refl , singleton of refl) →
  --                       let
  --                         @0 bs≡ : bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction d (nc₁₄ (sym bs≡) a')
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton (some e) refl , singleton of refl) →
  --                       let
  --                         @0 bs≡ : bs₅ ++ bs₆ ++ suf₁ ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction e (nc₁₅ (sym bs≡) a')
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f) refl) →
  --                       let
  --                         @0 bs≡ : bs₆ ++ suf₁ ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₆ ++ suf₁
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction f (nc₁₆ (sym bs≡) a')
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
  --                     {!!}
  --             (some a , none) →
  --               let
  --                 @0 xs≡₁ : bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                 xs≡₁ = (begin
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
  --                           ≡⟨ trans ps≡ (sym ps≡₁) ⟩
  --                           (bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ∎ )     
  --               in
  --               case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  --                 ret (const _) of λ where
  --                   (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
  --                     let
  --                       @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       bs≡ = (begin
  --                           bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                         contradiction b' (nc₁₂ bs≡ a)
  --                   (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
  --                       let
  --                         @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction c' (nc₁₃ bs≡ a)
  --                   (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
  --                       let
  --                         @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction d' (nc₁₄ bs≡ a)
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
  --                       let
  --                         @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction e' (nc₁₅ bs≡ a)
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
  --                       let
  --                         @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₁ ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₆' ++ suffix)  ⟩
  --                           bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction f' (nc₁₆ bs≡ a)
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
  --                     contradiction (¡ abcdefLen) λ where ()
  --             (some a , some a') →
  --               let
  --                 @0 xs≡₁ : bs₁' ++ bs₂' ++ bs₃₄₅₆' ++ suffix ≡ bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                 xs≡₁ = (begin
  --                             bs₁' ++ bs₂' ++ bs₃₄₅₆' ++ suffix
  --                            ≡⟨ solve (++-monoid UInt8) ⟩
  --                             (bs₁' ++ bs₂' ++ bs₃₄₅₆') ++ suffix
  --                            ≡⟨ trans ps≡ (sym ps≡₁) ⟩
  --                             (bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --                            ≡⟨ solve (++-monoid UInt8) ⟩
  --                             bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                             ∎ )

  --                 @0 bs₁≡ : bs₁' ≡ bs₁
  --                 bs₁≡ = ns₁ xs≡₁ a' a

  --                 @0 xs≡₂ : bs₂' ++ bs₃₄₅₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                 xs≡₂ = ++-cancelˡ bs₁'
  --                            (begin
  --                             bs₁' ++ bs₂' ++ bs₃₄₅₆' ++ suffix
  --                            ≡⟨ xs≡₁ ⟩
  --                             bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                            ≡⟨ cong (_++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₁≡) ⟩
  --                             bs₁' ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                             ∎ )
  --               in
  --               case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  --                 ret (const _) of λ where
  --                   (singleton (some b') refl , singleton ob' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
  --                     let                                           
  --                       @0 bs₂≡ : bs₂' ≡ bs₂
  --                       bs₂≡ = ns₂ xs≡₂ b' (proj₁  b)
  --                     in
  --                     case (‼ bs₂≡) ret (const _) of λ where
  --                       refl →
  --                         let @0 b≡ : proj₁ b ≡ b'
  --                             b≡ = ub (proj₁ b) b'
  --                         in
  --                         contradiction
  --                           (subst₀ (λ x → Default.NotDefault default₂ x) (cong some (sym (‼ b≡))) obnd)
  --                           (proj₂ b)
  --                   (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
  --                       let
  --                         @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₂ ⟩
  --                           bs₂' ++ bs₃₄₅₆' ++ suffix
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction c' (nc₂₃ bs≡ (proj₁ b))
  --                   (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
  --                       let
  --                         @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₂ ⟩
  --                           bs₂' ++ bs₃₄₅₆' ++ suffix
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction d' (nc₂₄ bs≡ (proj₁ b))
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
  --                       let
  --                         @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                         bs≡ = (begin
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₂ ⟩
  --                           bs₂' ++ bs₃₄₅₆' ++ suffix
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₅' ++ bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction e' (nc₂₅ bs≡ (proj₁ b))
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
  --                       let
  --                          @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                          bs≡ = (begin
  --                           bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ≡⟨ sym xs≡₂ ⟩
  --                           bs₂' ++ bs₃₄₅₆' ++ suffix
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ ++-identityˡ (bs₆' ++ suffix)  ⟩
  --                           bs₆' ++ suffix
  --                           ∎ )
  --                       in
  --                       contradiction f' (nc₂₆ bs≡ (proj₁ b))
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
  --                     {!!}
  --       (yes pb , no ¬pc , e , f) → return ∘ no $ λ where
  --         (success prefix read read≡
  --           (mk×ₚ
  --             (mk&ₚ {bs₁ = bs₁'} {bs₂ = bs₂₃₄₅₆'} oa'
  --             (mk&ₚ {bs₁ = bs₂'} {bs₂ = bs₃₄₅₆'} (mkDefault ob' obnd)
  --             (mk&ₚ {bs₁ = bs₃'} {bs₂ = bs₄₅₆'} (mkDefault oc' ocnd)
  --             (mk&ₚ {bs₁ = bs₄'} {bs₂ = bs₅₆'} od'
  --             (mk&ₚ {bs₁ = bs₅'} {bs₂ = bs₆'} (mkDefault oe' oend)
  --                    (mkDefault of' ofnd) refl) refl) refl) refl) refl) abcdefLen)
  --           suffix ps≡) →
  --           let c : Σ (C bs₃) (λ c → ¬ Default.NotDefault default₃ (some c))
  --               c = case (Singleton oc ∋ singleton oc refl) ret (const _) of λ where
  --                 (singleton none refl) → contradiction tt ¬pc
  --                 (singleton (some x) refl) → (x , ¬pc)
  --           in
  --           case (oa ,′e oa') ret (const _) of λ where
  --             (none , none) →
  --               let @0 xs≡₀ : (bs₃' ++ bs₄₅₆') ++ suffix ≡ (bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --                   xs≡₀ = {!!} -- trans ps≡ (sym ps≡₁)

  --                   @0 xs≡₁ : bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                   xs≡₁ = (begin
  --                           bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           (bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
  --                           ≡⟨ xs≡₀ ⟩
  --                           (bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --                           ≡⟨ solve (++-monoid UInt8) ⟩
  --                           bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                           ∎ ) 
                            
  --               in
  --               case ((singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  --                 ret (const _) of λ where
  --                   (singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
  --                       let
  --                         @0 bs₃≡ : bs₃' ≡ bs₃
  --                         bs₃≡ =
  --                           ns₃
  --                           (begin
  --                             bs₃' ++ (bs₄₅₆' ++ suffix)
  --                            ≡⟨ sym (++-assoc bs₃' _ _) ⟩
  --                             (bs₃' ++ bs₄₅₆') ++ suffix
  --                            ≡⟨ xs≡₀ ⟩
  --                              (bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --                            ≡⟨ ++-assoc bs₃ (bs₄ ++ bs₅ ++ bs₆) suf₁  ⟩
  --                              bs₃ ++ ((bs₄ ++ bs₅ ++ bs₆) ++ suf₁)
  --                            ∎ )
  --                           c' (proj₁  c)
  --                       in
  --                       case (‼ bs₃≡) ret (const _) of λ where
  --                         refl →
  --                           let @0 c≡ : proj₁ c ≡ c'
  --                               c≡ = uc (proj₁ c) c'
  --                           in
  --                           contradiction
  --                             (subst₀ (λ x → Default.NotDefault default₃ x) (cong some (sym (‼ c≡))) ocnd)
  --                             (proj₂ c)
  --                   (singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → {!!}
  --                       -- let
  --                       --   @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --   bs≡ = (begin
  --                       --     bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                       --     ≡⟨ sym xs≡₁ ⟩
  --                       --     bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --     ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                       --     bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --     ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                       --     bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --     ≡⟨ ++-identityˡ (bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                       --     bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --     ∎ )
  --                       -- in
  --                       -- contradiction d' (nc₂₄ bs≡ (proj₁ b))
  --                   (singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → {!!}
  --                       -- let
  --                       --   @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --   bs≡ = (begin
  --                       --     bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                       --     ≡⟨ sym xs≡₁ ⟩
  --                       --     bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --     ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                       --     bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --     ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                       --     bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --     ≡⟨ ++-identityˡ (bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                       --     bs₅' ++ bs₆' ++ suffix
  --                       --     ∎ )
  --                       -- in
  --                       -- contradiction e' (nc₂₅ bs≡ (proj₁ b))
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → {!!}
  --                       -- let
  --                       --    @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --    bs≡ = (begin
  --                       --     bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --                       --     ≡⟨ sym xs≡₁ ⟩
  --                       --     bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --     ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --                       --     bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --     ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --                       --     bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --                       --     ≡⟨ ++-identityˡ (bs₆' ++ suffix)  ⟩
  --                       --     bs₆' ++ suffix
  --                       --     ∎ )
  --                       -- in
  --                       -- contradiction f' (nc₂₆ bs≡ (proj₁ b))
  --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl) → {!!}
  --                     -- contradiction (¡ abcdefLen) (λ ())
  --             (none , some a') → {!!}
  --               -- let
  --               --   @0 xs≡₁ : bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --   xs≡₁ = (begin
  --               --             bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
  --               --             ≡⟨ trans ps≡ (sym ps≡₁) ⟩
  --               --             (bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ∎ )    
  --               -- in
  --               -- case ((singleton ob refl) ,′e (singleton oc refl) ,′e (singleton od refl) ,′e (singleton oe refl) ,′e (singleton of refl)) 
  --               --   ret (const _) of λ where
  --               --     (singleton (some b) refl , singleton oc refl , singleton od refl , singleton oe refl , singleton of refl) →
  --               --       let
  --               --         @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --         bs≡ = (begin
  --               --             bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₁ ⟩
  --               --             bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --           contradiction b (nc₁₂ (sym bs≡) a')
  --               --     (singleton none refl , singleton (some c) refl , singleton od refl , singleton oe refl , singleton of refl) → 
  --               --         let
  --               --           @0 bs≡ : bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --           bs≡ = (begin
  --               --             bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₁ ⟩
  --               --             bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction c (nc₁₃ (sym bs≡) a')
  --               --     (singleton none refl , singleton none refl , singleton (some d) refl , singleton oe refl , singleton of refl) → 
  --               --         let
  --               --           @0 bs≡ : bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --           bs≡ = (begin
  --               --             bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₁ ⟩
  --               --             bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction d (nc₁₄ (sym bs≡) a')
  --               --     (singleton none refl , singleton none refl , singleton none refl , singleton (some e) refl , singleton of refl) → 
  --               --         let
  --               --           @0 bs≡ : bs₅ ++ bs₆ ++ suf₁ ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --           bs≡ = (begin
  --               --             bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₁ ⟩
  --               --             bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction e (nc₁₅ (sym bs≡) a')
  --               --     (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f) refl) → 
  --               --         let
  --               --           @0 bs≡ : bs₆ ++ suf₁ ≡ bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --           bs≡ = (begin
  --               --             bs₆ ++ suf₁
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₁ ⟩
  --               --             bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction f (nc₁₆ (sym bs≡) a')
  --               --     (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
  --               --       {!!}
  --             (some a , none) → {!!}
  --               -- let
  --               --   @0 xs≡₁ : bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix ≡ bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --   xs≡₁ = (begin
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆') ++ suffix
  --               --             ≡⟨ trans ps≡ (sym ps≡₁) ⟩
  --               --             (bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ∎ )     
  --               -- in
  --               -- case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  --               --   ret (const _) of λ where
  --               --     (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) → 
  --               --       let
  --               --         @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --         bs≡ = (begin
  --               --             bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₁ ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --           contradiction b' (nc₁₂ bs≡ a)
  --               --     (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) → 
  --               --         let
  --               --           @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --           bs≡ = (begin
  --               --             bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₁ ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction c' (nc₁₃ bs≡ a)
  --               --     (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → 
  --               --         let
  --               --           @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --           bs≡ = (begin
  --               --             bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₁ ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction d' (nc₁₄ bs≡ a)
  --               --     (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → 
  --               --         let
  --               --           @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --           bs≡ = (begin
  --               --             bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₁ ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction e' (nc₁₅ bs≡ a)
  --               --     (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → 
  --               --         let
  --               --           @0 bs≡ : bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --           bs≡ = (begin
  --               --             bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₁ ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₁' ++ bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix) ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₆' ++ suffix)  ⟩
  --               --             bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction f' (nc₁₆ bs≡ a)
  --               --     (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
  --               --       contradiction (¡ abcdefLen) λ where ()
  --             (some a , some a') → {!!}
  --               -- let
  --               --   @0 xs≡₁ : bs₁' ++ bs₂' ++ bs₃₄₅₆' ++ suffix ≡ bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --   xs≡₁ = (begin
  --               --               bs₁' ++ bs₂' ++ bs₃₄₅₆' ++ suffix
  --               --              ≡⟨ solve (++-monoid UInt8) ⟩
  --               --               (bs₁' ++ bs₂' ++ bs₃₄₅₆') ++ suffix
  --               --              ≡⟨ trans ps≡ (sym ps≡₁) ⟩
  --               --               (bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆) ++ suf₁
  --               --              ≡⟨ solve (++-monoid UInt8) ⟩
  --               --               bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --               ∎ )

  --               --   @0 bs₁≡ : bs₁' ≡ bs₁
  --               --   bs₁≡ = ns₁ xs≡₁ a' a

  --               --   @0 xs≡₂ : bs₂' ++ bs₃₄₅₆' ++ suffix ≡ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --   xs≡₂ = ++-cancelˡ bs₁'
  --               --              (begin
  --               --               bs₁' ++ bs₂' ++ bs₃₄₅₆' ++ suffix
  --               --              ≡⟨ xs≡₁ ⟩
  --               --               bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --              ≡⟨ cong (_++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁) (sym bs₁≡) ⟩
  --               --               bs₁' ++ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --               ∎ )
  --               -- in
  --               -- case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  --               --   ret (const _) of λ where
  --               --     (singleton (some b') refl , singleton ob' refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
  --               --       let                                           
  --               --         @0 bs₂≡ : bs₂' ≡ bs₂
  --               --         bs₂≡ = ns₂ xs≡₂ b' (proj₁  b)
  --               --       in
  --               --       case (‼ bs₂≡) ret (const _) of λ where
  --               --         refl →
  --               --           let @0 b≡ : proj₁ b ≡ b'
  --               --               b≡ = ub (proj₁ b) b'
  --               --           in
  --               --           contradiction
  --               --             (subst₀ (λ x → Default.NotDefault default₂ x) (cong some (sym (‼ b≡))) obnd)
  --               --             (proj₂ b)
  --               --     (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) →
  --               --         let
  --               --           @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --           bs≡ = (begin
  --               --             bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₂ ⟩
  --               --             bs₂' ++ bs₃₄₅₆' ++ suffix
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction c' (nc₂₃ bs≡ (proj₁ b))
  --               --     (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) →
  --               --         let
  --               --           @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --           bs≡ = (begin
  --               --             bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₂ ⟩
  --               --             bs₂' ++ bs₃₄₅₆' ++ suffix
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction d' (nc₂₄ bs≡ (proj₁ b))
  --               --     (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) →
  --               --         let
  --               --           @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --           bs≡ = (begin
  --               --             bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₂ ⟩
  --               --             bs₂' ++ bs₃₄₅₆' ++ suffix
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₅' ++ bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction e' (nc₂₅ bs≡ (proj₁ b))
  --               --     (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) →
  --               --         let
  --               --            @0 bs≡ : bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁ ≡ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --            bs≡ = (begin
  --               --             bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆ ++ suf₁
  --               --             ≡⟨ sym xs≡₂ ⟩
  --               --             bs₂' ++ bs₃₄₅₆' ++ suffix
  --               --             ≡⟨ solve (++-monoid UInt8) ⟩
  --               --             bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₂' ++ bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix)  ⟩
  --               --             bs₃' ++ bs₄' ++ bs₅' ++ bs₆' ++ suffix
  --               --             ≡⟨ ++-identityˡ (bs₆' ++ suffix)  ⟩
  --               --             bs₆' ++ suffix
  --               --             ∎ )
  --               --         in
  --               --         contradiction f' (nc₂₆ bs≡ (proj₁ b))
  --               --     (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) →
  --               --       {!!}
  --       (yes pb , yes pc , no ¬pe , f) → {!!}
  --       (yes pb , yes pc , yes pe , no ¬pf) → {!!}
  --       (yes pb , yes pc , yes pe , yes pf) →
  --         return (yes (success pre₁ _ r₁≡
  --                  (mk×ₚ (mk&ₚ oa (mk&ₚ (mkDefault ob pb) (mk&ₚ (mkDefault oc pc)
  --                         (mk&ₚ od (mk&ₚ (mkDefault oe pe) (mkDefault of pf)
  --                         refl) refl) refl) refl) refl) abcdefLen) suf₁ ps≡₁))



  -- -- parseOption₂Default₄
  -- --     : ∀ {A D : @0 List UInt8 → Set}
  -- --     → @0 Unambiguous A → @0 NoSubstrings A
  -- --     → @0 Unambiguous B → @0 NoSubstrings B
  -- --     → @0 Unambiguous C → @0 NoSubstrings C
  -- --     → @0 Unambiguous D → @0 NoSubstrings D
  -- --     → @0 Unambiguous E → @0 NoSubstrings E
  -- --     → @0 NoSubstrings F
  -- --     → @0 NoConfusion A B → @0 NoConfusion A C → @0 NoConfusion A D → @0 NoConfusion A E → @0 NoConfusion A F
  -- --     → @0 NoConfusion B C → @0 NoConfusion B D → @0 NoConfusion B E → @0 NoConfusion B F
  -- --     → @0 NoConfusion C D → @0 NoConfusion C E → @0 NoConfusion C F
  -- --     → @0 NoConfusion D E → @0 NoConfusion D F
  -- --     → @0 NoConfusion E F
  -- --     → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B → Parser (Logging ∘ Dec) C
  -- --     → Parser (Logging ∘ Dec) D → Parser (Logging ∘ Dec) E → Parser (Logging ∘ Dec) F
  -- --     → ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option A) (&ₚ (Default B default₂) (&ₚ(Default C default₃)
  -- --                                  (&ₚ (Option D) (&ₚ (Default E default₅) (Default F default₆)))))) n)
  -- -- runParser (parseOption₂Default₄ ua ns₁ ub ns₂ uc ns₃ ud ns₄ ue ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf zero) xs =
  -- --   return (yes (success [] _ refl (mk×ₚ (mk&ₚ none (mk&ₚ (mkDefault none tt) (mk&ₚ (mkDefault none tt) (mk&ₚ none (mk&ₚ (mkDefault none tt) (mkDefault none tt)
  -- --               refl) refl) refl) refl) refl) (─ refl)) xs refl))
  -- -- runParser (parseOption₂Default₄ ua ns₁ ub ns₂ uc ns₃ ud ns₄ ue ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf n@(suc _)) xs = do
  -- --   (yes (success pre₁ r₁ r₁≡ (mk×ₚ  (mk&ₚ {bs₁}{bs₂'} oa (mk&ₚ {bs₂}{bs₃'} ob (mk&ₚ {bs₃}{bs₄'} oc (mk&ₚ {bs₄}{bs₅'} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf₁ ps≡₁)) ←
  -- --     runParser (parse₂Option₆ loc ns₁ ns₂ ns₃ ns₄ ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf n) xs
  -- --     where no ¬p₁₂' → do
  -- --       tell $ loc String.++ ": failed to parse"
  -- --       return ∘ no $ λ where
  -- --         (success prefix read read≡ (mk×ₚ  (mk&ₚ oa (mk&ₚ (mkDefault ob _) (mk&ₚ (mkDefault oc _) (mk&ₚ od (mk&ₚ (mkDefault oe _) (mkDefault of _)
  -- --           refl) refl) refl) refl) refl) abcdefLen) suffix ps≡) →
  -- --           contradiction
  -- --             (success prefix _ read≡ (mk×ₚ  (mk&ₚ oa (mk&ₚ ob (mk&ₚ oc (mk&ₚ od (mk&ₚ oe of refl) refl) refl) refl) refl) abcdefLen) suffix ps≡) ¬p₁₂'
  -- --   case (Default.notDefault? default₂ ob)  ,′e (Default.notDefault?  default₃ oc ,′e (Default.notDefault?  default₅ oe ,′e Default.notDefault? default₆ of))
  -- --     ret const _ of λ where
  -- --       (no ¬pb , c , e , f) → return ∘ no $ λ where
  -- --         (success prefix read read≡
  -- --           (mk×ₚ
  -- --             (mk&ₚ {bs₁ = bs₁'} {bs₂ = bs₂₃₄₅₆'} oa'
  -- --             (mk&ₚ {bs₁ = bs₂'} {bs₂ = bs₃₄₅₆'} (mkDefault ob' obnd)
  -- --             (mk&ₚ {bs₁ = bs₃'} {bs₂ = bs₄₅₆'} (mkDefault oc' ocnd)
  -- --             (mk&ₚ {bs₁ = bs₄'} {bs₂ = bs₅₆'} od'
  -- --             (mk&ₚ {bs₁ = bs₅'} {bs₂ = bs₆'} (mkDefault oe' oend)
  -- --                    (mkDefault of' ofnd) refl) refl) refl) refl) refl) abcdefLen)
  -- --           suffix ps≡) →
  -- --           case (oa ,′e oa') ret (const _) of λ where
  -- --             (none , none) →
  -- --               case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  -- --                 ret (const _) of λ where
  -- --                   (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --                   (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → {!!} 
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) → {!!}
  -- --             (none , some a') →
  -- --               case ((singleton ob refl) ,′e (singleton oc refl) ,′e (singleton od refl) ,′e (singleton oe refl) ,′e (singleton of refl)) 
  -- --                 ret (const _) of λ where
  -- --                   (singleton (some b) refl , singleton oc refl , singleton od refl , singleton oe refl , singleton of refl) → {!!}
  -- --                   (singleton none refl , singleton (some c) refl , singleton od refl , singleton oe refl , singleton of refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton (some d) refl , singleton oe refl , singleton of refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton (some e) refl , singleton of refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f) refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) → {!!}
  -- --             (some a , none) →
  -- --               case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  -- --                 ret (const _) of λ where
  -- --                   (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --                   (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) → {!!}
  -- --             (some a , some a') →
  -- --               case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  -- --                 ret (const _) of λ where
  -- --                   (singleton (some b') refl , singleton ob' refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --                   (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → {!!} 
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → {!!}
  -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) → {!!}
  -- --       (yes pb , no ¬pc , e , f) → return ∘ no $ λ where
  -- --         (success prefix read read≡
  -- --           (mk×ₚ
  -- --             (mk&ₚ {bs₁ = bs₁'} {bs₂ = bs₂₃₄₅₆'} oa'
  -- --             (mk&ₚ {bs₁ = bs₂'} {bs₂ = bs₃₄₅₆'} (mkDefault ob' obnd)
  -- --             (mk&ₚ {bs₁ = bs₃'} {bs₂ = bs₄₅₆'} (mkDefault oc' ocnd)
  -- --             (mk&ₚ {bs₁ = bs₄'} {bs₂ = bs₅₆'} od'
  -- --             (mk&ₚ {bs₁ = bs₅'} {bs₂ = bs₆'} (mkDefault oe' oend)
  -- --                    (mkDefault of' ofnd) refl) refl) refl) refl) refl) abcdefLen)
  -- --           suffix ps≡) →
  -- --           case (oa ,′e oa') ret (const _) of λ where
  -- --             v → ?
  -- --             -- (none , none) →
  -- --             --   case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  -- --             --     ret (const _) of λ where
  -- --             --       (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --             --       (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → {!!} 
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) → {!!}
  -- --             -- (none , some a') →
  -- --             --   case ((singleton ob refl) ,′e (singleton oc refl) ,′e (singleton od refl) ,′e (singleton oe refl) ,′e (singleton of refl)) 
  -- --             --     ret (const _) of λ where
  -- --             --       (singleton (some b) refl , singleton oc refl , singleton od refl , singleton oe refl , singleton of refl) → {!!}
  -- --             --       (singleton none refl , singleton (some c) refl , singleton od refl , singleton oe refl , singleton of refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton (some d) refl , singleton oe refl , singleton of refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton (some e) refl , singleton of refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f) refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) → {!!}
  -- --             -- (some a , none) →
  -- --             --   case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  -- --             --     ret (const _) of λ where
  -- --             --       (singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --             --       (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) → {!!}
  -- --             -- (some a , some a') →
  -- --             --   case ((singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  -- --             --     ret (const _) of λ where
  -- --             --       (singleton (some b') refl , singleton ob' refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --             --       (singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → {!!} 
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → {!!}
  -- --             --       (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) → {!!}
  -- --       (yes pb , yes pc , no ¬pe , f) → {!!}
  -- --       (yes pb , yes pc , yes pe , no ¬pf) → {!!}
  -- --       (yes pb , yes pc , yes pe , yes pf) → {!!}













  -- -- -- parseOption₂Default₄
  -- -- --     : ∀ {A D : @0 List UInt8 → Set}
  -- -- --     → @0 Unambiguous A → @0 NoSubstrings A
  -- -- --     → @0 Unambiguous B → @0 NoSubstrings B
  -- -- --     → @0 Unambiguous C → @0 NoSubstrings C
  -- -- --     → @0 Unambiguous D → @0 NoSubstrings D
  -- -- --     → @0 Unambiguous E → @0 NoSubstrings E
  -- -- --     → @0 NoSubstrings F
  -- -- --     → @0 NoConfusion A B → @0 NoConfusion A C → @0 NoConfusion A D → @0 NoConfusion A E → @0 NoConfusion A F
  -- -- --     → @0 NoConfusion B C → @0 NoConfusion B D → @0 NoConfusion B E → @0 NoConfusion B F
  -- -- --     → @0 NoConfusion C D → @0 NoConfusion C E → @0 NoConfusion C F
  -- -- --     → @0 NoConfusion D E → @0 NoConfusion D F
  -- -- --     → @0 NoConfusion E F
  -- -- --     → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B → Parser (Logging ∘ Dec) C
  -- -- --     → Parser (Logging ∘ Dec) D → Parser (Logging ∘ Dec) E → Parser (Logging ∘ Dec) F
  -- -- --     → ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option A) (&ₚ (Default B default₂) (&ₚ(Default C default₃)
  -- -- --                                  (&ₚ (Option D) (&ₚ (Default E default₅) (Default F default₆)))))) n)
  -- -- -- runParser (parseOption₂Default₄ ua ns₁ ub ns₂ uc ns₃ ud ns₄ ue ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf zero) xs =
  -- -- --   return (yes (success [] _ refl (mk×ₚ (mk&ₚ none (mk&ₚ (mkDefault none tt) (mk&ₚ (mkDefault none tt) (mk&ₚ none (mk&ₚ (mkDefault none tt) (mkDefault none tt)
  -- -- --               refl) refl) refl) refl) refl) (─ refl)) xs refl))
  -- -- -- runParser (parseOption₂Default₄ ua ns₁ ub ns₂ uc ns₃ ud ns₄ ue ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf n@(suc _)) xs = do
  -- -- --   (yes (success pre₁ r₁ r₁≡ (mk×ₚ  (mk&ₚ {bs₁}{bs₂'} oa (mk&ₚ {bs₂}{bs₃'} ob (mk&ₚ {bs₃}{bs₄'} oc (mk&ₚ {bs₄}{bs₅'} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf₁ ps≡₁)) ←
  -- -- --     runParser (parse₂Option₆ loc ns₁ ns₂ ns₃ ns₄ ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf n) xs
  -- -- --     where no ¬p₁₂' → do
  -- -- --       tell $ loc String.++ ": failed to parse"
  -- -- --       return ∘ no $ λ where
  -- -- --         (success prefix read read≡ (mk×ₚ  (mk&ₚ oa (mk&ₚ (mkDefault ob _) (mk&ₚ (mkDefault oc _) (mk&ₚ od (mk&ₚ (mkDefault oe _) (mkDefault of _)
  -- -- --           refl) refl) refl) refl) refl) abcdefLen) suffix ps≡) →
  -- -- --           contradiction
  -- -- --             (success prefix _ read≡ (mk×ₚ  (mk&ₚ oa (mk&ₚ ob (mk&ₚ oc (mk&ₚ od (mk&ₚ oe of refl) refl) refl) refl) refl) abcdefLen) suffix ps≡) ¬p₁₂'
  -- -- --   case Default.notDefault? default₂ ob ret (const _) of λ where
  -- -- --     (no ¬pb) →
  -- -- --       case Default.notDefault? default₃ oc ret (const _) of λ where
  -- -- --         (no ¬pc) →
  -- -- --           case Default.notDefault? default₅ oe ret (const _) of λ where
  -- -- --             (no ¬pe) →
  -- -- --               case Default.notDefault? default₆ of ret (const _) of λ where
  -- -- --                 (no ¬pf) → do
  -- -- --                            return ∘ no $ λ where
  -- -- --                              (success prefix read read≡  (mk×ₚ (mk&ₚ (some a') _ refl) abcdefLen) suffix ps≡) → {!!}
  -- -- --                              (success prefix read read≡  (mk×ₚ (mk&ₚ none (mk&ₚ (mkDefault (some b') pb) _ refl) refl) abcdefLen) suffix ps≡) → {!!}
  -- -- --                              (success prefix read read≡  (mk×ₚ (mk&ₚ none (mk&ₚ (mkDefault none pb) (mk&ₚ (mkDefault (some c') pc) _ refl) refl) refl) abcdefLen) suffix ps≡) → {!!}
  -- -- --                              (success prefix read read≡  (mk×ₚ (mk&ₚ none (mk&ₚ (mkDefault none pb) (mk&ₚ (mkDefault none pc) (mk&ₚ (some d') _ refl) refl) refl) refl) abcdefLen) suffix ps≡) → {!!}
  -- -- --                              (success prefix read read≡  (mk×ₚ (mk&ₚ none (mk&ₚ (mkDefault none pb) (mk&ₚ (mkDefault none pc) (mk&ₚ none
  -- -- --                                                                 (mk&ₚ (mkDefault (some e') pe) _ refl) refl) refl) refl) refl) abcdefLen) suffix ps≡) → {!!}
  -- -- --                              (success prefix read read≡  (mk×ₚ (mk&ₚ none (mk&ₚ (mkDefault none pb) (mk&ₚ (mkDefault none pc) (mk&ₚ none
  -- -- --                                                                 (mk&ₚ (mkDefault none pe) (mkDefault (some f') pf) refl) refl) refl) refl) refl) abcdefLen) suffix ps≡) → {!!}
  -- -- --                              (success prefix read read≡  (mk×ₚ (mk&ₚ none (mk&ₚ (mkDefault none pb) (mk&ₚ (mkDefault none pc) (mk&ₚ none
  -- -- --                                                                 (mk&ₚ (mkDefault none pe) (mkDefault none pf) refl) refl) refl) refl) refl) abcdefLen) suffix ps≡) → {!!}
  -- -- --                 (yes pf) → {!!}
  -- -- --             (yes pe) →
  -- -- --               case Default.notDefault? default₆ of ret (const _) of λ where
  -- -- --                 (no ¬pf) → {!!}
  -- -- --                 (yes pf) → {!!}
  -- -- --         (yes pc) →
  -- -- --           case Default.notDefault? default₅ oe ret (const _) of λ where
  -- -- --             (no ¬pe) →
  -- -- --               case Default.notDefault? default₆ of ret (const _) of λ where
  -- -- --                 (no ¬pf) → {!!}
  -- -- --                 (yes pf) → {!!}
  -- -- --             (yes pe) →
  -- -- --               case Default.notDefault? default₆ of ret (const _) of λ where
  -- -- --                 (no ¬pf) → {!!}
  -- -- --                 (yes pf) → {!!}
  -- -- --     (yes pb) →
  -- -- --       case Default.notDefault? default₃ oc ret (const _) of λ where
  -- -- --         (no ¬pc) →
  -- -- --           case Default.notDefault? default₅ oe ret (const _) of λ where
  -- -- --             (no ¬pe) →
  -- -- --               case Default.notDefault? default₆ of ret (const _) of λ where
  -- -- --                 (no ¬pf) → {!!}
  -- -- --                 (yes pf) → {!!}
  -- -- --             (yes pe) →
  -- -- --               case Default.notDefault? default₆ of ret (const _) of λ where
  -- -- --                 (no ¬pf) → {!!}
  -- -- --                 (yes pf) → {!!}
  -- -- --         (yes pc) →
  -- -- --           case Default.notDefault? default₅ oe ret (const _) of λ where
  -- -- --             (no ¬pe) →
  -- -- --               case Default.notDefault? default₆ of ret (const _) of λ where
  -- -- --                 (no ¬pf) → {!!}
  -- -- --                 (yes pf) → {!!}
  -- -- --             (yes pe) →
  -- -- --               case Default.notDefault? default₆ of ret (const _) of λ where
  -- -- --                 (no ¬pf) → return ∘ no $ λ where
  -- -- --                                     (success pre₁ _ r₁≡
  -- -- --                                         (mk×ₚ
  -- -- --                                           (mk&ₚ {bs₁ = bs₁'} {bs₂ = bs₂₃₄₅₆'} oa
  -- -- --                                           (mk&ₚ {bs₁ = bs₂'} {bs₂ = bs₃₄₅₆'} (mkDefault ob pb)
  -- -- --                                           (mk&ₚ {bs₁ = bs₃'} {bs₂ = bs₄₅₆'} (mkDefault oc pc)
  -- -- --                                           (mk&ₚ {bs₁ = bs₄'} {bs₂ = bs₅₆'} od
  -- -- --                                           (mk&ₚ {bs₁ = bs₅'} {bs₂ = bs₆'} (mkDefault oe pr)
  -- -- --                                                                            (mkDefault of pf) refl) refl) refl) refl) refl) abcdefLen) suf₁ ps≡₁) → contradiction pf {!¬pf!}
  -- -- --                 (yes pf) → return (yes (success pre₁ _ r₁≡
  -- -- --                                        (mk×ₚ (mk&ₚ oa (mk&ₚ (mkDefault ob pb) (mk&ₚ (mkDefault oc pc)
  -- -- --                                               (mk&ₚ od (mk&ₚ (mkDefault oe pe) (mkDefault of pf)
  -- -- --                                                 refl) refl) refl) refl) refl) abcdefLen) suf₁ ps≡₁))




  -- -- -- parseOption₂Default₄
  -- -- --     : ∀ {A D : @0 List UInt8 → Set}
  -- -- --     → @0 Unambiguous A → @0 NoSubstrings A
  -- -- --     → @0 Unambiguous B → @0 NoSubstrings B
  -- -- --     → @0 Unambiguous C → @0 NoSubstrings C
  -- -- --     → @0 Unambiguous D → @0 NoSubstrings D
  -- -- --     → @0 Unambiguous E → @0 NoSubstrings E
  -- -- --     → @0 NoSubstrings F
  -- -- --     → @0 NoConfusion A B → @0 NoConfusion A C → @0 NoConfusion A D → @0 NoConfusion A E → @0 NoConfusion A F
  -- -- --     → @0 NoConfusion B C → @0 NoConfusion B D → @0 NoConfusion B E → @0 NoConfusion B F
  -- -- --     → @0 NoConfusion C D → @0 NoConfusion C E → @0 NoConfusion C F
  -- -- --     → @0 NoConfusion D E → @0 NoConfusion D F
  -- -- --     → @0 NoConfusion E F
  -- -- --     → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B → Parser (Logging ∘ Dec) C
  -- -- --     → Parser (Logging ∘ Dec) D → Parser (Logging ∘ Dec) E → Parser (Logging ∘ Dec) F
  -- -- --     → ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option A) (&ₚ (Default B default₂) (&ₚ(Default C default₃)
  -- -- --                                  (&ₚ (Option D) (&ₚ (Default E default₅) (Default F default₆)))))) n)
  -- -- -- runParser (parseOption₂Default₄ ua ns₁ ub ns₂ uc ns₃ ud ns₄ ue ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf zero) xs =
  -- -- --   return (yes (success [] _ refl (mk×ₚ (mk&ₚ none (mk&ₚ (mkDefault none tt) (mk&ₚ (mkDefault none tt) (mk&ₚ none (mk&ₚ (mkDefault none tt) (mkDefault none tt)
  -- -- --               refl) refl) refl) refl) refl) (─ refl)) xs refl))
  -- -- -- runParser (parseOption₂Default₄ ua ns₁ ub ns₂ uc ns₃ ud ns₄ ue ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf n@(suc _)) xs = do
  -- -- --   (yes (success pre₁ r₁ r₁≡ (mk×ₚ  (mk&ₚ {bs₁}{bs₂'} oa (mk&ₚ {bs₂}{bs₃'} ob (mk&ₚ {bs₃}{bs₄'} oc (mk&ₚ {bs₄}{bs₅'} od (mk&ₚ {bs₅}{bs₆} oe of refl) refl) refl) refl) refl) abcdefLen) suf₁ ps≡₁)) ←
  -- -- --     runParser (parse₂Option₆ loc ns₁ ns₂ ns₃ ns₄ ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ pa pb pc pd pe pf n) xs
  -- -- --     where no ¬p₁₂' → do
  -- -- --       tell $ loc String.++ ": failed to parse"
  -- -- --       return ∘ no $ λ where
  -- -- --         (success prefix read read≡ (mk×ₚ  (mk&ₚ oa (mk&ₚ (mkDefault ob _) (mk&ₚ (mkDefault oc _) (mk&ₚ od (mk&ₚ (mkDefault oe _) (mkDefault of _)
  -- -- --           refl) refl) refl) refl) refl) abcdefLen) suffix ps≡) →
  -- -- --           contradiction
  -- -- --             (success prefix _ read≡ (mk×ₚ  (mk&ₚ oa (mk&ₚ ob (mk&ₚ oc (mk&ₚ od (mk&ₚ oe of refl) refl) refl) refl) refl) abcdefLen) suffix ps≡) ¬p₁₂'
  -- -- --   case (Default.notDefault? default₂ ob)  ,′e (Default.notDefault?  default₃ oc ,′e (Default.notDefault?  default₅ oe ,′e Default.notDefault? default₆ of))
  -- -- --     ret const _ of λ where
  -- -- --       (no ¬pb , c , e , f) → return ∘ no $ λ where
  -- -- --         (success prefix read read≡
  -- -- --           (mk×ₚ
  -- -- --             (mk&ₚ {bs₁ = bs₁'} {bs₂ = bs₂₃₄₅₆'} oa'
  -- -- --             (mk&ₚ {bs₁ = bs₂'} {bs₂ = bs₃₄₅₆'} (mkDefault ob' obnd)
  -- -- --             (mk&ₚ {bs₁ = bs₃'} {bs₂ = bs₄₅₆'} (mkDefault oc' ocnd)
  -- -- --             (mk&ₚ {bs₁ = bs₄'} {bs₂ = bs₅₆'} od'
  -- -- --             (mk&ₚ {bs₁ = bs₅'} {bs₂ = bs₆'} (mkDefault oe' oend)
  -- -- --                    (mkDefault of' ofnd) refl) refl) refl) refl) refl) abcdefLen)
  -- -- --           suffix ps≡) →
  -- -- --           let b : Σ (B bs₂) (λ b → ¬ Default.NotDefault default₂ (some b))
  -- -- --               b = case (Singleton ob ∋ singleton ob refl) ret (const _) of λ where
  -- -- --                 (singleton none refl) → contradiction tt ¬pb
  -- -- --                 (singleton (some x) refl) → (x , ¬pb)
  -- -- --           in
  -- -- --           case ((singleton oa' refl) ,′e (singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  -- -- --                 ret (const _) of λ where
  -- -- --                   (singleton (some a') refl , singleton ob' refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- -- --                   (singleton none refl , singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- -- --                   (singleton none refl , singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → {!!} 
  -- -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → {!!}
  -- -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → {!!}
  -- -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) → {!!}
  -- -- --       (yes pb , no ¬pc , e , f) → return ∘ no $ λ where
  -- -- --         (success prefix read read≡
  -- -- --           (mk×ₚ
  -- -- --             (mk&ₚ {bs₁ = bs₁'} {bs₂ = bs₂₃₄₅₆'} oa'
  -- -- --             (mk&ₚ {bs₁ = bs₂'} {bs₂ = bs₃₄₅₆'} (mkDefault ob' obnd)
  -- -- --             (mk&ₚ {bs₁ = bs₃'} {bs₂ = bs₄₅₆'} (mkDefault oc' ocnd)
  -- -- --             (mk&ₚ {bs₁ = bs₄'} {bs₂ = bs₅₆'} od'
  -- -- --             (mk&ₚ {bs₁ = bs₅'} {bs₂ = bs₆'} (mkDefault oe' oend)
  -- -- --                    (mkDefault of' ofnd) refl) refl) refl) refl) refl) abcdefLen)
  -- -- --           suffix ps≡) →
  -- -- --           let c : Σ (C bs₃) (λ c → ¬ Default.NotDefault default₃ (some c))
  -- -- --               c = case (Singleton oc ∋ singleton oc refl) ret (const _) of λ where
  -- -- --                 (singleton none refl) → contradiction tt ¬pc
  -- -- --                 (singleton (some x) refl) → (x , ¬pc)
  -- -- --           in
  -- -- --            case ((singleton oa' refl) ,′e (singleton ob' refl) ,′e (singleton oc' refl) ,′e (singleton od' refl) ,′e (singleton oe' refl) ,′e (singleton of' refl)) 
  -- -- --                 ret (const _) of λ where
  -- -- --                   (singleton (some a') refl , singleton ob' refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- -- --                   (singleton none refl , singleton (some b') refl , singleton oc' refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- -- --                   (singleton none refl , singleton none refl , singleton (some c') refl , singleton od' refl , singleton oe' refl , singleton of' refl) → {!!}
  -- -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton (some d') refl , singleton oe' refl , singleton of' refl) → {!!} 
  -- -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some e') refl , singleton of' refl) → {!!}
  -- -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton (some f') refl) → {!!}
  -- -- --                   (singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl , singleton none refl) → {!!}
  -- -- --       (yes pb , yes pc , no ¬pe , f) → {!!}
  -- -- --       (yes pb , yes pc , yes pe , no ¬pf) → {!!}
  -- -- --       (yes pb , yes pc , yes pe , yes pf) → {!!}

  --   where
  --   open ≡-Reasoning
