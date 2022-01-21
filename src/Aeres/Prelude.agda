module Aeres.Prelude where

open import Data.Bool    public
  hiding (_<_ ; _<?_ ; _≟_ ; _≤_ ; _≤?_)

open import Data.Empty public
  hiding (⊥-elim)

⊥-elim : ∀ {ℓ} {A : Set ℓ} → (@0 _ : ⊥) → A
⊥-elim ()

⊥-irrel : (@0 _ : ⊥) → ⊥
⊥-irrel ()

import Data.Char
module Char = Data.Char
Char = Char.Char

import Data.Fin
module Fin where
  open Data.Fin public

  open import Data.Nat
    renaming (_+_ to _+ℕ_ ; pred to predℕ)
  open import Data.Nat.Properties

  2*_ : ∀ {m} → Fin m → Fin (predℕ (2 * m))
  2*_  (zero{n}) rewrite +-suc n (n +ℕ 0) = zero
  2* suc {suc n} i rewrite +-suc n (suc (n +ℕ 0)) =
    suc (suc (2* i))

  open import Data.Fin.Properties public

Fin = Fin.Fin

import Data.Integer
module ℤ = Data.Integer
ℤ = ℤ.ℤ

open import Data.List    public
  hiding (_─_)

open import Data.List.Properties public

open import Data.List.Relation.Unary.All
  using ([] ; _∷_)
module All = Data.List.Relation.Unary.All
All = All.All

open import Data.List.Relation.Unary.Any public
  using (here ; there)
module Any = Data.List.Relation.Unary.Any
Any = Any.Any

open import Data.List.Membership.Propositional public
  using (_∈_ ; _∉_)

import Data.List.Membership.DecPropositional

-- import Data.Maybe
-- module Maybe = Data.Maybe
-- open Data.Maybe public
--   hiding (align ; alignWith ; fromMaybe ; map ; zip ; zipWith ; _>>=_)

import Data.Maybe
module Maybe where
  open Data.Maybe public
open Maybe public
  hiding (module Maybe ; align ; alignWith ; fromMaybe ; map ; zip ; zipWith ; _>>=_)

open import Data.Nat     public
  hiding (_≟_)
open import Data.Nat.DivMod public
open import Agda.Builtin.Nat public
  using (_-_)

open import Data.Product public
  hiding (map ; zip)

import Data.String
module String where
  open Data.String public
  open import Agda.Builtin.String public
    using ()
    renaming (primShowNat to showNat)
String = String.String

open import Data.Sum     public
  hiding (map ; map₁ ; map₂ ; swap ; assocʳ ; assocˡ)

open import Data.Unit    public
  using (⊤ ; tt)

open import Data.Vec public
  using (_∷_ ; [])
module Vec = Data.Vec
Vec = Vec.Vec

open import Function     public
  hiding (_∋_)

infix  0 case_ret_of_
infixl 0 _∋_

case_ret_of_ : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁}
               → (x : A) (@0 B : A → Set ℓ₂)
               → ((x : A) → B x) → B x
case a ret B of f = f a

_∋_ : ∀ {ℓ} (@0 A : Set ℓ) → A → A
A ∋ a = a

import Induction.WellFounded
module WellFounded where
  open Induction.WellFounded public
Acc = WellFounded.Acc

module Level where
  open import Level public

open import Relation.Binary public
  using ()
  renaming (Irrelevant to Unique₂)

open import Relation.Binary.PropositionalEquality public
  hiding (decSetoid ; cong)
  renaming ([_] to [_]R)
module Reveal = Reveal_·_is_

≡-unique : ∀ {ℓ} {A : Set ℓ} → Unique₂ (_≡_{A = A})
≡-unique refl refl = refl

≡-irrel : ∀ {ℓ} {A : Set ℓ} {x y : A} → (@0 _ : x ≡ y) → x ≡ y
≡-irrel refl = refl

≡-elim : ∀ {ℓ ℓ₁}{A : Set ℓ}{x : A} →
         (@0 P : ∀ {y} → x ≡ y → Set ℓ₁) →
         P refl → ∀ {y} (eq : x ≡ y) → P eq
≡-elim P pf refl = pf

≡-elimₖ : ∀ {ℓ ℓ₁}{A : Set ℓ}{x : A} →
          (@0 P : x ≡ x → Set ℓ₁) →
          P refl → (eq : x ≡ x) → P eq
≡-elimₖ P pf refl = pf

cong : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {@0 x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst₀ : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁} (@0 P : A → Set ℓ₂) {@0 x y : A} → (@0 _ : x ≡ y) → P x → P y
subst₀ P refl x = x

trans₀ : ∀ {ℓ} {@0 A : Set ℓ} {@0 x y z : A} → (@0 _ : x ≡ y) (@0 _ : y ≡ z) → x ≡ z
trans₀ refl refl = refl

open import Relation.Binary.Definitions public
  using (Tri ; tri< ; tri≈ ; tri> )

open import Relation.Nullary public
  renaming (Irrelevant to Unique)

×-unique : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → Unique A → Unique B → Unique (A × B)
×-unique ua ub (a , b) (c , d)
  with ua a c
  |    ub b d
... | refl | refl = refl

open import Relation.Nullary.Negation public
  hiding (contradiction)

contradiction : ∀ {ℓ ℓ'} {@0 P : Set ℓ} {A : Set ℓ'} → (@0 _ : P) (@0 _ : ¬ P) → A
contradiction p ¬p = ⊥-elim (¬p p)

open import Relation.Nullary.Decidable public
  hiding (map)

T-unique : ∀ {b} → Unique (T b)
T-unique {true} tt tt = refl

T-dec : ∀ {b} → Dec (T b)
T-dec {false} = no λ ()
T-dec {true} = yes tt

open import Relation.Nullary.Product public
  using (_×-dec_)

open import Relation.Nullary.Sum public
  using (_⊎-dec_)

open import Relation.Unary public
  using (Decidable)

-- Definitions
infixl 7 _%2^_
_%2^_ : (m n : ℕ) → ℕ
m %2^ n = _%_ m (2 ^ n) {fromWitnessFalse {Q = 2 ^ n Data.Nat.≟ 0} (λ eq → case 2 ≡ 0 ∋ m^n≡0⇒m≡0 2 n eq of λ ())}
  where open import Data.Nat.Properties


record Singleton {ℓ} {@0 A : Set ℓ} (@0 a : A) : Set ℓ where
  constructor singleton
  field
    x : A
    @0 x≡ : x ≡ a

pattern self {a} = singleton a refl

singleSelf : ∀ {ℓ} {@0 A : Set ℓ} → {a : A} → Singleton a
singleSelf{a = a} = singleton a refl

uniqueSingleton : ∀ {ℓ} {@0 A : Set ℓ} {a : A} → Unique (Singleton a)
uniqueSingleton self self = refl

infix 100 ─_
record Erased {ℓ} (@0 A : Set ℓ) : Set ℓ where
  constructor ─_
  field
    @0 x : A

erased? : ∀ {ℓ} {@0 A : Set ℓ} → Dec A → Dec (Erased A)
erased? (no ¬a) = no λ where
  (─ x) → contradiction x ¬a
erased? (yes a) = yes (─ a)

erased-unique : ∀ {ℓ} {@0 A : Set ℓ} → Unique A → Unique (Erased A)
erased-unique u (─ x) (─ y) = subst₀ (λ y → ─ x ≡ ─ y) (u x y) refl

Exists─ : (A : Set) (B : @0 A → Set) → Set
Exists─ A B = Σ[ x ∈ Erased A ] let (─ y) = x in B y

-- Typeclasses

record Numeric {ℓ} (A : Set ℓ) : Set ℓ where
  field
    toℕ : A → ℕ
open Numeric ⦃ ... ⦄ public

infix 10 #_
#_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Numeric A ⦄
     → (m : A) {n : ℕ} {m<n : True (suc (toℕ m) ≤? n) } → Fin n
#_ _ {m<n = m<n} = Fin.fromℕ< (toWitness m<n)

InRange : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} ⦃ _ : Numeric A ⦄ ⦃ _ : Numeric B ⦄
          → (l u : A) → B → Set
InRange l u x = toℕ l ≤ toℕ x × toℕ x ≤ toℕ u

inRange? : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} ⦃ _ : Numeric A ⦄ ⦃ _ : Numeric B ⦄
          → (l u : A)
          → (x : B) → Dec (InRange l u x)
inRange? l u x = toℕ l ≤? toℕ x ×-dec toℕ x ≤? toℕ u

inRange-unique : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} ⦃ _ : Numeric A ⦄ ⦃ _ : Numeric B ⦄
                 → ∀ {l u : A} {x : B}
                 → (pf₁ pf₂ : InRange l u x) → pf₁ ≡ pf₂
inRange-unique = ×-unique ≤-irrelevant ≤-irrelevant
  where open import Data.Nat.Properties

instance
  ℕNumeric : Numeric ℕ
  Numeric.toℕ ℕNumeric = id

  BoolNumeric : Numeric Bool
  Numeric.toℕ BoolNumeric false = 0
  Numeric.toℕ BoolNumeric true = 1

  FinNumeric : ∀ {n} → Numeric (Fin n)
  Numeric.toℕ FinNumeric = Fin.toℕ

  CharNumeric : Numeric Char
  Numeric.toℕ CharNumeric = Char.toℕ

record Eq {ℓ} (A : Set ℓ) : Set ℓ where
  infix 4 _≟_ _≠_
  field
    _≟_ : (x y : A) → Dec (x ≡ y)

  _≠_ : (x y : A) → Dec (x ≢ y)
  x ≠ y
    with x ≟ y
  ... | no  ≠  = yes ≠
  ... | yes pf = no (_$ pf)

open Eq ⦃ ... ⦄ public

infix 4 _∈?_ _∉?_

_∈?_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → ∀ (x : A) xs → Dec (x ∈ xs)
_∈?_ = Data.List.Membership.DecPropositional._∈?_ _≟_

_∉?_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → ∀ (x : A) xs → Dec (x ∉ xs)
_∉?_ = Data.List.Membership.DecPropositional._∉?_ _≟_

instance
  ℕEq : Eq ℕ
  Eq._≟_ ℕEq = Data.Nat._≟_

  CharEq : Eq Char
  Eq._≟_ CharEq = Char._≟_

  FinEq : ∀ {n} → Eq (Fin n)
  Eq._≟_ FinEq = Fin._≟_

  ℤEq : Eq ℤ
  Eq._≟_ ℤEq = ℤ._≟_

  ListEq : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → Eq (List A)
  Eq._≟_ ListEq = ≡-dec _≟_

record Sized {ℓ} (@0 A : Set ℓ) : Set ℓ where
  field
    sizeOf : A → ℕ
open Sized ⦃ ... ⦄ public

record Irrel {ℓ} (@0 A : Set ℓ) : Set ℓ where
  infix 10 ‼_
  field
    irrel : (@0 _ : A) → A
  ‼_ = irrel
open Irrel ⦃ ... ⦄ public
infix 10 ̂‼_
̂‼_ : ∀ {ℓ} {@0 A : Set ℓ} → ⦃ _ : Irrel A ⦄ → Erased A → A
̂‼ (─ x) = ‼ x

instance
  IrrelBot : Irrel ⊥
  Irrel.irrel IrrelBot = ⊥-irrel

  Irrel≡ : ∀ {ℓ} {@0 A : Set ℓ} {@0 x y : A} → Irrel (x ≡ y)
  Irrel.irrel Irrel≡ refl = refl

  Irrel¬ : ∀ {ℓ} {A : Set ℓ} → Irrel (¬ A)
  Irrel.irrel Irrel¬ ¬a a = contradiction a ¬a

import Category.Monad
Monad = Category.Monad.RawMonad
MonadZero = Category.Monad.RawMonadZero

module Monad {ℓ} {M : Set ℓ → Set ℓ} (m : Monad M) where
  open Category.Monad.RawMonad m public
    hiding (zip ; zipWith)

open Monad ⦃ ... ⦄ public

instance
  MonadMaybe : ∀ {ℓ} → Monad{ℓ} Maybe
  MonadMaybe = monad
    where open import Data.Maybe.Categorical

module MonadZero {ℓ} {M : Set ℓ → Set ℓ} (m : MonadZero M) where
  import Category.Monad

  ∅ = Category.Monad.RawMonadZero.∅ m

open MonadZero ⦃ ... ⦄ public

instance
  MonadZeroMaybe : ∀ {ℓ} → MonadZero{ℓ} Maybe
  MonadZeroMaybe = monadZero
    where open import Data.Maybe.Categorical

record Writer {ℓ} (M : Set ℓ → Set ℓ) (W : Set ℓ) : Set ℓ where
  field
    tell : W → M (Level.Lift _ ⊤)

open Writer ⦃ ... ⦄ public

record Logging {ℓ} (A : Set ℓ) : Set ℓ where
  constructor mkLogged
  field
    log : List String.String
    val : A

instance
  MonadLogging : ∀ {ℓ} → Monad{ℓ} Logging
  Monad.return MonadLogging x = mkLogged [] x
  Monad._>>=_  MonadLogging (mkLogged log₁ val₁) f
    with f val₁
  ... | mkLogged log₂ val₂ = mkLogged (log₁ ++ log₂) val₂

  WriterLogging : Writer Logging String.String
  Writer.tell   WriterLogging w = mkLogged [ w String.++ "\n" ] (Level.lift tt)

-- Lemmas
module Lemmas where

  open import Tactic.MonoidSolver using (solve ; solve-macro)
  open import Data.Nat.Properties
  open import Data.List.Properties

  m+n-m≡n : ∀ {m n} → m ≤ n → m + (n - m) ≡ n
  m+n-m≡n{m}{n} m≤n = begin
    m + (n - m) ≡⟨ sym $ +-∸-assoc m m≤n ⟩
    m + n - m ≡⟨ cong (_∸ m) (+-comm m n) ⟩
    n + m - m ≡⟨ +-∸-assoc n {m} ≤-refl ⟩
    n + (m - m) ≡⟨ cong (n +_) (n∸n≡0 m) ⟩
    n + 0 ≡⟨ +-identityʳ n ⟩
    n ∎
    where open ≡-Reasoning

  ++-assoc₄ : ∀ {ℓ} {A : Set ℓ} (ws xs ys zs : List A) → ws ++ xs ++ ys ++ zs ≡ (ws ++ xs ++ ys) ++ zs
  ++-assoc₄{A = A} ws xs ys zs = solve (++-monoid A)

  -- open import Data.List.Solver using (module ++-Solver)
  -- open ++-Solver using (_⊕_)

  -- ++-assoc₄ : ∀ {ℓ} {A : Set ℓ} (ws xs ys zs : List A) → ws ++ xs ++ ys ++ zs ≡ (ws ++ xs ++ ys) ++ zs
  -- ++-assoc₄ = ++-Solver.solve 4 (λ ws xs ys zs → ws ⊕ xs ⊕ ys ⊕ zs , (ws ⊕ xs ⊕ ys) ⊕ zs) refl

  take-length-++ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → take (length xs) (xs ++ ys) ≡ xs
  take-length-++ [] ys = refl
  take-length-++ (x ∷ xs) ys = cong (x ∷_) (take-length-++ xs ys)

  length-++-≡ : ∀ {ℓ} {A : Set ℓ} (ws xs ys zs : List A) → ws ++ xs ≡ ys ++ zs → length ws ≡ length ys → ws ≡ ys × xs ≡ zs
  length-++-≡ [] xs [] zs ++-≡ len≡ = refl , ++-≡
  length-++-≡ (x ∷ ws) xs (x₁ ∷ ys) zs ++-≡ len≡
    with length-++-≡ ws xs ys zs (∷-injectiveʳ ++-≡) (cong pred len≡)
  ...| refl , xs≡zs = cong (_∷ ws) (∷-injectiveˡ ++-≡) , xs≡zs

  ++-≡-⊆ : ∀ {ℓ} {A : Set ℓ} (ws xs ys zs : List A) → ws ++ xs ≡ ys ++ zs → ∃[ n ] ( ws ++ take n xs ≡ ys ⊎  ws ≡ ys ++ take n zs)
  ++-≡-⊆ [] xs [] zs eq = 0 , inj₁ refl
  ++-≡-⊆ [] (x₁ ∷ xs) (x ∷ ys) zs eq =
    1 + length ys
    , inj₁ (begin take (1 + length ys) (x₁ ∷ xs)
                    ≡⟨ cong (take (1 + length ys)) eq ⟩
                  take (1 + length ys) (x ∷ ys ++ zs)
                    ≡⟨ cong (x ∷_) (take-length-++ ys zs) ⟩
                  x ∷ ys ∎)
    where open ≡-Reasoning
  ++-≡-⊆ (x ∷ ws) xs [] zs eq =
    1 + length ws
    , inj₂ (begin (x ∷ ws ≡⟨ sym (cong (x ∷_) (take-length-++ ws xs)) ⟩
                  take (length (x ∷ ws)) (x ∷ ws ++ xs) ≡⟨ cong (take (1 + length ws)) eq ⟩
                  take (length (x ∷ ws)) zs ∎))
    where open ≡-Reasoning
  ++-≡-⊆ (x ∷ ws) xs (x₁ ∷ ys) zs eq
    with ∷-injectiveˡ eq
  ... | refl
    with ++-≡-⊆ ws xs ys zs (∷-injectiveʳ eq)
  ... | n , inj₁ ys⊆ = n , inj₁ (cong (x ∷_) ys⊆)
  ... | n , inj₂ ws⊆ = n , inj₂ (cong (x ∷_) ws⊆)

  length-++-≤₁ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → length xs ≤ length (xs ++ ys)
  length-++-≤₁ [] ys = z≤n
  length-++-≤₁ (x ∷ xs) ys = s≤s (length-++-≤₁ xs ys)

  length-++-< : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → xs ≢ [] → length ys < length (xs ++ ys)
  length-++-< [] ys xs≢[] = contradiction refl xs≢[]
  length-++-< (x ∷ xs) ys xs≢[] = begin
    1 +             length ys ≤⟨ s≤s (m≤n+m (length ys) (length xs)) ⟩
    1 + length xs + length ys ≡⟨ cong suc (sym (length-++ xs)) ⟩
    1 + length (xs ++ ys)     ≡⟨ refl ⟩
    length (x ∷ xs ++ ys)     ∎
    where
    open ≤-Reasoning

  ++-cancel≡ˡ : ∀ {ℓ} {@0 A : Set ℓ} (@0 ws xs : List A) {@0 ys zs : List A} → ws ≡ xs
                → ws ++ ys ≡ xs ++ zs → ys ≡ zs
  ++-cancel≡ˡ .xs xs refl eq = ‼ ++-cancelˡ xs eq

  ≡⇒≤ : ∀ {m n} → m ≡ n → m ≤ n
  ≡⇒≤ refl = ≤-refl

  all-++-≡ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (P : A → Set ℓ₂)
             → ∀ {ws x xs ys z zs}
             → All P ws → ¬ P x → All P ys → ¬ P z
             → ws ++ [ x ] ++ xs ≡ ys ++ [ z ] ++ zs
             → ws ≡ ys
  all-++-≡ P [] ¬x [] ¬z eq = refl
  all-++-≡ P [] ¬x (px ∷ allys) ¬z eq =
    contradiction (subst P (sym $ ∷-injectiveˡ eq) px) ¬x
  all-++-≡ P (px ∷ allws) ¬x [] ¬z eq =
    contradiction (subst P (∷-injectiveˡ eq) px) ¬z
  all-++-≡ P (px ∷ allws) ¬x (px₁ ∷ allys) ¬z eq
    with ∷-injectiveˡ eq
  ... | refl = cong (_ ∷_) (all-++-≡ _ allws ¬x allys ¬z (∷-injectiveʳ eq))

  ∷ʳ⇒≢[] : ∀ {ℓ} {A : Set ℓ} {xs : List A} {y} → xs ∷ʳ y ≢ []
  ∷ʳ⇒≢[] {xs = []} ()
  ∷ʳ⇒≢[] {xs = x ∷ xs} ()
