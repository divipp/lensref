open import Level
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Fin
open import Data.Sum
open import Data.Maybe
open import Data.Product
open import Data.Vec using (Vec; _∷_; [])
import Data.Vec as Vec
open import Data.List
open import Relation.Binary.PropositionalEquality

--------------- lenses

Lens : Set → Set → Set
Lens A B = A → B × (B → A)

idₗ : {A : Set} → Lens A A
idₗ = λ z → z , λ x → x

_∘ₗ_ : {A B C : Set} → Lens A B → Lens B C → Lens A C
l ∘ₗ k = λ a → let (l₁ , l₂) = l a; (k₁ , k₂) = k l₁ in k₁ , λ x → l₂ (k₂ x)

infixl 9 _∘ₗ_

--- composition laws

_≡ₗ_ : {A B : Set} (k l : Lens A B) → Set
_≡ₗ_ {A} {B} k l = (a : A) → let (k₁ , k₂) = k a; (l₁ , l₂) = l a in k₁ ≡ l₁ × ((b : B) → k₂ b ≡ l₂ b)

infix 4 _≡ₗ_

id-left : {A B : Set} (k : Lens A B) → idₗ ∘ₗ k ≡ₗ k
id-left k a = refl , λ b → refl

id-right : {A B : Set} (k : Lens A B) → k ≡ₗ idₗ ∘ₗ k
id-right k a = refl , λ b → refl

comp-assoc : {A B C D : Set} (k : Lens A B) (l : Lens B C) (m : Lens C D) → k ∘ₗ (l ∘ₗ m) ≡ₗ (k ∘ₗ l) ∘ₗ m
comp-assoc k l m a = refl , λ b → refl


--------------- heterogeneous lists

TList : Set₁
TList = List Set

data HList : TList → Set where
  [] : HList []
  _∷_ : ∀ {t : Set} {ts : TList} → (v : t) → HList ts → HList (t ∷ ts)

--- operations

_+++_ : ∀ {ts xs : TList} → HList ts → HList xs → HList (ts ++ xs)
[] +++ y = y
(v ∷ x) +++ y = v ∷ (x +++ y)

splitH : ∀ {ts xs : TList} → HList (ts ++ xs) → HList ts × HList xs
splitH {ts = []} xs₁ = [] , xs₁
splitH {ts = x ∷ ts} (v ∷ xs₁) = let (r₁ , r₂) = splitH {ts = ts} xs₁ in v ∷ r₁ , r₂

---------------- auxiliary stuff

TList′ : ℕ → Set₁
TList′ = Vec Set

data HList′ : {n : ℕ} → TList′ n → Set where
  [] : HList′ []
  _∷_ : ∀ {n} {t : Set} {ts : TList′ n} → (v : t) → HList′ ts → HList′ (t ∷ ts)

pattern ex a = ._ , a

toVec : ∀ {ℓ} {A : Set ℓ} (as : List A) → Σ ℕ λ n → (n ≡ length as) × Vec A n
toVec [] = 0 , refl , []
toVec (x ∷ as) with toVec as
toVec (x ∷ as) | ex (refl , as′) = _ , refl , x ∷ as′

toVec′ : ∀ {ts : TList} → HList ts → let (_ , _ , ts′) = toVec ts in HList′ ts′ × (HList′ ts′ → HList ts)
toVec′ {[]} [] = [] , (λ _ → [])
toVec′ {x ∷ ts} (v ∷ xs) with toVec ts | toVec′ xs 
toVec′ {x ∷ ts} (v ∷ xs) | ex (refl , _) | xs′ , f = v ∷ xs′ , λ { (v₁ ∷ x₁) → v₁ ∷ f x₁ }

----------

lookup : (ts : TList) → Fin (length ts) → Set
lookup x i with toVec x
lookup x i | ex (refl , v) = Vec.lookup i v


---------------------------------------------- signals

Signal : ∀ {ℓ} → TList → Set ℓ → Set ℓ
Signal ts A = HList ts → A

widenSignal : ∀ {ts xs : TList} {A : Set} → Signal ts A → Signal (ts ++ xs) A
widenSignal s vs = s (proj₁ (splitH vs))

sig : ∀ {ts : TList} (i : Fin (length ts)) → Signal ts (lookup ts i)
sig {ts} i st with toVec ts | toVec′ st
sig i st | ex (refl , v) | z , _ = sig′ i z
  where
    sig′ : ∀ {n} {ts : Vec Set n} (i : Fin n) → HList′ ts → Vec.lookup i ts
    sig′ zero (v ∷ x) = v
    sig′ (suc i) (v ∷ x) = sig′ i x

join : ∀ {ts : TList} {A : Set} → Signal ts (Signal ts A) → Signal ts A
join s vs = s vs vs

ret : ∀ {ts : TList} {A : Set} → A → Signal ts A
ret a _ = a

-- TODO: ret + join  monad laws


------------------------------------ references

Ref : TList → Set → Set
Ref ts = Lens (HList ts)

widenRef : {ts xs : TList} {A : Set} → Ref ts A → Ref (ts ++ xs) A
widenRef r vs = let (vs₁ , vs₂) = splitH vs; (r₁ , r₂) = r vs₁ in r₁ , λ x → r₂ x +++ vs₂

ref : {ts : TList} (i : Fin (length ts)) → Ref ts (lookup ts i)
ref {ts} i st with toVec ts | toVec′ st
ref {ts} i st | ex (refl , v) | z , tr = let (r₁ , r₂) = ref′ i z in r₁ , λ x → tr (r₂ x)
  where
    ref′ : ∀ {n} {ts : TList′ n} (i : Fin n) → Lens (HList′ ts) (Vec.lookup i ts)
    ref′ zero (v ∷ x) = v , λ v → v ∷ x
    ref′ (suc i) (v ∷ x) with ref′ i x
    ref′ (suc i) (v ∷ x) | z , f = z , λ z → v ∷ f z

unitRef : ∀ {ts : TList} → Ref ts ⊤
unitRef st = tt , λ tt → st

joinRef : ∀ {ts : TList} {A : Set} → Signal ts (Ref ts A) → Ref ts A
joinRef s st = s st st

lensMap : ∀ {ts : TList} {A B : Set} → Ref ts A → Lens A B → Ref ts B
lensMap = _∘ₗ_

readRef : ∀ {ts : TList} {A : Set} → Ref ts A → Signal ts A
readRef r st = proj₁ (r st)


---------------------------------- programs

open import Coinduction

Event : TList → Set
Event ts = Σ (Fin (length ts)) λ i → lookup ts i

mutual
  data R (ts : TList) : Set₁ where
    step : HList ts → (Event ts → ∞ (W ts)) → R ts

  W : TList → Set₁
  W ts = Σ TList λ vs → R (ts ++ vs)

Prog : Set₁
Prog = W []


-----------------------------------------

Gen : TList → TList → Set → Set
Gen ts xs A = HList ts → A × HList (ts ++ xs)

Gen′ : TList → Set → Set₁
Gen′ ts A = HList ts → A × Σ TList λ xs → HList (ts ++ xs)

-- TODO: widenGen

data Trigger (ts : TList) (A : Set) : Set₁ where
    extend : {B : Set} → Ref ts B → Lens A B → Trigger ts A
    stabilize : (A → A → Bool) → Signal ts A → Trigger ts A
    onChange : Signal ts (Gen′ ts A) → Trigger ts A

runTrigger : ∀ {ts : TList} {A : Set} → Trigger ts A → Gen′ ts A
runTrigger (extend x x₁) x₂ = {!!}
runTrigger (stabilize x x₁) x₂ = {!!}
runTrigger (onChange x) x₁ = {!!}

-- ...
