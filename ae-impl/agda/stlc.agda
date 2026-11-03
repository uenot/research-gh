module stlc where

open import Data.String using (String; _≟_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no; False; toWitnessFalse; ¬?)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; ≢-sym)

Id : Set
Id = String

data Val : Set
data Comp : Set

data Val where
  `_ : Id → Val
  ƛ_⇒_ : Id → Comp → Val
  ⟨_,_⟩ : Val → Val → Val
  `unit : Val

data Comp where
  `val : Val → Comp
  `let_←_`in_ : Id → Comp → Comp → Comp
  _·_ : Val → Val → Comp
  π₁_ : Val → Comp
  π₂_ : Val → Comp

subVal : Val → Id → Val → Val
subComp : Comp → Id → Val → Comp

subVal (` x) id v with x ≟ id
... | yes _ = v
... | no _ = ` x
subVal (ƛ x ⇒ m) id v with x ≟ id
... | yes _ = ƛ x ⇒ m
... | no _ = ƛ x ⇒ (subComp m id v)
subVal ⟨ v₁ , v₂ ⟩ id v = ⟨ (subVal v₁ id v), (subVal v₂ id v) ⟩
subVal `unit id v = `unit

subComp (`val w) id v = `val (subVal w id v)
subComp (`let x ← m₁ `in m₂) id v with x ≟ id
... | yes _ = `let x ← (subComp m₁ id v) `in m₂
... | no _ = `let x ← (subComp m₁ id v) `in (subComp m₂ id v)
subComp (w₁ · w₂) id v = (subVal w₁ id v) · (subVal w₂ id v)
subComp (π₁ w) id v = π₁ (subVal w id v)
subComp (π₂ w) id v = π₂ (subVal w id v)

data _↝_ : Comp → Comp → Set where
  ξ-let :
    ∀ {x m₁ m₂ n} → m₁ ↝ m₂ → (`let x ← m₁ `in n) ↝ (`let x ← m₂ `in n)
  β-let :
    ∀ {x v m} → (`let x ← (`val v) `in m) ↝ subComp m x v
  β-· :
    ∀ {x v m} → ((ƛ x ⇒ m) · v) ↝ subComp m x v
  β-π₁ :
    ∀ {v w} → (π₁ ⟨ v , w ⟩) ↝ `val v
  β-π₂ :
    ∀ {v w} → (π₂ ⟨ v , w ⟩) ↝ `val w

data Type : Set where
  _⇒_ : Type → Type → Type
  _×_ : Type → Type → Type
  `1 : Type

data TypeCtx : Set where
  ∅ : TypeCtx
  _,_∶_ : TypeCtx → Id → Type → TypeCtx

data _∋_∶_ : TypeCtx → Id → Type → Set where
  Z : ∀ {Γ x A} → (Γ , x ∶ A) ∋ x ∶ A
  S : ∀ {Γ x y A B} → x ≢ y → Γ ∋ x ∶ A → (Γ , y ∶ B) ∋ x ∶ A

S' : ∀ {Γ x y A B} → {x≢y : False (x ≟ y)} → Γ ∋ x ∶ A → (Γ , y ∶ B) ∋ x ∶ A
S' {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

data _⊢ᵥ_∶_ : TypeCtx → Val → Type → Set
data _⊢ₘ_∶_ : TypeCtx → Comp → Type → Set

data _⊢ᵥ_∶_ where
  TV-Var : ∀ {Γ x A} → Γ ∋ x ∶ A → Γ ⊢ᵥ ` x ∶ A

  TV-Lam : ∀ {Γ x M A B} → (Γ , x ∶ A) ⊢ₘ M ∶ B → Γ ⊢ᵥ (ƛ x ⇒ M) ∶ (A ⇒ B)

  TV-Unit : ∀ {Γ} → Γ ⊢ᵥ `unit ∶ `1

  TV-Pair : ∀ {Γ V W A B} → Γ ⊢ᵥ V ∶ A → Γ ⊢ᵥ W ∶ B → Γ ⊢ᵥ ⟨ V , W ⟩ ∶ (A × B)

data _⊢ₘ_∶_ where
  TC-Val : ∀ {Γ V A} → Γ ⊢ᵥ V ∶ A → Γ ⊢ₘ (`val V) ∶ A

  TC-Let : ∀ {Γ x M N A B} → Γ ⊢ₘ M ∶ A → (Γ , x ∶ A) ⊢ₘ N ∶ B
    → Γ ⊢ₘ `let x ← M `in N ∶ B

  TC-App : ∀ {Γ V W A B} → Γ ⊢ᵥ V ∶ (A ⇒ B) → Γ ⊢ᵥ W ∶ A → Γ ⊢ₘ V · W ∶ B

  TC-π₁ : ∀ {Γ V A B} → Γ ⊢ᵥ V ∶ (A × B) → Γ ⊢ₘ π₁ V ∶ A

  TC-π₂ : ∀ {Γ V A B} → Γ ⊢ᵥ V ∶ (A × B) → Γ ⊢ₘ π₂ V ∶ B

data Progress (M : Comp) : Set where
  step : ∀ {N} → M ↝ N → Progress M
  done : ∀ {V} → M ≡ `val V → Progress M

canon-ƛ : ∀ {V A B} → ∅ ⊢ᵥ V ∶ (A ⇒ B) → ∃[ x ] ∃[ M ] V ≡ (ƛ x ⇒ M)
canon-ƛ (TV-Lam {x = x} {M = M} pf) = x , M , refl

canon-× : ∀ {V A B} → ∅ ⊢ᵥ V ∶ (A × B) → ∃[ V₁ ] ∃[ V₂ ] V ≡ ⟨ V₁ , V₂ ⟩
canon-× (TV-Pair {V = V₁} {W = V₂} p1 p2) = V₁ , V₂ , refl

progress : ∀ {M A} → ∅ ⊢ₘ M ∶ A → Progress M
progress (TC-Val x) = done refl
progress (TC-Let tm tn) with progress tm
... | step M↝M' = step (ξ-let M↝M')
... | done refl = step β-let
progress (TC-App tV tW) with canon-ƛ tV
... | x , M , refl = step β-·
progress (TC-π₁ tV) with canon-× tV
... | V₁ , V₂ , refl = step β-π₁
progress (TC-π₂ tV) with canon-× tV
... | V₁ , V₂ , refl = step β-π₂

_⊆_ : TypeCtx → TypeCtx → Set
Γ ⊆ Δ = ∀ {x A} → Γ ∋ x ∶ A → Δ ∋ x ∶ A

ext : ∀ {Γ Δ x A} → Γ ⊆ Δ → (Γ , x ∶ A) ⊆ (Δ , x ∶ A)
ext Γ⊆Δ Z = Z
ext Γ⊆Δ (S x≢y ev) = S x≢y (Γ⊆Δ ev)

shadow : ∀ {Γ x A B} → ((Γ , x ∶ A) , x ∶ B) ⊆ (Γ , x ∶ B)
shadow Z = Z
shadow (S x≢x Z) = contradiction refl x≢x
shadow (S {x = y} y≢x (S x y∋)) = S y≢x y∋

xchg : ∀ {Γ x A y B} → x ≢ y → ((Γ , x ∶ A) , y ∶ B) ⊆ ((Γ , y ∶ B) , x ∶ A)
xchg x≢y Z = S (≢-sym x≢y) Z
xchg x≢y (S {x = z} z≢y Z) = Z
xchg x≢y (S {x = z} z≢y (S z≢x x∋)) = S z≢x (S z≢y x∋)

wknᵥ : ∀ {Γ Δ V A} → Γ ⊆ Δ → Γ ⊢ᵥ V ∶ A → Δ ⊢ᵥ V ∶ A
wknₘ : ∀ {Γ Δ M A} → Γ ⊆ Δ → Γ ⊢ₘ M ∶ A → Δ ⊢ₘ M ∶ A

wknᵥ Γ⊆Δ (TV-Var ∋x∶A) = TV-Var (Γ⊆Δ ∋x∶A)
wknᵥ Γ⊆Δ (TV-Lam ⊢M) = TV-Lam (wknₘ (ext Γ⊆Δ) ⊢M)
wknᵥ Γ⊆Δ TV-Unit = TV-Unit
wknᵥ Γ⊆Δ (TV-Pair ⊢V ⊢W) = TV-Pair (wknᵥ Γ⊆Δ ⊢V) (wknᵥ Γ⊆Δ ⊢W)

wknₘ Γ⊆Δ (TC-Val ⊢V) = TC-Val (wknᵥ Γ⊆Δ ⊢V)
wknₘ Γ⊆Δ (TC-Let ⊢M ⊢N) = TC-Let (wknₘ Γ⊆Δ ⊢M) (wknₘ (ext Γ⊆Δ) ⊢N)
wknₘ Γ⊆Δ (TC-App ⊢V ⊢W) = TC-App (wknᵥ Γ⊆Δ ⊢V) (wknᵥ Γ⊆Δ ⊢W)
wknₘ Γ⊆Δ (TC-π₁ ⊢V) = TC-π₁ (wknᵥ Γ⊆Δ ⊢V)
wknₘ Γ⊆Δ (TC-π₂ ⊢V) = TC-π₂ (wknᵥ Γ⊆Δ ⊢V)

subprezᵥ : ∀ {Γ V x W A B} → (Γ , x ∶ A) ⊢ᵥ V ∶ B → ∅ ⊢ᵥ W ∶ A
  → Γ ⊢ᵥ (subVal V x W) ∶ B
subprezₘ : ∀ {Γ M x V A B} → (Γ , x ∶ A) ⊢ₘ M ∶ B → ∅ ⊢ᵥ V ∶ A
  → Γ ⊢ₘ (subComp M x V) ∶ B

subprezᵥ {x = y} (TV-Var {x = x} Z) ⊢W with x ≟ y
... | yes refl = wknᵥ (λ()) ⊢W
... | no ev = contradiction refl ev
subprezᵥ {x = y} (TV-Var {x = x} (S x≢y ∋x)) ⊢W with x ≟ y
... | yes refl = contradiction refl x≢y
... | no ev = TV-Var ∋x
subprezᵥ {x = y} (TV-Lam {x = x} ⊢M) ⊢W with x ≟ y
... | yes refl = TV-Lam (wknₘ shadow ⊢M)
... | no x≢y = TV-Lam (subprezₘ (wknₘ (xchg (≢-sym x≢y)) ⊢M) ⊢W)
subprezᵥ TV-Unit ⊢W = TV-Unit
subprezᵥ (TV-Pair ⊢V₁ ⊢V₂) ⊢W = TV-Pair (subprezᵥ ⊢V₁ ⊢W) (subprezᵥ ⊢V₂ ⊢W)

subprezₘ (TC-Val ⊢W) ⊢V = TC-Val (subprezᵥ ⊢W ⊢V)
subprezₘ {x = y} (TC-Let {x = x} ⊢M ⊢N) ⊢V with x ≟ y
... | yes refl = TC-Let (subprezₘ ⊢M ⊢V) (wknₘ shadow ⊢N)
... | no x≢y = TC-Let
                ((subprezₘ ⊢M ⊢V))
                (subprezₘ (wknₘ (xchg (≢-sym x≢y)) ⊢N) ⊢V)
subprezₘ (TC-App ⊢W₁ ⊢W₂) ⊢V  = TC-App (subprezᵥ ⊢W₁ ⊢V) (subprezᵥ ⊢W₂ ⊢V)
subprezₘ (TC-π₁ ⊢W) ⊢V  = TC-π₁ (subprezᵥ ⊢W ⊢V)
subprezₘ (TC-π₂ ⊢W) ⊢V = TC-π₂ (subprezᵥ ⊢W ⊢V)

preservation : ∀ {M N A} → ∅ ⊢ₘ M ∶ A → M ↝ N → ∅ ⊢ₘ N ∶ A
preservation (TC-Let ⊢M ⊢N) (ξ-let (M↝M')) =
  TC-Let (preservation ⊢M M↝M') ⊢N
preservation (TC-Let (TC-Val ⊢V) ⊢M) (β-let) = subprezₘ ⊢M ⊢V
preservation (TC-App (TV-Lam ⊢M) ⊢V) β-· = subprezₘ ⊢M ⊢V
preservation (TC-π₁ (TV-Pair ⊢V ⊢W)) (β-π₁) = TC-Val ⊢V
preservation (TC-π₂ (TV-Pair ⊢V ⊢W)) (β-π₂) = TC-Val ⊢W