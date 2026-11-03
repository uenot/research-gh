module Async where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data Type : Set where
  _⇒_ : Type → Type → Type
  `1 : Type
  ○_ : Type → Type

data Context : Set where
  ∅ : Context
  _⨾_ : Context → Type → Context
infix 8 _⨾_

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → Γ ⨾ A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ ⨾ B ∋ A
infix 5 _∋_

Ren : Context → Context → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

extRen : ∀ {Γ Δ A} → Ren Γ Δ → Ren (Γ ⨾ A) (Δ ⨾ A)
extRen ρ Z = Z
extRen ρ (S x) = S (ρ x)

data _⊢ᵥ_ : Context → Type → Set
data _⊢ₘ_ : Context → Type → Set
infix 4 _⊢ᵥ_
infix 4 _⊢ₘ_

data _⊢ᵥ_ where
  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ᵥ A
  ƛ_ : ∀ {Γ A B} → Γ ⨾ A ⊢ₘ B → Γ ⊢ᵥ A ⇒ B
  `unit : ∀ {Γ} → Γ ⊢ᵥ `1
  `now_ : ∀ {Γ A} → Γ ⊢ᵥ A → Γ ⊢ᵥ ○ A

data _⊢ₘ_ where
  `val_ : ∀ {Γ A} → Γ ⊢ᵥ A → Γ ⊢ₘ A
  `async_`in_ : ∀ {Γ A B} → Γ ⊢ₘ A → Γ ⨾ ○ A ⊢ₘ B → Γ ⊢ₘ B
  `await_`in_ : ∀ {Γ A B} → Γ ⊢ᵥ ○ A → Γ ⨾ A ⊢ₘ B → Γ ⊢ₘ B
  _·_ : ∀ {Γ A B} → Γ ⊢ᵥ A ⇒ B → Γ ⊢ᵥ A → Γ ⊢ₘ B

renameᵥ : ∀ {Γ Δ A} → Ren Γ Δ → Γ ⊢ᵥ A → Δ ⊢ᵥ A
renameₘ : ∀ {Γ Δ A} → Ren Γ Δ → Γ ⊢ₘ A → Δ ⊢ₘ A

renameᵥ ρ (` x) = ` ρ x
renameᵥ ρ (ƛ M) = ƛ renameₘ (extRen ρ) M
renameᵥ ρ `unit = `unit
renameᵥ ρ (`now V) = `now (renameᵥ ρ V)

renameₘ ρ (`val V) = `val (renameᵥ ρ V)
renameₘ ρ (`async M `in N) = `async (renameₘ ρ M) `in renameₘ (extRen ρ) N
renameₘ ρ (`await V `in M) = `await (renameᵥ ρ V) `in renameₘ (extRen ρ) M
renameₘ ρ (V · W) = (renameᵥ ρ V) · (renameᵥ ρ W)

Subst : Context → Context → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ᵥ A

extSub : ∀ {Γ Δ A} → Subst Γ Δ → Subst (Γ ⨾ A) (Δ ⨾ A)
extSub γ Z = ` Z
extSub γ (S x) = renameᵥ S_ (γ x)

subᵥ : ∀ {Γ Δ A} → Subst Γ Δ → Γ ⊢ᵥ A → Δ ⊢ᵥ A
subₘ : ∀ {Γ Δ A} → Subst Γ Δ → Γ ⊢ₘ A → Δ ⊢ₘ A

subᵥ γ (` x) = γ x
subᵥ γ (ƛ M) = ƛ (subₘ (extSub γ) M)
subᵥ γ `unit = `unit
subᵥ γ (`now V) = `now (subᵥ γ V)

subₘ γ (`val V) = `val (subᵥ γ V)
subₘ γ (`async M `in N) = `async (subₘ γ M) `in (subₘ (extSub γ) N)
subₘ γ (`await V `in M) = `await (subᵥ γ V) `in (subₘ (extSub γ) M)
subₘ γ (V · W) = (subᵥ γ V) · (subᵥ γ W)

sub₁ : ∀ {Γ A} → Γ ⊢ᵥ A → Subst (Γ ⨾ A) Γ
sub₁ V Z = V
sub₁ V (S x) = ` x

data _⊢_⤋_⊢_ (Γ : Context) (A : Type) : Context → Type → Set where
  □ : Γ ⊢ A ⤋ Γ ⊢ A
  `async[_]`in_ : ∀ {Δ B C} → Γ ⊢ A ⤋ Δ ⊢ B → Δ ⨾ ○ B ⊢ₘ C → Γ ⊢ A ⤋ Δ ⊢ C
  `async_`in[_] : ∀ {Δ B C} → Δ ⊢ₘ B → Γ ⊢ A ⤋ (Δ ⨾ ○ B) ⊢ C → Γ ⊢ A ⤋ Δ ⊢ C

plug : ∀ {Γ Δ A B} → Γ ⊢ A ⤋ Δ ⊢ B → Γ ⊢ₘ A → Δ ⊢ₘ B
plug □ M = M
plug (`async[ ℰ ]`in N) M = `async (plug ℰ M) `in N
plug `async N `in[ ℰ ] M = `async N `in plug ℰ M

data _↝β_ : ∀ {Γ A} → Γ ⊢ₘ A → Γ ⊢ₘ A → Set where
  β-async : ∀ {Γ A B} {V : Γ ⊢ᵥ B} {M : Γ ⨾ ○ B ⊢ₘ A}
    → (`async (`val V) `in M) ↝β subₘ (sub₁ (`now V)) M
  β-await : ∀ {Γ A B} {V : Γ ⊢ᵥ B} {M : Γ ⨾ B ⊢ₘ A}
    → (`await (`now V) `in M) ↝β subₘ (sub₁ V) M
  β-· : ∀ {Γ A B} {V : Γ ⊢ᵥ A} {M : Γ ⨾ A ⊢ₘ B}
    → ((ƛ M) · V) ↝β subₘ (sub₁ V) M

data _↝_ : ∀ {Γ A} →  Γ ⊢ₘ A → Γ ⊢ₘ A → Set where
  ξξ : ∀ {Γ Δ A B} {M N : Γ ⊢ₘ A} {M' N' : Δ ⊢ₘ B}
    → (ℰ : Γ ⊢ A ⤋ Δ ⊢ B) → M' ≡ plug ℰ M → N' ≡ plug ℰ N
    → M ↝β N → M' ↝ N'

pattern ξ ℰ β = ξξ ℰ refl refl β

data Progress : ∀ {A} → ∅ ⊢ₘ A → Set where
  step : ∀ {A} {M N : ∅ ⊢ₘ A} → M ↝ N → Progress M
  done : ∀ {A} {V : ∅ ⊢ᵥ A} → Progress (`val V)

progress : ∀ {A} → (M : ∅ ⊢ₘ A) → Progress M
progress (`val V) = done
progress (`async M `in N) with progress M
... | step (ξ ℰ β) = step (ξ (`async[ ℰ ]`in N) β)
... | done = step (ξ □ β-async)
progress (`await `now V `in M) = step (ξ □ β-await)
progress ((ƛ M) · V) = step (ξ □ β-·)