module AsyncDelim where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data Type : Set where
  _⇒_ : Type → Type → Type
  `1 : Type
  ○_ : Type → Type
  □_ : Type → Type

data Context : Set where
  ∅ : Context
  _⨾_ : Context → Type → Context
  _# : Context → Context
infix 8 _⨾_
infix 10 _#

data Stable : Type → Set where
  S1 : Stable `1
  S□ : ∀ {A} → Stable (□ A)

data _∋_ : Context → Type → Set where
  zero : ∀ {Γ A} → Γ ⨾ A ∋ A
  succ : ∀ {Γ A B} → Γ ∋ A → Γ ⨾ B ∋ A
  lift : ∀ {Γ A} → Stable A → Γ ∋ A → Γ # ∋ A
infix 5 _∋_

data _⊑_ : Context → Context → Set where
  base : ∅ ⊑ ∅
  drop : ∀ {Γ Δ A} → Γ ⊑ Δ → Γ ⊑ Δ ⨾ A
  keep : ∀ {Γ Δ A} → Γ ⊑ Δ → Γ ⨾ A ⊑ Δ ⨾ A
  keepLock : ∀ {Γ Δ} → Γ ⊑ Δ → Γ # ⊑ Δ #
  relock : ∀ {Γ Δ} → Γ # ⊑ Δ → Γ # ⊑ Δ #
  unlock : ∀ {Γ Δ} → Γ ⊑ Δ → Γ # ⊑ Δ
infix 6 _⊑_

⊑-refl : ∀ {Γ} → Γ ⊑ Γ
⊑-refl {∅} = base
⊑-refl {Γ ⨾ A} = keep ⊑-refl
⊑-refl {Γ #} = keepLock ⊑-refl

renameVar : ∀ {Γ Δ A} → Γ ⊑ Δ → Γ ∋ A → Δ ∋ A
renameVar (drop ρ) x = succ (renameVar ρ x)
renameVar (keep ρ) zero = zero
renameVar (keep ρ) (succ x) = succ (renameVar ρ x)
renameVar (keepLock ρ) (lift stab x) = lift stab (renameVar ρ x)
renameVar (relock ρ) (lift stab x) = lift stab (renameVar ρ (lift stab x))
renameVar (unlock ρ) (lift stab x) = renameVar ρ x

data _⊢_ : Context → Type → Set
data _⊢_! : Context → Type → Set
infix 4 _⊢_
infix 4 _⊢_!

data _⊢_ where
  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
  ƛ_ : ∀ {Γ A B} → Γ ⨾ A ⊢ B ! → Γ ⊢ A ⇒ B
  `unit : ∀ {Γ} → Γ ⊢ `1
  `now_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ ○ A
  `box_ : ∀ {Γ A} → Γ # ⊢ A → Γ ⊢ □ A

data _⊢_! where
  `val_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A !
  `async_`in_ : ∀ {Γ A B} → Γ ⊢ A ! → Γ ⨾ ○ A ⊢ B ! → Γ ⊢ B !
  `await_`in_ : ∀ {Γ A B} → Γ ⊢ ○ A → Γ ⨾ A ⊢ B ! → Γ ⊢ B !
  _·_ : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B !
  `unbox_ : ∀ {Γ A} → Γ ⊢ □ A → Γ ⊢ A !

renameᵥ : ∀ {Γ Δ A} → Γ ⊑ Δ → Γ ⊢ A → Δ ⊢ A
renameₘ : ∀ {Γ Δ A} → Γ ⊑ Δ → Γ ⊢ A ! → Δ ⊢ A !

renameᵥ ρ (` x) = ` (renameVar ρ x)
renameᵥ ρ (ƛ M) = ƛ renameₘ (keep ρ) M
renameᵥ ρ `unit = `unit
renameᵥ ρ (`now V) = `now (renameᵥ ρ V)
renameᵥ ρ (`box V) = `box renameᵥ (keepLock ρ) V

renameₘ ρ (`val V) = `val (renameᵥ ρ V)
renameₘ ρ (`async M `in N) = `async (renameₘ ρ M) `in renameₘ (keep ρ) N
renameₘ ρ (`await V `in M) = `await (renameᵥ ρ V) `in renameₘ (keep ρ) M
renameₘ ρ (V · W) = (renameᵥ ρ V) · (renameᵥ ρ W)
renameₘ ρ (`unbox V) = `unbox (renameᵥ ρ V)

stableᵥ : ∀ {Γ A} → Stable A → Γ ⊢ A → Γ # ⊢ A
stableᵥ S1 (` x) = ` lift S1 x
stableᵥ S1 `unit = `unit
stableᵥ S□ (` x) = ` lift S□ x
stableᵥ S□ (`box V) = `box renameᵥ (relock ⊑-refl) V

Subst : Context → Context → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

extSub : ∀ {Γ Δ A} → Subst Γ Δ → Subst (Γ ⨾ A) (Δ ⨾ A)
extSub γ zero = ` zero
extSub γ (succ x) = renameᵥ (drop ⊑-refl) (γ x)

lockSub : ∀ {Γ Δ} → Subst Γ Δ → Subst (Γ #) (Δ #)
lockSub γ (lift stab x) = stableᵥ stab (γ x)

subᵥ : ∀ {Γ Δ A} → Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
subₘ : ∀ {Γ Δ A} → Subst Γ Δ → Γ ⊢ A ! → Δ ⊢ A !

subᵥ γ (` x) = γ x
subᵥ γ (ƛ M) = ƛ (subₘ (extSub γ) M)
subᵥ γ `unit = `unit
subᵥ γ (`now V) = `now (subᵥ γ V)
subᵥ γ (`box V) = `box subᵥ (lockSub γ) V

subₘ γ (`val V) = `val (subᵥ γ V)
subₘ γ (`async M `in N) = `async (subₘ γ M) `in (subₘ (extSub γ) N)
subₘ γ (`await V `in M) = `await (subᵥ γ V) `in (subₘ (extSub γ) M)
subₘ γ (V · W) = (subᵥ γ V) · (subᵥ γ W)
subₘ γ (`unbox V) = `unbox subᵥ γ V

sub₁ : ∀ {Γ A} → Γ ⊢ A → Subst (Γ ⨾ A) Γ
sub₁ V zero = V
sub₁ V (succ x) = ` x

data _⊢_⤋_⊢_ (Γ : Context) (A : Type) : Context → Type → Set where
  □ : Γ ⊢ A ⤋ Γ ⊢ A
  `async[_]`in_ : ∀ {Δ B C} → Γ ⊢ A ⤋ Δ ⊢ B → Δ ⨾ ○ B ⊢ C ! → Γ ⊢ A ⤋ Δ ⊢ C
  `async_`in[_] : ∀ {Δ B C} → Δ ⊢ B ! → Γ ⊢ A ⤋ (Δ ⨾ ○ B) ⊢ C → Γ ⊢ A ⤋ Δ ⊢ C

plug : ∀ {Γ Δ A B} → Γ ⊢ A ⤋ Δ ⊢ B → Γ ⊢ A ! → Δ ⊢ B !
plug □ M = M
plug (`async[ ℰ ]`in N) M = `async (plug ℰ M) `in N
plug `async M `in[ ℰ ] N = `async M `in plug ℰ N

data _↝β_ : ∀ {Γ A} → Γ ⊢ A ! → Γ ⊢ A ! → Set where
  β-async : ∀ {Γ A B} {V : Γ ⊢ B} {M : Γ ⨾ ○ B ⊢ A ! }
    → (`async (`val V) `in M) ↝β subₘ (sub₁ (`now V)) M
  β-await : ∀ {Γ A B} {V : Γ ⊢ B} {M : Γ ⨾ B ⊢ A ! }
    → (`await (`now V) `in M) ↝β subₘ (sub₁ V) M
  β-· : ∀ {Γ A B} {V : Γ ⊢ A} {M : Γ ⨾ A ⊢ B ! }
    → ((ƛ M) · V) ↝β subₘ (sub₁ V) M
  β-□ : ∀ {Γ A} {V : Γ # ⊢ A}
    → (`unbox (`box V)) ↝β (`val renameᵥ (unlock ⊑-refl) V)

data _↝_ : ∀ {Γ A} →  Γ ⊢ A ! → Γ ⊢ A ! → Set where
  ξξ : ∀ {Γ Δ A B} {M N : Γ ⊢ A ! } {M' N' : Δ ⊢ B ! }
    → (ℰ : Γ ⊢ A ⤋ Δ ⊢ B) → M' ≡ plug ℰ M → N' ≡ plug ℰ N
    → M ↝β N → M' ↝ N'

pattern ξ ℰ β = ξξ ℰ refl refl β

data Progress : ∀ {A} → ∅ ⊢ A ! → Set where
  step : ∀ {A} {M N : ∅ ⊢ A ! } → M ↝ N → Progress M
  done : ∀ {A} {V : ∅ ⊢ A} → Progress (`val V)

progress : ∀ {A} → (M : ∅ ⊢ A !) → Progress M
progress (`val V) = done
progress (`async M `in N) with progress M
... | step (ξ ℰ β) = step (ξ (`async[ ℰ ]`in N) β)
... | done = step (ξ □ β-async)
progress (`await `now V `in M) = step (ξ □ β-await)
progress ((ƛ M) · V) = step (ξ □ β-·)
progress (`unbox (`box V)) = step (ξ □ β-□)