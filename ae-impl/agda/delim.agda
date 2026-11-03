module Delim where

open import Data.Nat using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

-- Type Definitions

data Type : Set
data Effect : Set

data Type where
  _⇒[_]_ : Type → Effect → Type → Type
  `1 : Type

data Effect where
  ε : Effect
  _,_ : Effect → Type → Effect
infix 7 _,_

data Context : Set where
  ∅ : Context
  _⨾_ : Context → Type → Context
infix 8 _⨾_

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → Γ ⨾ A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ ⨾ B ∋ A
infix 5 _∋_

_++_ : Effect → Effect → Effect
E ++ ε = E
E ++ (F , A) = (E ++ F) , A
infix 6 _++_

-- Type Util/Lemmas

Renaming : Context → Context → Set
Renaming Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

extRenaming : ∀ {Γ Δ A} → Renaming Γ Δ → Renaming (Γ ⨾ A) (Δ ⨾ A)
extRenaming ρ Z = Z
extRenaming ρ (S x) = S (ρ x)

-- Term Definitions

data _⊢_ : Context → Type → Set
data _⊢_!_ : Context → Type → Effect → Set
infix 4 _⊢_
infix 4 _⊢_!_

data _⊢_ where
  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
  ƛ_ : ∀ {Γ A B E} → Γ ⨾ A ⊢ B ! E → Γ ⊢ A ⇒[ E ] B
  `unit : ∀ {Γ} → Γ ⊢ `1

data _⊢_!_ where
  `val_ : ∀ {Γ A E} → Γ ⊢ A → Γ ⊢ A ! E
  `let_`in_ : ∀ {Γ A B E} → Γ ⊢ A ! E → Γ ⨾ A ⊢ B ! E → Γ ⊢ B ! E
  _·_ : ∀ {Γ A B E} → Γ ⊢ A ⇒[ E ] B → Γ ⊢ A → Γ ⊢ B ! E
  ⟨_⟩ : ∀ {Γ A E} → Γ ⊢ A ! E , A → Γ ⊢ A ! E
  S0_ : ∀ {Γ A E B} → Γ ⨾ A ⇒[ E ] B ⊢ B ! E → Γ ⊢ A ! E , B

-- Substitution & Lemmas

renameᵥ : ∀ {Γ Δ A} → Renaming Γ Δ → Γ ⊢ A → Δ ⊢ A
renameₘ : ∀ {Γ Δ A E} → Renaming Γ Δ → Γ ⊢ A ! E → Δ ⊢ A ! E

renameᵥ ρ (` x) = ` (ρ x)
renameᵥ ρ (ƛ M) = ƛ renameₘ (extRenaming ρ) M
renameᵥ ρ `unit = `unit

renameₘ ρ (`val V) = `val (renameᵥ ρ V)
renameₘ ρ (`let M `in N) = `let (renameₘ ρ M) `in (renameₘ (extRenaming ρ) N)
renameₘ ρ (V · W) = (renameᵥ ρ V) · (renameᵥ ρ W)
renameₘ ρ ⟨ M ⟩ = ⟨ renameₘ ρ M ⟩
renameₘ ρ (S0 M) = S0 (renameₘ (extRenaming ρ) M)

Subst : Context → Context → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

extSub : ∀ {Γ Δ A} → Subst Γ Δ → Subst (Γ ⨾ A) (Δ ⨾ A)
extSub γ Z = ` Z
extSub γ (S x) = renameᵥ S_ (γ x)

subᵥ : ∀ {Γ Δ A} → Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
subₘ : ∀ {Γ Δ A E} → Subst Γ Δ → Γ ⊢ A ! E → Δ ⊢ A ! E

subᵥ γ (` x) = γ x
subᵥ γ (ƛ M) = ƛ subₘ (extSub γ) M
subᵥ γ `unit = `unit

subₘ γ (`val V) = `val (subᵥ γ V)
subₘ γ (`let M `in N) = `let (subₘ γ M) `in (subₘ (extSub γ) N)
subₘ γ (V · W) = (subᵥ γ V) · (subᵥ γ W)
subₘ γ ⟨ M ⟩ = ⟨ subₘ γ M ⟩
subₘ γ (S0 M) = S0 subₘ (extSub γ) M

singleSub : ∀ {Γ A} → Γ ⊢ A → Subst (Γ ⨾ A) Γ
singleSub V Z = V
singleSub V (S x) = ` x

-- Evaluation Contexts

-- number indices denote #-of-resets, so 0 denotes a "pure" context
data _⊢_!_⤋[_]_!_ (Γ : Context) (C : Type) (E : Effect) :
  ℕ → Type → Effect → Set where
  □ : Γ ⊢ C ! E ⤋[ 0 ] C ! E
  `let[_]`in_ : ∀ {A B F n} → Γ ⊢ C ! E ⤋[ n ] A ! F → Γ ⨾ A ⊢ B ! F
    → Γ ⊢ C ! E ⤋[ n ] B ! F
  ⟨[_]⟩ : ∀ {A F n} → Γ ⊢ C ! E ⤋[ n ] A ! (F , A) → Γ ⊢ C ! E ⤋[ suc n ] A ! F

plug : ∀ {Γ A B E F n} → Γ ⊢ A ! E ⤋[ n ] B ! F → Γ ⊢ A ! E → Γ ⊢ B ! F
plug □ M = M
plug (`let[ ℰ ]`in N) M = `let (plug ℰ M) `in N
plug ⟨[ ℰ ]⟩ M = ⟨ plug ℰ M ⟩

pureEC : ∀ {Γ A B E F} → Γ ⊢ A ! E ⤋[ 0 ] B ! F → E ≡ F
pureEC □ = refl
pureEC (`let[ ℰ ]`in _) = pureEC ℰ

renameₑ : ∀ {Γ Δ A B E F n} → Renaming Γ Δ → Γ ⊢ A ! E ⤋[ n ] B ! F
  → Δ ⊢ A ! E ⤋[ n ] B ! F
renameₑ ρ □ = □
renameₑ ρ (`let[ ℰ ]`in M) = `let[ renameₑ ρ ℰ ]`in (renameₘ (extRenaming ρ) M)
renameₑ ρ ⟨[ ℰ ]⟩ = ⟨[ renameₑ ρ ℰ ]⟩

-- Semantics

data _↝β_ : ∀ {Γ A E} → Γ ⊢ A ! E → Γ ⊢ A ! E → Set where
  β-let : ∀ {Γ A B E} {V : Γ ⊢ B} {M : Γ ⨾ B ⊢ A ! E}
    → `let (`val V) `in M ↝β subₘ (singleSub V) M
  β-· : ∀ {Γ A B E} {M : Γ ⨾ B ⊢ A ! E} {V : Γ ⊢ B}
    → (ƛ M) · V ↝β subₘ (singleSub V) M
  β-⟨⟩ : ∀ {Γ A E} {V : Γ ⊢ A} → _↝β_ {E = E} (⟨ `val V ⟩) (`val V)
  β-S0 : ∀ {Γ A B E}
    {M : Γ ⨾ B ⇒[ E ] A ⊢ A ! E} {ℰ : Γ ⊢ B ! (E , A) ⤋[ 0 ] A ! (E , A)} →
    ⟨ plug ℰ (S0 M) ⟩ ↝β
    subₘ (singleSub (ƛ ⟨ plug (renameₑ S_ ℰ) (`val (` Z)) ⟩)) M
infix 4 _↝β_

data _↝_ : ∀ {Γ A E} →  Γ ⊢ A ! E → Γ ⊢ A ! E → Set where
  ξξ : ∀ {Γ A B E F n} {M N : Γ ⊢ A ! E} {M' N' : Γ ⊢ B ! F}
    → (ℰ : Γ ⊢ A ! E ⤋[ n ] B ! F) → M' ≡ plug ℰ M → N' ≡ plug ℰ N
    → M ↝β N → M' ↝ N'

pattern ξ E β = ξξ E refl refl β

data Progress : ∀ {A E} → ∅ ⊢ A ! E → Set where
  step : ∀ {A E} {M N : ∅ ⊢ A ! E} → M ↝ N → Progress M
  done : ∀ {A E} {V : ∅ ⊢ A} → Progress {E = E} (`val V)
  blocked : ∀ {A B C E F} {M : (∅ ⨾ B ⇒[ F ] C) ⊢ C ! F}
    → (ℰ : ∅ ⊢ B ! F , C ⤋[ 0 ] A ! E) → Progress (plug ℰ (S0 M))

progress : ∀ {A E} → (M : ∅ ⊢ A ! E) → Progress M
progress (`val V) = done
progress (`let M `in N) with progress M
... | step (ξ ℰ β) = step (ξ (`let[ ℰ ]`in N) β)
... | done = step (ξ □ β-let)
... | blocked ℰ = blocked (`let[ ℰ ]`in N)
progress ((ƛ M) · V) = step (ξ □ β-·)
progress ⟨ M ⟩ with progress M
... | step (ξ ℰ β) = step (ξ ⟨[ ℰ ]⟩ β)
... | done = step (ξ □ β-⟨⟩)
... | blocked ℰ with pureEC ℰ
...   | refl = step (ξ □ β-S0)
progress (S0 M) = blocked □

data PureProgress : ∀ {A} → ∅ ⊢ A ! ε → Set where
  pureStep : ∀ {A} {M N : ∅ ⊢ A ! ε} → M ↝ N → PureProgress M
  pureDone : ∀ {A} {V : ∅ ⊢ A} → PureProgress (`val V)

pureProgress : ∀ {A} → (M : ∅ ⊢ A ! ε) → PureProgress M
pureProgress (`val V) = pureDone
pureProgress (`let M `in N) with pureProgress M
... | pureStep (ξ ℰ β) = pureStep (ξ (`let[ ℰ ]`in N) β)
... | pureDone = pureStep (ξ □ β-let)
pureProgress ((ƛ M) · V) = pureStep (ξ □ β-·)
pureProgress ⟨ M ⟩ with progress M
... | step (ξ ℰ β) = pureStep (ξ ⟨[ ℰ ]⟩ β)
... | done = pureStep (ξ □ β-⟨⟩)
... | blocked ℰ with pureEC ℰ
...   | refl = pureStep (ξ □ β-S0)

