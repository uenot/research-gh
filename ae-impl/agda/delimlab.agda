module DelimLab where

open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open Eq.≡-Reasoning

-- Type Definitions

Op = String

data Type : Set
data Effect : Set

data Type where
  _⇒[_]_ : Type → Effect → Type → Type
  `1 : Type

data Effect where
  ε : Effect
  _,_⦂_ : Effect → Op → Type → Effect
infix 7 _,_⦂_

data Context : Set where
  ∅ : Context
  _⨾_ : Context → Type → Context
infix 8 _⨾_

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → Γ ⨾ A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ ⨾ B ∋ A
infix 5 _∋_

data _∌ₑ_ : Effect → Op → Set where
  Z : ∀ {ℓ} → ε ∌ₑ ℓ
  S_ : ∀ {E ℓ ℓ' A} → ℓ ≢ ℓ' → E ∌ₑ ℓ → (E , ℓ' ⦂ A) ∌ₑ ℓ
infix 5 _∌ₑ_

-- Type Util/Lemmas

Renaming : Context → Context → Set
Renaming Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

extRenaming : ∀ {Γ Δ A} → Renaming Γ Δ → Renaming (Γ ⨾ A) (Δ ⨾ A)
extRenaming ρ Z = Z
extRenaming ρ (S x) = S (ρ x)

_++_ : Effect → Effect → Effect
E ++ ε = E
E ++ (F , ℓ ⦂ A) = (E ++ F) , ℓ ⦂ A

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
  _⟨_⟩ : ∀ {Γ A E} → (ℓ : Op) → Γ ⊢ A ! E , ℓ ⦂ A → Γ ⊢ A ! E
  S_[_]⇒_ : ∀ {Γ A B E F}
    → (ℓ : Op)
    → F ∌ₑ ℓ
    → Γ ⨾ A ⇒[ E ] B ⊢ B ! E
    → Γ ⊢ A ! (E , ℓ ⦂ B) ++ F

-- Substitution & Lemmas

renameᵥ : ∀ {Γ Δ A} → Renaming Γ Δ → Γ ⊢ A → Δ ⊢ A
renameₘ : ∀ {Γ Δ A E} → Renaming Γ Δ → Γ ⊢ A ! E → Δ ⊢ A ! E

renameᵥ ρ (` x) = ` (ρ x)
renameᵥ ρ (ƛ M) = ƛ renameₘ (extRenaming ρ) M
renameᵥ ρ `unit = `unit

renameₘ ρ (`val V) = `val (renameᵥ ρ V)
renameₘ ρ (`let M `in N) = `let (renameₘ ρ M) `in (renameₘ (extRenaming ρ) N)
renameₘ ρ (V · W) = (renameᵥ ρ V) · (renameᵥ ρ W)
renameₘ ρ (ℓ ⟨ M ⟩) = ℓ ⟨ renameₘ ρ M ⟩
renameₘ ρ (S ℓ [ ∌ ]⇒ M) = S ℓ [ ∌ ]⇒ (renameₘ (extRenaming ρ) M)

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
subₘ γ (ℓ ⟨ M ⟩) = ℓ ⟨ subₘ γ M ⟩
subₘ γ (S ℓ [ p ]⇒ M) = S ℓ [ p ]⇒ subₘ (extSub γ) M

singleSub : ∀ {Γ A} → Γ ⊢ A → Subst (Γ ⨾ A) Γ
singleSub V Z = V
singleSub V (S x) = ` x

-- Evaluation Contexts

data _⊢_!_⤋_!_ (Γ : Context) (C : Type) (E : Effect) :
  Type → Effect → Set where
  □ : Γ ⊢ C ! E ⤋ C ! E
  `let[_]`in_ : ∀ {A B F} → Γ ⊢ C ! E ⤋ A ! F → Γ ⨾ A ⊢ B ! F
    → Γ ⊢ C ! E ⤋ B ! F
  _⟨[_]⟩ : ∀ {A F} (ℓ : Op) → Γ ⊢ C ! E ⤋ A ! (F , ℓ ⦂ A)
    → Γ ⊢ C ! E ⤋ A ! F

plug : ∀ {Γ A B E F} → Γ ⊢ A ! E ⤋ B ! F → Γ ⊢ A ! E → Γ ⊢ B ! F
plug □ M = M
plug (`let[ ℰ ]`in N) M = `let (plug ℰ M) `in N
plug (ℓ ⟨[ ℰ ]⟩) M = ℓ ⟨ plug ℰ M ⟩

renameₑ : ∀ {Γ Δ A B E F} → Renaming Γ Δ → Γ ⊢ A ! E ⤋ B ! F
  → Δ ⊢ A ! E ⤋ B ! F
renameₑ ρ □ = □
renameₑ ρ (`let[ ℰ ]`in M) = `let[ renameₑ ρ ℰ ]`in (renameₘ (extRenaming ρ) M)
renameₑ ρ (ℓ ⟨[ ℰ ]⟩) = ℓ ⟨[ renameₑ ρ ℰ ]⟩

-- data _∌ᶜ_ : ∀ {Γ A B E F} → Γ ⊢ A ! E ⤋ B ! F → Op → Set where
--   □∌ : ∀ {Γ A E ℓ} → (□ {Γ} {A} {E}) ∌ᶜ ℓ
--   let∌ : ∀ {Γ A B C E F ℓ} {ℰ : Γ ⊢ A ! E ⤋ B ! F} {N : Γ ⨾ B ⊢ C ! F}
--     → ℰ ∌ᶜ ℓ → `let[ ℰ ]`in N ∌ᶜ ℓ
--   ⟨⟩∌ : ∀ {Γ A B E F ℓ ℓ'} {ℰ : Γ ⊢ A ! E ⤋ B ! (F , ℓ' ⦂ B)}
--     → ℓ ≢ ℓ' → ℰ ∌ᶜ ℓ → (ℓ' ⟨[ ℰ ]⟩) ∌ᶜ ℓ
-- infix 5 _∌ᶜ_

data _⊑_ : Effect → Effect → Set where
  ⊑-refl : ∀ {E} → E ⊑ E
  ⊑-snoc : ∀ {E F ℓ A} → E ⊑ F → E ⊑ (F , ℓ ⦂ A)

pop-⊑ : ∀ {E F ℓ A} → (E , ℓ ⦂ A) ⊑ F → E ⊑ F
pop-⊑ ⊑-refl = ⊑-snoc ⊑-refl
pop-⊑ (⊑-snoc ⊑) = ⊑-snoc (pop-⊑ ⊑)

ec-⊑ : ∀ {Γ A B E F} → (ℰ : Γ ⊢ A ! E ⤋ B ! F) → F ⊑ E
ec-⊑ □ = ⊑-refl
ec-⊑ (`let[ ℰ ]`in M) = ec-⊑ ℰ
ec-⊑ (ℓ ⟨[ ℰ ]⟩) = pop-⊑ (ec-⊑ ℰ)

∌-⊑ : ∀ {E F ℓ} → E ⊑ F → F ∌ₑ ℓ → E ∌ₑ ℓ
∌-⊑ ⊑-refl ∌ = ∌
∌-⊑ (⊑-snoc ⊑) ((S ≢) ∌) = (∌-⊑ ⊑) ∌

-- Semantics

data _↝β_ : ∀ {Γ A E} → Γ ⊢ A ! E → Γ ⊢ A ! E → Set where
  β-let : ∀ {Γ A B E} {V : Γ ⊢ B} {M : Γ ⨾ B ⊢ A ! E}
    → `let (`val V) `in M ↝β subₘ (singleSub V) M
  β-· : ∀ {Γ A B E} {M : Γ ⨾ B ⊢ A ! E} {V : Γ ⊢ B}
    → (ƛ M) · V ↝β subₘ (singleSub V) M
  β-⟨⟩ : ∀ {Γ A E ℓ} {V : Γ ⊢ A} → _↝β_ {E = E} (ℓ ⟨ `val V ⟩) (`val V)
  β-S : ∀ {Γ A B E F ℓ p}
    {M : Γ ⨾ B ⇒[ E ] A ⊢ A ! E}
    {ℰ : Γ ⊢ B ! (E , ℓ ⦂ A) ++ F ⤋ A ! (E , ℓ ⦂ A)}
    → ℓ ⟨ plug ℰ (S ℓ [ p ]⇒ M) ⟩
      ↝β subₘ (singleSub (ƛ (ℓ ⟨ plug (renameₑ S_ ℰ) (`val (` Z)) ⟩))) M
infix 4 _↝β_

data _↝_ : ∀ {Γ A E} →  Γ ⊢ A ! E → Γ ⊢ A ! E → Set where
  ξξ : ∀ {Γ A B E F} {M N : Γ ⊢ A ! E} {M' N' : Γ ⊢ B ! F}
    → (ℰ : Γ ⊢ A ! E ⤋ B ! F) → M' ≡ plug ℰ M → N' ≡ plug ℰ N
    → M ↝β N → M' ↝ N'

pattern ξ ℰ β = ξξ ℰ refl refl β

data Progress : ∀ {A E} → ∅ ⊢ A ! E → Set where
  step : ∀ {A E} {M N : ∅ ⊢ A ! E} → M ↝ N → Progress M
  done : ∀ {A E} {V : ∅ ⊢ A} → Progress {E = E} (`val V)
  blocked : ∀ {A B C E F G H ℓ}
    {M : (∅ ⨾ B ⇒[ E ] A) ⊢ A ! E}
    → (p : F ∌ₑ ℓ)
    → (E , ℓ ⦂ A) ++ G ≡ H
    → (ℰ : ∅ ⊢ B ! ((E , ℓ ⦂ A) ++ F) ⤋ C ! H)
    → Progress (plug ℰ (S ℓ [ p ]⇒ M))

progress : ∀ {A E} → (M : ∅ ⊢ A ! E) → Progress M
progress (`val V) = done
progress (`let M `in N) with progress M
... | step (ξ ℰ β) = step (ξ (`let[ ℰ ]`in N) β)
... | done = step (ξ □ β-let)
... | blocked ∌ eq ℰ = blocked ∌ eq (`let[ ℰ ]`in N)
progress ((ƛ M) · V) = step (ξ □ β-·)
progress (ℓ ⟨ M ⟩) with progress M
... | step (ξ ℰ β) = step (ξ (ℓ ⟨[ ℰ ]⟩) β)
... | done = step (ξ □ β-⟨⟩)
... | blocked {ℓ = ℓ'} ∌ eq ℰ with ℓ' ≟ ℓ
...   | yes refl = {!   !}
...   | no neq = blocked ∌ {!  !} {!   !}
progress (S ℓ [ ∌ ]⇒ M) = blocked ∌ refl □


-- -- data PureProgress : ∀ {A} → ∅ ⊢ A ! ε → Set where
-- --   pureStep : ∀ {A} {M N : ∅ ⊢ A ! ε} → M ↝ N → PureProgress M
-- --   pureDone : ∀ {A} {V : ∅ ⊢ A} → PureProgress (`val V)

-- -- pureProgress : ∀ {A} → (M : ∅ ⊢ A ! ε) → PureProgress M
-- -- pureProgress (`val V) = pureDone
-- -- pureProgress (`let M `in N) with pureProgress M
-- -- ... | pureStep (ξ ℰ β) = pureStep (ξ (`let[ ℰ ]`in N) β)
-- -- ... | pureDone = pureStep (ξ □ β-let)
-- -- pureProgress ((ƛ M) · V) = pureStep (ξ □ β-·)
-- -- pureProgress ⟨ M ⟩ with progress M
-- -- ... | step (ξ ℰ β) = pureStep (ξ ⟨[ ℰ ]⟩ β)
-- -- ... | done = pureStep (ξ □ β-⟨⟩)
-- -- ... | blocked ℰ with pureEC ℰ
-- -- ...   | refl = pureStep (ξ □ β-S0)

