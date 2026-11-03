module STLCIntrinsic where

open import Data.Nat using (ℕ; zero; suc; _<_; z<s; s<s; _≤_; z≤n; s≤s; _≤?_)
open import Data.Product using (∃-syntax; _,_) renaming (_×_ to _∧_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (True; toWitness)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; refl; subst; cong; cong₂)
open Eq.≡-Reasoning

data Type : Set where
  _⇒_ : Type → Type → Type
  _×_ : Type → Type → Type
  `1 : Type

data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → (Γ , A) ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → (Γ , B) ∋ A

data _⊢ᵥ_ : Context → Type → Set
data _⊢ₘ_ : Context → Type → Set

data _⊢ᵥ_ where
  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ᵥ A
  ƛ_ : ∀ {Γ A B} → (Γ , A) ⊢ₘ B → Γ ⊢ᵥ (A ⇒ B)
  ⟨_,_⟩ : ∀ {Γ A B} → Γ ⊢ᵥ A → Γ ⊢ᵥ B → Γ ⊢ᵥ (A × B)
  `unit : ∀ {Γ} → Γ ⊢ᵥ `1

data _⊢ₘ_ where
  `val_ : ∀ {Γ A} → Γ ⊢ᵥ A → Γ ⊢ₘ A
  `let_`in_ : ∀ {Γ A B} → Γ ⊢ₘ A → (Γ , A) ⊢ₘ B → Γ ⊢ₘ B
  _·_ : ∀ {Γ A B} → Γ ⊢ᵥ (A ⇒ B) → Γ ⊢ᵥ A → Γ ⊢ₘ B
  π₁_ : ∀ {Γ A B} → Γ ⊢ᵥ (A × B) → Γ ⊢ₘ A
  π₂_ : ∀ {Γ A B} → Γ ⊢ᵥ (A × B) → Γ ⊢ₘ B

size : Context → ℕ
size ∅ = zero
size (Γ , _) = suc (size Γ)

lookup : {Γ : Context} → {n : ℕ} → n < size Γ → Type
lookup {Γ , A} {zero} _ = A
lookup {Γ , x} {suc n} (s≤s ev) = lookup ev

count : ∀ {Γ} → {n : ℕ} → (p : n < size Γ) → Γ ∋ (lookup p)
count {_ , _} {zero} p = Z
count {Γ , _} {n = suc n} (s≤s p) = S count p

#_ : ∀ {Γ} → (n : ℕ) → {n∈Γ : True (suc n ≤? size Γ)}
  → Γ ⊢ᵥ lookup (toWitness n∈Γ)
#_ n {n∈Γ} = ` count (toWitness n∈Γ)

_⊆_ : Context → Context → Set
Γ ⊆ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

ext : ∀ {Γ Δ A} → Γ ⊆ Δ → (Γ , A) ⊆ (Δ , A)
ext Γ⊆Δ Z = Z
ext {A = B} Γ⊆Δ (S Γ∋A) = S (Γ⊆Δ Γ∋A)

renameᵥ : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ ⊢ᵥ A → Δ ⊢ᵥ A
renameₘ : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ ⊢ₘ A → Δ ⊢ₘ A

renameᵥ Γ⊆Δ (` x) = ` Γ⊆Δ x
renameᵥ Γ⊆Δ (ƛ M) = ƛ renameₘ (ext  Γ⊆Δ) M
renameᵥ Γ⊆Δ ⟨ V , W ⟩ = ⟨ renameᵥ Γ⊆Δ V , renameᵥ Γ⊆Δ W ⟩
renameᵥ Γ⊆Δ `unit = `unit

renameₘ Γ⊆Δ (`val V) = `val renameᵥ Γ⊆Δ V
renameₘ Γ⊆Δ (`let_`in_ M N) = `let renameₘ Γ⊆Δ M `in renameₘ (ext Γ⊆Δ) N
renameₘ Γ⊆Δ (V · W) = renameᵥ Γ⊆Δ V · renameᵥ Γ⊆Δ W
renameₘ Γ⊆Δ (π₁ V) = π₁ renameᵥ Γ⊆Δ V
renameₘ Γ⊆Δ (π₂ V) = π₂ renameᵥ Γ⊆Δ V

Subst : Context → Context → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ᵥ A

extSub : ∀ {Γ Δ A} → Subst Γ Δ → Subst (Γ , A) (Δ , A)
extSub γ Z = ` Z
extSub {A = B} γ (S Γ∋A) = renameᵥ S_ (γ Γ∋A)

subᵥ : ∀ {Γ Δ A} → Subst Γ Δ → Γ ⊢ᵥ A → Δ ⊢ᵥ A
subₘ : ∀ {Γ Δ A} → Subst Γ Δ → Γ ⊢ₘ A → Δ ⊢ₘ A

subᵥ γ (` x) = γ x
subᵥ γ (ƛ M) = ƛ subₘ (extSub γ) M
subᵥ γ ⟨ V , W ⟩ = ⟨ subᵥ γ V , subᵥ γ W ⟩
subᵥ γ `unit = `unit

subₘ γ (`val V) = `val (subᵥ γ V)
subₘ γ (`let M `in N) = `let subₘ γ M `in subₘ (extSub γ) N
subₘ γ (V · W) = subᵥ γ V · subᵥ γ W
subₘ γ (π₁ V) = π₁ (subᵥ γ V)
subₘ γ (π₂ V) = π₂ (subᵥ γ V)

_▶_ : ∀ {Δ Γ A} → Subst Γ Δ → Δ ⊢ᵥ A → Subst (Γ , A) Δ
(γ ▶ V) Z     = V
(γ ▶ V) (S x) = γ x

γ₀ : ∀ {Γ A} → Γ ⊢ᵥ A → Subst (Γ , A) Γ
γ₀ V Z = V
γ₀ V (S x) = ` x

_[_]ᵥ : ∀ {Γ A B} → (Γ , A) ⊢ᵥ B → Γ ⊢ᵥ A → Γ ⊢ᵥ B
_[_]ᵥ {Γ} {A} {B} V W = subᵥ (γ₀ W) V

_[_]ₘ : ∀ {Γ A B} → (Γ , A) ⊢ₘ B → Γ ⊢ᵥ A → Γ ⊢ₘ B
_[_]ₘ {Γ} {A} {B} M V = subₘ (γ₀ V) M

data _↝β_ : ∀ {Γ A} → Γ ⊢ₘ A → Γ ⊢ₘ A → Set where
  β-let : ∀ {Γ A B} {M : ((Γ , A) ⊢ₘ B)} {V : Γ ⊢ᵥ A}
    → (`let (`val V) `in M) ↝β (M [ V ]ₘ)
  β-· :  ∀ {Γ A B} {M : ((Γ , A) ⊢ₘ B)} {V : Γ ⊢ᵥ A}
    → ((ƛ M) · V) ↝β (M [ V ]ₘ)
  β-π₁ : ∀ {Γ A B} {V : Γ ⊢ᵥ A} {W : Γ ⊢ᵥ B} → (π₁ ⟨ V , W ⟩) ↝β (`val V)
  β-π₂ : ∀ {Γ A B} {V : Γ ⊢ᵥ A} {W : Γ ⊢ᵥ B} → (π₂ ⟨ V , W ⟩) ↝β (`val W)

data _⊢ₑ_⇒_ (Γ : Context) (C : Type) : Type → Set where
  □ : Γ ⊢ₑ C ⇒ C
  `let[_]`in_ : ∀ {A B} → Γ ⊢ₑ C ⇒ A → (Γ , A) ⊢ₘ B → Γ ⊢ₑ C ⇒ B

_⟦_⟧ : ∀ {Γ A B} → Γ ⊢ₑ A ⇒ B → Γ ⊢ₘ A → Γ ⊢ₘ B
□ ⟦ M ⟧ = M
(`let[ E ]`in N) ⟦ M ⟧ = `let E ⟦ M ⟧ `in N

data _↝_ : ∀ {Γ A} →  Γ ⊢ₘ A → Γ ⊢ₘ A → Set where
  ξξ : ∀ {Γ A B} {M N : Γ ⊢ₘ A} {M' N' : Γ ⊢ₘ B} →
    (E : Γ ⊢ₑ A ⇒ B) → M' ≡ E ⟦ M ⟧ → N' ≡ E ⟦ N ⟧ → M ↝β N → M' ↝ N'

pattern ξ E M—→N = ξξ E refl refl M—→N

_●_ : ∀ {Γ A B C} (E : Γ ⊢ₑ B ⇒ C) → (F : Γ ⊢ₑ A ⇒ B) → (Γ ⊢ₑ A ⇒ C)
□ ● F = F
(`let[ E ]`in M) ● F = `let[ E ● F ]`in M

plug-● : ∀ {Γ A B C} (E : Γ ⊢ₑ B ⇒ C) → (F : Γ ⊢ₑ A ⇒ B) (M : Γ ⊢ₘ A)
  → E ⟦ F ⟦ M ⟧ ⟧ ≡ (E ● F) ⟦ M ⟧
plug-● □ F M = refl
plug-● (`let[ E ]`in x) F M = cong (`let_`in x) (plug-● E F M)

data _↠_ : ∀ {Γ A} →  Γ ⊢ₘ A → Γ ⊢ₘ A → Set where
  ↠-refl : ∀ {Γ A} {M : Γ ⊢ₘ A} → M ↠ M
  ↠-trans : ∀ {Γ A} {M N : Γ ⊢ₘ A} (L : Γ ⊢ₘ A) →
     M ↝ L →  L ↠ N → M ↠ N

_++↠_ : ∀ {Γ A} {M₀ M₁ M₂ : Γ ⊢ₘ A} → M₀ ↠ M₁ → M₁ ↠ M₂ → M₀ ↠ M₂
↠-refl ++↠ M₁↠M₂ = M₁↠M₂
(↠-trans N M₀↝N N↠M₁) ++↠ M₁↠M₂ = ↠-trans N M₀↝N (N↠M₁ ++↠ M₁↠M₂)

ξ-cong : ∀ {Γ A B} {M N : Γ ⊢ₘ A} (E : Γ ⊢ₑ A ⇒ B)
  → M ↠ N → (E ⟦ M ⟧) ↠ (E ⟦ N ⟧)
ξ-cong E ↠-refl = ↠-refl
ξ-cong E (↠-trans L (ξ F ↝β) L↠N) =
  ↠-trans
    (E ⟦ L ⟧)
    (ξξ (E ● F) (plug-● E F _) (plug-● E F _) ↝β)
    (ξ-cong E L↠N)

_++↠⟨_⟩_ : ∀ {Γ A} {M M' N N' : Γ ⊢ₘ A} → M ↠ M' → M' ↝ N → N ↠ N' → M ↠ N'
↠-refl ++↠⟨ M'↝N ⟩ N↠N' = ↠-trans _ M'↝N N↠N'
↠-trans L M↝L L↠M' ++↠⟨ M'↝N ⟩ N↠N' = ↠-trans L M↝L (L↠M' ++↠⟨ M'↝N ⟩ N↠N')

data Progress {A} (M : ∅ ⊢ₘ A) : Set where
  step : ∀ {N} → M ↝ N → Progress M
  done : ∀ {V} → M ≡ `val V → Progress M

progress : ∀ {A} → (M : ∅ ⊢ₘ A) → Progress M
progress (`val V) = done refl
progress (`let M `in N) with progress M
... | step (ξ E ↝β) = step (ξ (`let[ E ]`in N) ↝β)
... | done refl = step (ξ □ β-let)
progress ((ƛ M) · W) = step (ξ □ β-·)
progress (π₁ ⟨ V , W ⟩) = step (ξ □ β-π₁)
progress (π₂ ⟨ V , W ⟩) = step (ξ □ β-π₂)

length : ∀ {A} {M N : ∅ ⊢ₘ A} → M ↠ N → ℕ
length (↠-refl) = zero
length (↠-trans L M↝L L↠N) = suc (length L↠N)


_⇓ : ∀ {Γ A} → (Γ ⊢ₘ A) → Set
_⇓ M = ∃[ V ] M ↠ (`val V)

V⟦_⟧∋_ : (A : Type) → ∅ ⊢ᵥ A → Set
M⟦_⟧∋_ : (A : Type) → ∅ ⊢ₘ A → Set

V⟦ A ⇒ B ⟧∋ (ƛ M) = ∀ V → V⟦ A ⟧∋ V → M⟦ B ⟧∋ (M [ V ]ₘ)
V⟦ A × B ⟧∋ ⟨ V , W ⟩ = (V⟦ A ⟧∋ V) ∧ (V⟦ B ⟧∋ W)
V⟦ `1 ⟧∋ `unit = ⊤

M⟦ A ⟧∋ M = ∃[ V ] (M ↠ (`val V) ∧ V⟦ A ⟧∋ V)

G⟦_⟧∋_ : (Γ : Context) → Subst Γ ∅ → Set
G⟦ Γ ⟧∋ γ = ∀ {A} (x : Γ ∋ A) → V⟦ A ⟧∋ γ x

G-ext : ∀ {Γ A} {γ : Subst Γ ∅} {V : ∅ ⊢ᵥ A} →
  G⟦ Γ ⟧∋ γ → V⟦ A ⟧∋ V → G⟦ Γ , A ⟧∋ (γ ▶ V)
G-ext ∋γ ∋V Z = ∋V
G-ext ∋γ ∋V (S x) = ∋γ x

_≐_ : ∀ {Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
γ₁ ≐ γ₂ = ∀ {A} (x : _ ∋ A) → γ₁ x ≡ γ₂ x

_∘_ : ∀ {Γ₀ Γ₁ Γ₂} → Subst Γ₁ Γ₂ → Subst Γ₀ Γ₁ → Subst Γ₀ Γ₂
(γ₁ ∘ γ₂) x = subᵥ γ₁ (γ₂ x)


ext-sub-rename : ∀ {Γ Γ' Δ A} {ρ : Γ ⊆ Γ'} {γ : Subst Γ Δ} {γ' : Subst Γ' Δ}
  → (∀ {B} (x : Γ ∋ B) → γ' (ρ x) ≡ γ x)
  → ∀ {B} (x : (Γ , A) ∋ B) → extSub γ' (ext ρ x) ≡ extSub γ x
ext-sub-rename h Z = refl
ext-sub-rename h (S x) = cong (renameᵥ S_) (h x)


sub-renameᵥ : ∀ {Γ Γ' Δ A} {ρ : Γ ⊆ Γ'} {γ : Subst Γ Δ} {γ' : Subst Γ' Δ}
  → (V : Γ ⊢ᵥ A) → (∀ {B} (x : Γ ∋ B) → γ' (ρ x) ≡ γ x)
  → subᵥ γ' (renameᵥ ρ V) ≡ subᵥ γ V
sub-renameₘ : ∀ {Γ Γ' Δ A} {ρ : Γ ⊆ Γ'} {γ : Subst Γ Δ} {γ' : Subst Γ' Δ}
  → (M : Γ ⊢ₘ A) → (∀ {B} (x : Γ ∋ B) → γ' (ρ x) ≡ γ x)
  → subₘ γ' (renameₘ ρ M) ≡ subₘ γ M

sub-renameᵥ (` x) h = h x
sub-renameᵥ (ƛ M) h = cong ƛ_ (sub-renameₘ M (ext-sub-rename h))
sub-renameᵥ ⟨ V , W ⟩ h = cong₂ ⟨_,_⟩ (sub-renameᵥ V h) (sub-renameᵥ W h)
sub-renameᵥ `unit h = refl

sub-renameₘ (`val V) h = cong `val_ (sub-renameᵥ V h)
sub-renameₘ (`let M `in N) h =
    cong₂ `let_`in_ (sub-renameₘ M h) (sub-renameₘ N (ext-sub-rename h))
sub-renameₘ (V · W) h = cong₂ _·_ (sub-renameᵥ V h) (sub-renameᵥ W h)
sub-renameₘ (π₁ V) h = cong π₁_ (sub-renameᵥ V h)
sub-renameₘ (π₂ V) h = cong π₂_ (sub-renameᵥ V h)

ext-ext : ∀ {Γ Δ Θ A B} {ρ₁ : Γ ⊆ Δ} {ρ₂ : Δ ⊆ Θ} {ρ₃ : Γ ⊆ Θ}
  → (∀ {C} (x : Γ ∋ C) → ρ₂ (ρ₁ x) ≡ ρ₃ x)
  → (x : (Γ , B) ∋ A) → ext ρ₂ (ext ρ₁ x) ≡ ext ρ₃ x
ext-ext h Z = refl
ext-ext h (S x) = cong S_ (h x)

rename-renameᵥ : ∀ {Γ Δ Θ A} {ρ₁ : Γ ⊆ Δ} {ρ₂ : Δ ⊆ Θ} {ρ₃ : Γ ⊆ Θ}
  → (∀ {B} (x : Γ ∋ B) → ρ₂ (ρ₁ x) ≡ ρ₃ x) → (V : Γ ⊢ᵥ A)
  → renameᵥ ρ₂ (renameᵥ ρ₁ V) ≡ renameᵥ ρ₃ V
rename-renameₘ : ∀ {Γ Δ Θ A} {ρ₁ : Γ ⊆ Δ} {ρ₂ : Δ ⊆ Θ} {ρ₃ : Γ ⊆ Θ}
  → (∀ {B} (x : Γ ∋ B) → ρ₂ (ρ₁ x) ≡ ρ₃ x) → (M : Γ ⊢ₘ A)
  → renameₘ ρ₂ (renameₘ ρ₁ M) ≡ renameₘ ρ₃ M

rename-renameᵥ h (` x) = cong `_ (h x)
rename-renameᵥ h (ƛ M) = cong ƛ_ (rename-renameₘ (ext-ext h) M)
rename-renameᵥ h ⟨ V , W ⟩ =
  cong₂ ⟨_,_⟩ (rename-renameᵥ h V) (rename-renameᵥ h W)
rename-renameᵥ h `unit = refl

rename-renameₘ h (`val V) = cong `val_ (rename-renameᵥ h V)
rename-renameₘ h (`let M `in N) =
  cong₂ `let_`in_ (rename-renameₘ h M) (rename-renameₘ (ext-ext h) N)
rename-renameₘ h (V · W) = cong₂ _·_ (rename-renameᵥ h V) (rename-renameᵥ h W)
rename-renameₘ h (π₁ V) = cong π₁_ (rename-renameᵥ h V)
rename-renameₘ h (π₂ V) = cong π₂_ (rename-renameᵥ h V)

ext-rename-sub : ∀ {Γ Δ Δ' B} {ρ : Δ ⊆ Δ'} (γ : Subst Γ Δ)
  → (λ x → renameᵥ (ext ρ) (extSub γ x))
    ≐ extSub {A = B} (λ y → renameᵥ ρ (γ y))
ext-rename-sub γ Z = refl
ext-rename-sub {ρ = ρ} γ (S x) =
  begin
    renameᵥ (ext ρ) (renameᵥ S_ (γ x))
  ≡⟨ rename-renameᵥ (λ _ → refl) (γ x) ⟩
    renameᵥ (λ y → S (ρ y)) (γ x)
  ≡⟨ sym (rename-renameᵥ (λ _ → refl) (γ x)) ⟩
    renameᵥ S_ (renameᵥ ρ (γ x))
  ∎

ext-cong : ∀ {Γ Δ A} {γ γ' : Subst Γ Δ}
  → γ ≐ γ' → (extSub {A = A} γ) ≐ extSub γ'
ext-cong h Z = refl
ext-cong h (S x) = cong (renameᵥ S_) (h x)

sub-congᵥ : ∀ {Γ Δ A} {γ γ' : Subst Γ Δ}
  → γ ≐ γ' → (V : Γ ⊢ᵥ A) → subᵥ γ V ≡ subᵥ γ' V
sub-congₘ : ∀ {Γ Δ A} {γ γ' : Subst Γ Δ}
  → γ ≐ γ' → (M : Γ ⊢ₘ A) → subₘ γ M ≡ subₘ γ' M

sub-congᵥ h (` x) = h x
sub-congᵥ h (ƛ M) = cong ƛ_ (sub-congₘ (ext-cong h) M)
sub-congᵥ h ⟨ V , W ⟩ = cong₂ ⟨_,_⟩ (sub-congᵥ h V) (sub-congᵥ h W)
sub-congᵥ h `unit = refl

sub-congₘ h (`val V) = cong `val_ (sub-congᵥ h V)
sub-congₘ h (`let M `in N) =
  cong₂ `let_`in_ (sub-congₘ h M) (sub-congₘ (ext-cong h) N)
sub-congₘ h (V · W) = cong₂ _·_ (sub-congᵥ h V) (sub-congᵥ h W)
sub-congₘ h (π₁ V) = cong π₁_ (sub-congᵥ h V)
sub-congₘ h (π₂ V) = cong π₂_ (sub-congᵥ h V)

rename-subᵥ : ∀ {Γ Δ Δ' A} (ρ : Δ ⊆ Δ') (γ : Subst Γ Δ) (V : Γ ⊢ᵥ A)
  → renameᵥ ρ (subᵥ γ V) ≡ subᵥ (λ x → renameᵥ ρ (γ x)) V
rename-subₘ : ∀ {Γ Δ Δ' A} (ρ : Δ ⊆ Δ') (γ : Subst Γ Δ) (M : Γ ⊢ₘ A)
  → renameₘ ρ (subₘ γ M) ≡ subₘ (λ x → renameᵥ ρ (γ x)) M
rename-subᵥ ρ γ (` x) = refl
rename-subᵥ ρ γ (ƛ M) = cong ƛ_ (
    begin
      renameₘ (ext ρ) (subₘ (extSub γ) M)
    ≡⟨ rename-subₘ (ext ρ) (extSub γ) M ⟩
      subₘ (λ x → renameᵥ (ext ρ) ((extSub γ) x)) M
    ≡⟨ sub-congₘ (ext-rename-sub γ) M ⟩
      subₘ (extSub (λ x → renameᵥ ρ (γ x))) M
    ∎
  )
rename-subᵥ ρ γ ⟨ V , W ⟩ = cong₂ ⟨_,_⟩ (rename-subᵥ ρ γ V) (rename-subᵥ ρ γ W)
rename-subᵥ ρ γ `unit = refl

rename-subₘ ρ γ (`val V) = cong `val_ (rename-subᵥ ρ γ V)
rename-subₘ ρ γ (`let M `in N) = cong₂ `let_`in_ (rename-subₘ ρ γ M) (
    begin
      renameₘ (ext ρ) (subₘ (extSub γ) N)
    ≡⟨ rename-subₘ (ext ρ) (extSub γ) N ⟩
      subₘ (λ x → renameᵥ (ext ρ) ((extSub γ) x)) N
    ≡⟨ sub-congₘ (ext-rename-sub γ) N ⟩
      subₘ (extSub (λ x → renameᵥ ρ (γ x))) N
    ∎
  )
rename-subₘ ρ γ (V · W) = cong₂ _·_ (rename-subᵥ ρ γ V) (rename-subᵥ ρ γ W)
rename-subₘ ρ γ (π₁ V) = cong π₁_ (rename-subᵥ ρ γ V)
rename-subₘ ρ γ (π₂ V) = cong π₂_ (rename-subᵥ ρ γ V)

ext-∘ : ∀ {Γ₀ Γ₁ Γ₂ A}
  {γ₁ : Subst Γ₀ Γ₁} {γ₂ : Subst Γ₁ Γ₂} {γ₂γ₁ : Subst Γ₀ Γ₂}
  → (γ₂ ∘ γ₁) ≐ γ₂γ₁
  → ((extSub {A = A} γ₂) ∘ (extSub γ₁)) ≐ (extSub γ₂γ₁)
ext-∘ eq Z = refl
ext-∘ {γ₁ = γ₁} {γ₂ = γ₂} {γ₂γ₁ = γ₂γ₁} eq (S ∋x) =
  begin
    (extSub γ₂ ∘ extSub γ₁) (S ∋x)
  ≡⟨⟩
    subᵥ (extSub γ₂) (renameᵥ S_ (γ₁ ∋x))
  ≡⟨ sub-renameᵥ (γ₁ ∋x) (λ _ → refl) ⟩
    subᵥ (λ x → renameᵥ S_ (γ₂ x)) (γ₁ ∋x)
  ≡⟨ sym (rename-subᵥ S_ γ₂ (γ₁ ∋x)) ⟩
    renameᵥ S_ (subᵥ γ₂ (γ₁ ∋x))
  ≡⟨ cong (renameᵥ S_) (eq ∋x) ⟩
    renameᵥ S_ (γ₂γ₁ ∋x)
  ∎


sub-subᵥ : ∀ {Γ₀ Γ₁ Γ₂ A}
  {γ₁ : Subst Γ₀ Γ₁} {γ₂ : Subst Γ₁ Γ₂} {γ₂γ₁ : Subst Γ₀ Γ₂}
  → (V : Γ₀ ⊢ᵥ A) → (γ₂ ∘ γ₁) ≐ γ₂γ₁
  → subᵥ γ₂ (subᵥ γ₁ V) ≡ subᵥ γ₂γ₁ V
sub-subₘ : ∀ {Γ₀ Γ₁ Γ₂ A}
  {γ₁ : Subst Γ₀ Γ₁} {γ₂ : Subst Γ₁ Γ₂} {γ₂γ₁ : Subst Γ₀ Γ₂}
  → (M : Γ₀ ⊢ₘ A) → (γ₂ ∘ γ₁) ≐ γ₂γ₁
  → subₘ γ₂ (subₘ γ₁ M) ≡ subₘ γ₂γ₁ M

sub-subᵥ (` x) γeq = γeq x
sub-subᵥ (ƛ M) γeq = cong ƛ_ (sub-subₘ M (ext-∘ γeq))
sub-subᵥ ⟨ V , W ⟩ γeq = cong₂ ⟨_,_⟩ (sub-subᵥ V γeq) (sub-subᵥ W γeq)
sub-subᵥ `unit  γeq = refl

sub-subₘ (`val V) γeq = cong `val_ (sub-subᵥ V γeq)
sub-subₘ (`let M `in N) γeq =
  cong₂ `let_`in_ (sub-subₘ M γeq) (sub-subₘ N (ext-∘ γeq))
sub-subₘ (V · W) γeq = cong₂ _·_ (sub-subᵥ V γeq) (sub-subᵥ W γeq)
sub-subₘ (π₁ V) γeq = cong π₁_ (sub-subᵥ V γeq)
sub-subₘ (π₂ V) γeq = cong π₂_ (sub-subᵥ V γeq)

ext-id : ∀ {Γ A} {γ : Subst Γ Γ} → γ ≐ (λ x → ` x)
  → (extSub {A = A} γ) ≐ (λ x → ` x)
ext-id h Z = refl
ext-id {γ = γ} h (S x) = begin
    renameᵥ S_ (γ x)
  ≡⟨ cong (renameᵥ S_) (h x) ⟩
    renameᵥ S_ (` x)
  ≡⟨⟩
    ` (S x)
  ∎

sub-idᵥ : ∀ {Γ A} {γ : Subst Γ Γ} → (V : Γ ⊢ᵥ A)
  → γ ≐ (λ y → ` y) → subᵥ γ V ≡ V
sub-idₘ : ∀ {Γ A} {γ : Subst Γ Γ} → (M : Γ ⊢ₘ A)
  → γ ≐ (λ y → ` y) → subₘ γ M ≡ M

sub-idᵥ (` x) h = h x
sub-idᵥ (ƛ M) h = cong ƛ_ (sub-idₘ M (ext-id h))
sub-idᵥ ⟨ V , W ⟩ h = cong₂ ⟨_,_⟩ (sub-idᵥ V h) (sub-idᵥ W h)
sub-idᵥ `unit h = refl

sub-idₘ (`val V) h = cong `val_ (sub-idᵥ V h)
sub-idₘ (`let M `in N) h = cong₂ `let_`in_ (sub-idₘ M h) (sub-idₘ N (ext-id h))
sub-idₘ (V · W) h = cong₂ _·_ (sub-idᵥ V h) (sub-idᵥ W h)
sub-idₘ (π₁ V) h = cong π₁_ (sub-idᵥ V h)
sub-idₘ (π₂ V) h = cong π₂_ (sub-idᵥ V h)

γ₀-∘ : ∀ {Γ A} (γ : Subst Γ ∅) (V : ∅ ⊢ᵥ A) → ((γ₀ V) ∘ extSub γ) ≐ (γ ▶ V)
γ₀-∘ γ V Z = refl
γ₀-∘ γ V (S x) = begin
    (γ₀ V ∘ extSub γ) (S x)
  ≡⟨⟩
    subᵥ (γ₀ V) (renameᵥ S_ (γ x))
  ≡⟨ sub-renameᵥ (γ x) (λ _ → refl) ⟩
    subᵥ (λ y → ` y) (γ x)
  ≡⟨ sub-idᵥ (γ x) (λ y → refl) ⟩
    γ x
  ≡⟨⟩
    (γ ▶ V) (S x)
  ∎

ext-single : ∀ {Γ A B} (γ : Subst Γ ∅) (V : ∅ ⊢ᵥ A) (M : (Γ , A) ⊢ₘ B)
  → (subₘ (extSub γ) M) [ V ]ₘ ≡ subₘ (γ ▶ V) M
ext-single γ V M = sub-subₘ M (γ₀-∘ γ V)

Semᵥ : (Γ : Context) → (A : Type) → (V : Γ ⊢ᵥ A) → Set
Semᵥ Γ A V = ∀ (γ : Subst Γ ∅) → G⟦ Γ ⟧∋ γ → V⟦ A ⟧∋ (subᵥ γ V)

Semₘ : (Γ : Context) → (A : Type) → (M : Γ ⊢ₘ A) → Set
Semₘ Γ A M = ∀ (γ : Subst Γ ∅) → G⟦ Γ ⟧∋ γ → M⟦ A ⟧∋ (subₘ γ M)

syntax Semᵥ Γ A V = Γ ⊨ᵥ V ⦂ A
syntax Semₘ Γ A M = Γ ⊨ₘ M ⦂ A

fundᵥ : ∀ {Γ A} (V : Γ ⊢ᵥ A) → Γ ⊨ᵥ V ⦂ A
fundₘ : ∀ {Γ A} (M : Γ ⊢ₘ A) → Γ ⊨ₘ M ⦂ A

fundᵥ (` x) γ Gγ = Gγ x
fundᵥ (ƛ_ {B = B} M) γ Gγ V ∋V rewrite ext-single γ V M =
  fundₘ M (γ ▶ V) (G-ext Gγ ∋V)
fundᵥ ⟨ V , W ⟩ γ Gγ = fundᵥ V γ Gγ , fundᵥ W γ Gγ
fundᵥ `unit γ Gγ = tt

fundₘ (`val V) γ Gγ = subᵥ γ V , ↠-refl , fundᵥ V γ Gγ
fundₘ (`let M `in N) γ Gγ with fundₘ M γ Gγ
... | V , M↠V , ∋V with fundₘ N (γ ▶ V) (G-ext Gγ ∋V)
... | W , N↠W , ∋W = W ,
      (ξ-cong (`let[ □ ]`in subₘ (extSub γ) N) M↠V
        ++↠⟨ ξξ □ refl (sym (ext-single γ V N)) β-let ⟩
        N↠W) ,
      ∋W
fundₘ (V · W) γ Gγ with subᵥ γ V | fundᵥ V γ Gγ
... | ƛ M | ∋V with ∋V (subᵥ γ W) (fundᵥ W γ Gγ)
... | U , MW↠U , ∋U =
      U ,
      ↠-trans (subₘ (γ₀ (subᵥ γ W)) M) (ξ □ β-·) MW↠U ,
      ∋U
fundₘ (π₁ V) γ Gγ with subᵥ γ V | fundᵥ V γ Gγ
... | ⟨ W , _ ⟩ | ∋W , _ = W , (↠-trans (`val W) (ξ □ β-π₁) ↠-refl) , ∋W
fundₘ (π₂ V) γ Gγ with subᵥ γ V | fundᵥ V γ Gγ
... | ⟨ _ , W ⟩ | _ , ∋W = W , (↠-trans (`val W) (ξ □ β-π₂) ↠-refl) , ∋W

normalization : ∀ {A} → (M : ∅ ⊢ₘ A) → M ⇓
normalization M with fundₘ M (λ ()) (λ ())
... | V , M↠V , _ = V , subst (_↠ (`val V)) (sub-idₘ M  λ ()) M↠V