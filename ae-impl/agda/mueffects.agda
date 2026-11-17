open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

module MuEffects (Op : Set) (_≟_ : (a b : Op) → Dec (a ≡ b)) where

data Effect : Set where
  ∅ : Effect
  _,_↦_ : Effect → Op → Effect → Effect

_∋_ : Effect → Op → Maybe Effect
∅ ∋ op = nothing
(E , op' ↦ F) ∋ op with op ≟ op'
... | yes _ = just F
... | no _ = E ∋ op


_⊔_ : Effect → Effect → Effect
_⊔?_ : Effect → Maybe Effect → Effect

∅ ⊔ F = F
(E , op ↦ E') ⊔ F = (E ⊔ F) , op ↦ (E' ⊔? (F ∋ op))

E ⊔? just F = E ⊔ F
E ⊔? nothing = E

comb : Maybe Effect → Maybe Effect → Maybe Effect
comb (just E) MF = just (E ⊔? MF)
comb nothing MF = MF

∋-⊔ : ∀ {E F op} → (E ⊔ F) ∋ op ≡ comb (E ∋ op) (F ∋ op)
∋-⊔ {∅} = refl
∋-⊔ {E , op' ↦ E'} {F} {op} with op ≟ op'
... | yes refl = refl
... | no _ = ∋-⊔ {E} {F}



⊔-assoc : ∀ {E F G} → ((E ⊔ F) ⊔ G) ≡ (E ⊔ (F ⊔ G))
⊔?-comb : ∀ {E MF MG} → (E ⊔? MF) ⊔? MG ≡ E ⊔? comb MF MG

⊔-assoc {∅} = refl
⊔-assoc {E , op ↦ E'} {F} {G} =
  begin
    ((E , op ↦ E') ⊔ F) ⊔ G
  ≡⟨⟩
    ((E ⊔ F) ⊔ G) , op ↦ ((E' ⊔? (F ∋ op)) ⊔? (G ∋ op))
  ≡⟨ cong (λ x → (x , op ↦ ((E' ⊔? (F ∋ op)) ⊔? (G ∋ op))))
    (⊔-assoc {E} {F} {G}) ⟩
    ((E ⊔ (F ⊔ G)) , op ↦ ((E' ⊔? (F ∋ op)) ⊔? (G ∋ op)))
  ≡⟨ cong (λ x → (E ⊔ (F ⊔ G)) , op ↦ x) (⊔?-comb {E'} {F ∋ op} {G ∋ op}) ⟩
    ((E ⊔ (F ⊔ G)) , op ↦ (E' ⊔? comb (F ∋ op) (G ∋ op)))
  ≡⟨ cong (λ x →  (E ⊔ (F ⊔ G)) , op ↦ (E' ⊔? x)) (sym (∋-⊔ {F} {G} {op})) ⟩
    ((E ⊔ (F ⊔ G)) , op ↦ (E' ⊔? ((F ⊔ G) ∋ op)))
  ≡⟨⟩
    (E , op ↦ E') ⊔ (F ⊔ G)
  ∎

⊔?-comb {E} {just F} {just G} = ⊔-assoc {E} {F} {G}
⊔?-comb {E} {just F} {nothing} = refl
⊔?-comb {E} {nothing} {just G} = refl
⊔?-comb {E} {nothing} {nothing} = refl

⊔-comm : ∀ E F → E ⊔ F ≡ F ⊔ E
⊔-comm ∅ ∅ = refl
⊔-comm (E , op ↦ E') ∅ = {!   !}
⊔-comm E (F , x ↦ F₁) = {!   !}