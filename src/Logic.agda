module Logic where

open import Introduction using (ℕ ; succ ; zero; pred)

-- PREDICATE LOGIC

-- conjunction (same as product !)

data _∧_ (A B : Set) : Set where
  _&_ : A → B → A ∧ B

-- ∧-elimination

fst : {A B : Set} → A ∧ B → A
fst (a & b) = a

snd : {A B : Set} → A ∧ B → B
snd (a & b) = b

-- disjunction (same as sum !)

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

-- ∨-elimination

case : {A B C : Set} → A ∨ B → (A → C) → (B → C) → C
case (inl a) f g = f a
case (inr b) f g = g b

-- true and false

data ⊤ : Set where
  ⟨⟩ : ⊤

data ⊥ : Set where          -- False has not habitant

-- ⊥-elim (absurd pattern () is telling us ⊥ implies anything)

nocase : {A : Set} → ⊥ → A
nocase ()

-- negation

¬ : Set → Set
¬ A = A → ⊥

-- implication (we need a constructor in Agda)

data _⇒_ (A B : Set) : Set where
  fun : (A → B) → A ⇒ B

-- equivalence

_⇔_ : Set → Set → Set
A ⇔ B = (A ⇒ B) ∧ (B ⇒ A)
  
-- application

apply : {A B : Set} → A ⇒ B → A → B
apply (fun f) a = f a

---- PROPOSITIONAL LOGIC

-- universal

data Forall (A : Set) (B : A → Set) : Set where -- ∀ = \all
  ∀' : ((a : A) → B a) → Forall A B 

-- ∀-elim

∀-elim : {A : Set}{B : A → Set} → Forall A B → (a : A) → B a
∀-elim (∀' f) a = f a

-- existential

data ∃ (A : Set)(B : A → Set) : Set where
  [_,_] : (a : A) → B a → ∃ A B

-- ∃-elim

∃-elim : {A C : Set}{B : A → Set} → ∃ A B → ((a : A) → B a → C) → C
∃-elim [ a , b ] f = f a b

---- EQUATIONAL REASONING

-- reflexivity

infix 4 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

-- and we can easily define _≢_

_≢_ : {A : Set} → A → A → Set
a ≢ b = ¬ (a ≡ b)

-- symmetry

sym : ∀{A}{a b : A} → a ≡ b → b ≡ a
sym refl = refl

-- transitivity

trans : ∀{A}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

-- congruence

cong : {A B : Set} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong f refl = refl


-- Example of equational reasoning on natural numbers

-- we will need the operator of composition

_∘_ : {A : Set} {B : A → Set} {C : {x : A} → B x → Set} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

-- We use Dec as "Decidable relations".

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

≡⇓ℕ : {m n : ℕ} → succ m ≡ succ n → m ≡ n
≡⇓ℕ refl = refl

_≟_ : (m n : ℕ) → Dec (m ≡ n)
zero ≟ zero   = yes refl
zero ≟ succ n = no (λ ())
succ m ≟ zero = no (λ ())
succ m ≟ succ n with m ≟ n
succ m ≟ succ .m | yes refl = yes refl
succ m ≟ succ n  | no  m≢n  = no (m≢n ∘ ≡⇓ℕ)
