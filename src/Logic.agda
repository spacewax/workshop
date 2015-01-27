module Logic where

open import Introduction using (ℕ ; succ ; zero)

-- PROPOSITIONAL LOGIC

-- Conjunction (same definition as product !)

{-

  Γ ⊢ A  Γ ⊢ B
 ────────────── ∧ᵢ
   Γ ⊢ A ∧ B

-}

data _∧_ (A B : Set) : Set where
  _&_ : A → B → A ∧ B

-- ∧-elimination

{-

   Γ ⊢ A ∧ B
 ────────────── ∧ₑ₁
     Γ ⊢ A

-}

fst : {A B : Set} → A ∧ B → A
fst (a & b) = a

{-

   Γ ⊢ A ∧ B
 ────────────── ∧ₑ₂
     Γ ⊢ B

-}

snd : {A B : Set} → A ∧ B → B
snd (a & b) = b

-- Disjunction (same definition as sum !)

{-

     Γ ⊢ A
 ────────────── ∨ᵢ₁
   Γ ⊢ A ∨ B

     Γ ⊢ B
 ────────────── ∨ᵢ₂
   Γ ⊢ A ∨ B

-}

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

-- ∨-elimination

{-

  Γ ⊢ A ∨ B   Γ,A ⊢ C  Γ,B ⊢ C
 ─────────────────────────────── ∨ₑ
               Γ ⊢ C

-}

case : {A B C : Set} → A ∨ B → (A → C) → (B → C) → C
case (inl a) f g = f a
case (inr b) f g = g b

-- True and false

data ⊤ : Set where
  ⟨⟩ : ⊤

data ⊥ : Set where          -- False has not habitant

-- ⊥-elim (⊥ implies anything)

{-

     Γ ⊢ ⊥
 ────────────── ⊥ₑ
     Γ ⊢ A

-}

nocase : {A : Set} → ⊥ → A
nocase ()                       -- we call it the 'absurd pattern'

-- Negation

---- ¬ A ≡ A ⇒ ⊥

¬ : Set → Set
¬ A = A → ⊥

¬-elim : ∀{A} → ¬ A → A → ⊥
¬-elim a b = a b

-- Implication

data _⇒_ (A B : Set) : Set where
  fun : (A → B) → A ⇒ B

{-

  Γ,A ⊢ B   Γ ⊢ A
 ───────────────── ⇒ₑ
       Γ ⊢ B

-}

---- sometimes named application ;)
⇒-elim : ∀{A B} → A ⇒ B → (a : A) → B 
⇒-elim (fun f) a = f a

-- Equivalence

{-

  Γ,A ⊢ B   Γ,B ⊢ A
 ─────────────────── ⇔ᵢ
       Γ ⊢ A ⇔ B

-}

_⇔_ : Set → Set → Set
A ⇔ B = (A ⇒ B) ∧ (B ⇒ A)

-- ⇔-elimination

{-

  Γ ⊢ A   Γ ⊢ A ⇔ B
 ─────────────────── ⇔ₑ₁
       Γ ⊢ B

-}

⇔-elim₁ : ∀{A B} → A → A ⇔ B → B
⇔-elim₁ a (fun a→b & b⇒a) = a→b a

{-

  Γ ⊢ B   Γ ⊢ A ⇔ B
 ─────────────────── ⇔ₑ₂
       Γ ⊢ A

-}

⇔-elim₂ : ∀{A B} → B → A ⇔ B → A
⇔-elim₂ b (a⇒b & fun b→a) = b→a b


---- PREDICATE LOGIC

-- Universal

data Forall (A : Set) (β : A → Set) : Set where
  ∀' : ((α : A) → β α) → Forall A β

{-

    φ (β / α)
  ───────────── ∀ᵢ
       ∀α φ  

-}

∀-intro : {A : Set} {β : A → Set} → ((α : A) → β α) → ∀ α → β α
∀-intro β = β

-- ∀-elim

{-

      ∀α φ
  ───────────── ∀ₑ
    φ (β / α)   

-}

∀-elim : {A : Set}{B : A → Set} → Forall A B → (a : A) → B a
∀-elim (∀' f) a = f a

-- Existential

{-

  ∃α φ  φ(β/α) ⊢ ψ 
 ─────────────────── ∃ᵢ
                     

-}

data ∃ (A : Set)(B : A → Set) : Set where
  [_,_] : (a : A) → B a → ∃ A B

-- Asking for the witness α and the proof that B holds for the
-- witness α.

witness : {A : Set} {B : A → Set} → ∃ A B → A
witness [ a , b ] = a

proof : {A : Set} {B : A → Set} → (c : ∃ A B) → B (witness c)
proof [ a , b ] = b

-- ∃-elim

{-

  ∃α φ  φ(β/α) ⊢ ψ 
 ─────────────────── ∃ₑ
       ψ

-}

∃-elim : {A C : Set}{B : A → Set} → ∃ A B → ((a : A) → B a → C) → C
∃-elim [ a , b ] f = f a b

---- EQUATIONAL REASONING

-- Reflexivity

infix 4 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

-- Sometimes named subst
≡-elim : ∀{A}{P : A → Set}{a₁ a₂ : A} → a₁ ≡ a₂ → P a₁ → P a₂
≡-elim refl pa₂ = pa₂

-- and we can easily define _≢_ with ¬_

_≢_ : {A : Set} → A → A → Set
a ≢ b = ¬ (a ≡ b)

-- Symmetry

sym : ∀{A}{a b : A} → a ≡ b → b ≡ a
sym refl = refl

-- Transitivity

trans : ∀{A}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

-- Congruence

cong : {A B : Set} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong f refl = refl

-- Example of equational reasoning on natural numbers.

-- We will need the composition operator.

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
