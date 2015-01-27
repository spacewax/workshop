module Introduction where

---- Boolean

data Bool : Set where
  true  : Bool
  false : Bool

-- telescopic syntax
-- data Bool : Set where
--   true false : Bool

-- basic operations on boolean

-- negation

not : Bool → Bool
not true = false
not false = true

-- disjunction

_or_ : Bool → Bool → Bool       -- mixfix syntax
true  or _  = true
false or b₂ = b₂

-- conjunction

_and_ : Bool → Bool → Bool
true  and b₂ = b₂
false and _  = false

-- Natural numbers

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- we bind the built-in type

{-# BUILTIN NATURAL ℕ #-}       

-- fixity as in Haskell

infixl 7 _*_
infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

_*_ :  ℕ → ℕ → ℕ
zero * n = zero
succ m * n = n + m * n

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

-- product and sum

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data _||_ (A B : Set) : Set where
  inl : A → A || B
  inr : B → A || B

-- List

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- hd : {A : Set} → List A → A
-- hd [] = {!!}                    -- ????
-- hd (x ∷ l) = x

length : ∀{A} → List A → ℕ
length [] = zero
length (x ∷ xs) = succ (length xs)

-- Vectors are lists indexed by their length

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

vhd : {A : Set}{n : ℕ} → Vec A (succ n) → A
vhd (x ∷ v) = x

append : ∀{m n A} → Vec A m → Vec A n → Vec A (m + n)
append [] v₂ = v₂
append (x ∷ v₁) v₂ = x ∷ append v₁ v₂

_++_ = append

concat : ∀{m n A} → Vec (Vec A m) n → Vec A (n * m)
concat [] = []
concat ([] ∷ xss) = concat xss
concat (xs ∷ xss) = xs ++ concat xss

zip : ∀{A B n} → Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

zipWith : ∀{A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith f [] [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

toList : ∀{A n} → Vec A n → List A
toList [] = []
toList (x ∷ xs) = x ∷ toList xs

fromList : ∀{A} → (xs : List A) → Vec A (length xs)
fromList [] = []
fromList (x ∷ xs) = x ∷ fromList xs
