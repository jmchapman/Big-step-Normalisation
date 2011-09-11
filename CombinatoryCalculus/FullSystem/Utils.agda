module FullSystem.Utils where

-- A few mod cons

data False : Set where

record True : Set where

data _==_ {A : Set}(a : A) : {B : Set} -> (b : B) -> Set where
  refl⁼ : a == a

sym⁼ : {A : Set}{a a' : A} -> a == a' -> a' == a
sym⁼ refl⁼ = refl⁼

trans⁼ : {A : Set}{a a' a'' : A} -> a == a' -> a' == a'' -> a == a''
trans⁼ refl⁼ p = p

resp : {A : Set}{B : A -> Set}{a a' : A} -> a == a'  -> 
       (f : forall a -> B a) -> f a == f a'
resp refl⁼ f = refl⁼ 

resp2 : {A B : Set}{C : A -> B -> Set}{a a' : A} -> a == a' -> {b b' : B} ->
  b == b' -> (f : forall a b -> C a b) -> f a b == f a' b'
resp2 refl⁼ refl⁼ f = refl⁼ 

resp3 : {A B C : Set}{D : A -> B -> C -> Set}{a a' : A} -> a == a' -> {b b' : B} ->
  b == b' -> {c c' : C} -> c == c' -> (f : forall a b c -> D a b c) -> f a b c == f a' b' c'
resp3 refl⁼ refl⁼ refl⁼ f = refl⁼ 

data Σ (A : Set) (B : A -> Set) : Set where
  sig : (a : A) -> (b : B a) -> Σ A B

σ₀ : {A : Set}{B : A -> Set} -> (Σ A B) -> A
σ₀ (sig x _) = x

σ₁ : {A : Set}{B : A -> Set} -> (s : Σ A B) -> B (σ₀ s)
σ₁ (sig _ y) = y

data _∧_∧_ (A B C : Set) : Set where
  tr : (a : A)(b : B)(c : C) -> A ∧ B ∧ C

π₀ : forall {A}{B}{C} -> A ∧ B ∧ C -> A
π₀ (tr a _ _) = a

π₁ : forall {A}{B}{C} -> A ∧ B ∧ C -> B
π₁ (tr _ b _) = b

π₂ : forall {A}{B}{C} -> A ∧ B ∧ C -> C
π₂ (tr _ _ c) = c

data _∧_ (A B : Set) : Set where
  pr : (a : A)(b : B) -> A ∧ B

pfst : forall {A}{B} -> A ∧ B -> A
pfst (pr a _) = a

psnd : forall {A}{B} -> A ∧ B -> B
psnd (pr _ b) = b
