module Synthetic.Notes where

-- ========================
-- Day One (7 August, 2019)
-- ========================

-- Logical Correspondences
-- =======================

{-
Types               | Propositions   | Sets                | Spaces
Forms               | Proofs         | Elements            | Point
Families            | Predicates     | Families of Sets    | Fibration
Π (x : A) . B(x)    | ∀              | Sections            | Continuous Section
Σ (x : A) . B(x)    | ∃              | Disjoint Union      | Total Space
Identity Type       | =              | =                   | Paths
-}

-- Inference Rules
-- ===============

{-
  id : A → A

  Γ ⊢ A type
  -----------
  Γ , A ⊢ x : A
-----------------
Γ ⊢ λ x . x : A → A

Conclusion: id := λ x → x
-}

{- Question: You only use the arrow notation when the codomain doesn't depend on the domain?
   Answer: yes -}

{- Question: The inference rules aren't like Axioms - they aren't complete yet?
   Answer: No, we'll get to that -}

{-
                          Γ ⊢ g : B → C
                         ----------------------
Γ, x : A, f(x) : B(x)     Γ , x : A, y : B ⊢  C
------------------------------------------------
 Γ , A ⊢ g(f(x)) : C
---------------------
  Γ ⊢ g ∘ f : A → C
-}

{-
  Natural Numbers:

  ---------  --------  ---------------
  ⊢ ℕ type   ⊢ 0 : ℕ  ⊢ succ : ℕ → ℕ
-}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

{-
  The first rule is a formation rule.  For more complex types, there would be
  dependencies introduced, but ℕ doesn't depend on anything so it has empty
  antecedents.

  The introduction rules are presented next, telling you what canonical elements
  of ℕ are

  Then Elimination rules

  Then Computation rules - Induction.  We want an assertion that holds for arbitrary
  Γ , n : ℕ ⊢ P(n)

  We want something that sez

  Γ ⊢ p₀ : P(0)             Γ ⊢ Pₛ : Π(n : ℕ) (P(n) → P(s(n)))
  ------------------------------------------------------------------
                Γ ⊢ Π (n : ℕ) . P(n)

  THis rule gives you induction and recursion - they're kind of the same thing.
-}

indₙ : {C : ℕ → Set} → C 0 → ((n : ℕ) → C n → C (succ n)) → (n : ℕ) → C n
indₙ c₀ cₛ zero = c₀
indₙ c₀ cₛ (succ n) = cₛ n (indₙ c₀ cₛ n)


{-
 Example: Addition on the natural numbers:

 We want to define a function _+_ that takes two natural numbers and the way
 to do that in type theory is to iterate the (→) type constructor: ℕ → (ℕ → ℕ)
 (Agda is automatically associative here).
-}

_+_ : ℕ → ℕ → ℕ
x + y = {!   !}


-- More Types
-- ==========

{-
  "Combinatorial Types"

  1, 0, 2, +, ×

  Example: ⋆ : 1

  induction principle for 1 is
-}

data ⊤ : Set where
  ⋆ : ⊤

rec₁ : ∀{c}{C : Set c} → C → ⊤ → C
rec₁ c ⋆ = c

{-
  There is a dual to Π called "dependent pairs", written Σ
-}

{-
  Type Families

  Pi Types
  ========

  0000000000000000
 0                 0
 0                 0
 0   Type Family   0
 0 (Fibers of "X") 0
 0      B(x)       0
 0                 0
  0000000000000000
          |
      "Lies Above"
          |
   ----------------
  |                |
  |                |
  |     Type "X"   |
  |                |
  |                |
   ----------------

   Sigma Types
   ========

META: Take old picture, connect all the lines to form a torus

   0000000000000000
  0                 0
  0                 0
  0  Type Family    0
  0 (Fibers of "X") 0
  0                 0
  0                 0
   0000000000000000
           |
       "Lies Above"
           |
    ----------------
   |                |
   |                |
   |     Type "X"   |
   |                |
   |                |
    ----------------
-}

-- Identity Type
-- =============

{-
    Γ ⊢ x : A
---------------------
Γ, x : A ⊢ (x = x) type


         Γ ⊢ A
  -------------------
  Γ ⊢ reflₓ : (x = x)


  The induction principle asks us to exhibit a section for each witness here,
  but that's just reflₓ
-}

data _≡_ {a}{A : Set a}(x : A) : A → Set a where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

ind= : ∀ {i} {A : Set i} → (C : (x y : A) → (x ≡ y) → Set i) → ((x : A) → C x x refl) → {x y : A} → (p : x ≡ y) → C x y p
ind= C c {x}{y} p rewrite p = c y

{-
  Now we want a function

  f : Π (x = y) → (y = x)

  This is a perfect use-case for path induction, because we need only consider
  refl.
-}
_⁻¹ : ∀ {i} {A : Set i}{x y : A} → (x ≡ y) → (y ≡ x)
_⁻¹ {i} {A} p = ind= D d p where
  D : (x y : A) → x ≡ y → Set i
  D = λ x y p → (y ≡ x)

  d : (x : A) → D x x refl
  d = λ x → refl

{-
  Awodey sez: Talk about funtoriality thru transport.

  With this in mind, as long as equalities are paths, it makes sense that we
  can define an equality-respecting operation that, from one perspective, takes
  a point on a path in the base space and induces a corresponding path in
  the space of the fibration.  We call this operation "transport" - it looks like
  parallel movement in the upper and lower spaces in the diagrams above.
-}

transport : ∀ {i} {A : Set i}{P : A → Set i}{x y : A} → (p : x ≡ y) → (P x → P y)
transport {i} {A}{P} {x}{y} p = ind= D d p where
    D : (x y : A) → (p : x ≡ y) → Set i
    D x y p = P x → P y

    d : (x : A) → D x x refl
    d = λ x → (λ x → x)
