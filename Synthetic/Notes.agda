{-# OPTIONS --without-K #-}
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

-- ========================
-- Day One (7 August, 2019)
-- ========================

-- Contractible Types
-- ==================

{-
  A type is said to be constractible if it comes equipped with a term of type

  is-contr(A) := Σ (x : A) Π (y : A) . x = y
-}

open import Agda.Primitive using (Level; _⊔_)

private
  variable
    a b : Level
    A : Set a
    B : Set b

open import Agda.Builtin.Sigma public
  renaming (fst to proj₁; snd to proj₂)
  hiding (module Σ)

module Σ = Agda.Builtin.Sigma.Σ
  renaming (fst to proj₁; snd to proj₂)

-- The syntax declaration below is attached to Σ-syntax, to make it
-- easy to import Σ without the special syntax.

infix 2 Σ-syntax

Σ-syntax : (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

isContr : ∀ {i} → Set i → Set i
isContr X = Σ X λ x → (x' : X) → x ≡ x'


-- Fundamental theorem of id-types
-- ===============================

{-
  For f : Π (x : A) B(x) → C(x)

  we say that f is a family of equivalences if each f(x) is an equivalence

  Theorem: Consider a type family B over A, a : A, b : B(a).  The following are
  equivalent:

  1) The canonical map Π (x : A) (a = x) → B(x) is a family of equivalences
  2) The total space Σ (x : A) . B(x) is contractible
  3) ∀ C(x, y) indexed by x : A, y : B(x),
      Π(x : A) Π(y : B(x)) C(x, y) ↔ C(a, b)
     has a section

  Theorem: TFAE
  1) The Univalence Axiom

      id-to-equiv : Π(x : A) (A = X) → (A ≃ X)

    is a family of equivalences
  2) Σ (X : U) A ≃ X is contractible
  3) ∀ C(x, y) indexed by x : A, y : B(x),
      Π(X : U) Π(p : A ≃ X) C(x, p) ↔ C(A, idₐ)
     has a section
-}

-- For any A and B, a quasi-inverse of f is a triple with
--    ∘ A way back (an inverse for the homomorphism)
--    ∘ Homotopies:
--        ⊚ α : f ∘ g ∼ id
--        ⊚ β : g ∘ f ∼ id
-- For now, because I am lazy, the presence of a quasi-inverse will count
-- as our definition of equivalence for now.  Sorry.
record IsEquiv {i j}{A : Set i}{B : Set j}(to : A → B) : Set (i ⊔ j) where
  field
    from : B → A
    iso₁ : (x : A) → from (to x) ≡ x
    iso₂ : (y : B) → to (from y) ≡ y

id : ∀ {i}{X : Set i} → X → X
id x = x

-- Example 2.4.7: Identity is an equivalence.
id-is-equiv : ∀ {i} (A : Set i) → IsEquiv (id {i}{A})
id-is-equiv {i} A = record
  { from = id {i}{A}
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl
  }

-- Type equivalence is also an equivalence, just on the Universe because:
--    ∘ id-is-equiv works for it, therefore A ≃ A
--    ∘ With A ≃ B, we can always make B ≃ A
--    ∘ With A ≃ B and B ≃ C we have A ≃ C
_≃_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
A ≃ B = Σ (A → B) IsEquiv

idtoeqv : ∀ {i} {A : Set i}{B : Set i} → (A ≡ B) → (A ≃ B)
idtoeqv {_}{A} refl = (id , id-is-equiv A)

-- Higher Inductive Types
-- ======================

{-
  The circle is a higher inductive type with constructors
    base : Sᵈ
    loop : base = base
-}

{-
data S¹ : Set where
   base : S¹

postulate
  loop : base ≡ base
-}

{-
  THe induction principle asserts that for any family F over S¹, we must show
  Π (X : S¹) P(X).

  Supposing we had such an f : Π (X : S¹) P(X), then the most we can do is
  evaluate it at each of the constructors:

    f(base) : P(base)
    f(loop) doesn't quite make sense, but
      transport along p(loop, f(base)) = f(base)
    does
-}

-- Fundamental Cover of the Circle
-- ===============================

{-
  The fundamental cover of the circle is an infinite spiral lying over the
  circle.

  We want

    (S¹ → U) ≃ (Σ (x : U) X = X) ≃ (Σ (x : U) X ≃ X)

  From this we obtain a family E over S¹` equipped with

        ℤ → E(base)

  succ  ↓        ↓  transport(loop)

        ℤ → E(base)`
-}

{-
  Idea: Ω(S¹) ≃ ℤ by showing Σ (x : S¹) is contractible

  Method:
    First construct (base kₑ) = (base (k+1)ₑ)
-}

-- We need pointed sets for this part
Set• : ∀ i → Set _
Set• i = Σ (Set i) λ X → X

-- The loop space of a type is
--  - A base point
--  - A loop (reflexivity) about that point
Ω₁ : ∀ {i} → Set• i → Set• i
Ω₁ (X , x) = ((x ≡ x) , refl)

-- Construct arbitrary n-dimensional loop spaces
Ωⁿ : ∀ {i} → ℕ → Set• i → Set• _
Ωⁿ 0 x = x
Ωⁿ (succ n) x = Ωⁿ n (Ω₁ x)

-- Projects the type from an n-dimensional loop space
Ω : ∀ {i} → ℕ → {X : Set i} → X → Set i
Ω n {X} x = proj₁ (Ωⁿ n (X , x))

-- Projects the loop from an n-dimensional loop space
loop : ∀ {i} n {X : Set i}(x : X) → Ω n x
loop n {X} x = proj₂ (Ωⁿ n (X , x))

{-
  Method:

-}
























--
