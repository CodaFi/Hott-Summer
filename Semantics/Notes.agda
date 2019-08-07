module Semantics.Notes where

-- ========================
-- Day One (7 August, 2019)
-- ========================

-- Semntics of Type Theory
-- ========================

{-
  Normally, when doing mathematics, we don't discriminate between the formal
  expression (or term) 1+1 or the number that is denoted by the expression (2).
  But in logic, we want to be very clear about the difference between
  mathematical structure and formal language.

  The syntax and semantics of type theory deserve their own courses for this
  reason, but we don't have time for that.
-}

-- What is Semantics?
-- ==================

{-
  "Semantics is the study of interpretations of formal systems in mathematical
   models"

  So, then,
-}

-- What is a Formal System?
-- ========================

{-
  A formal system is all about syntax - what we can write on paper.

  But also data structures in memory of a computer.

  We want to consider expressions that are formally correct, and it oughta be
  efficiently decidable by an algorithm whether a particular expression is
  well-formed and correct.

  Examples:

  ∘ First-Order Logic
  ∘ Propositional Logic
  ∘ Programming Languages
  ∘ Type Theory (really, more like Theories)
-}

-- What is a Mathematical Model?
-- =============================

{-
  Model theorists have a very precise notion of models of logic that we are not
  going to use.

  We are interested in a certain kind of categorical model.
-}

-- What is Interpretation?
-- =======================

{-
  "A translation (mapping) from expressions of the formal system to objects or
   elements of the mathematical model"

   ⟦_⟧ : Expressions → Model
    ^ "Scott Brackets"

   Usually defined by structural induction on the rules of the term language -
   usually these languages are built inductively.
-}

-- Why Semantics?
-- ==============

{-
  ∘ For consistency and independence proofs

    Example: Gödel and Cohen showed the independence of CH from ZFC.  Gödel gave
    a model of ZFC where CH was valid, showing that is was consistent.  Cohen
    used forcing to construct a model where ¬ CH was valid.

  ∘ To use a formal system as an "internal language" for "syntactic reasoning"

    Lawvere and Vocke proposed "Syntactic Differential Geometry" to allow them
    to reason about manifolds using abstract infinitessimals.  They didn't
    propose a formal system at the time, but you could definitely do it up in
    a type theory.

    Synthetic Homotopy Theory uses Martin Löf Type Theory (MLTT) as a language
    for reasoning about Homotopy Types.

    Simplicial model of HoTT due to Voevodsky showed the consistency of the
    Univalence Axiom relative to MLTT.

    Groupoid model of HoTT by Hoffman & Streicher - it used to be asked whether
    identity proofs were themselves indistinguishable.  They showed Uniqueness
    of Identity Proofs (Axiom K) is independent of MLTT.
-}

-- The Rules of Type Theory
-- ========================

{-
  Consider MLTT with
    ∘ Σ Types
    ∘ Π Types
    ∘ Identity Types
    ∘ ℕ
  We're ignoring the universe and more complex types for now.

  Judgemental Forms

    Γ ⊢ ctx         | Γ is a context
    Γ ≡ Δ ⊢ cxt     | Γ and Δ are equal contexts
    Γ ⊢ A type      | A is a type in context Γ
    Γ ⊢ A ≡ B Type  | types A and B are equal
    Γ ⊢ t : A       | t is a term of type A
    Γ ⊢ t ≡ u : A   | t and u are equal terms of type A

  For each type former, we have the usual
    - Formation, introduction, elimination, computation, congruence
  Details:
    - Empty context and context extensions

    ---------
    ⟨⟩ ⊢ ctx

        Γ ⊢ A
    --------------
    Γ, x : A ⊢ ctx

    Γ ≡ Δ ⊢ ctx
    Γ ⊢ A ≡ B types
    -----------------------------
    (Γ, x : A) ≡ (Δ, x : B) ⊢ ctx

-- Question: Are terms and types the same here?
--   Answer: No.  Not for now

    - Variable, weakening, and substitution

    Γ, x : A, Δ ⊢ ctx
  -----------------------
    Γ, x : A, Δ ⊢ x : A

    Γ , Δ ⊢ F
  -----------------
  Γ , x : A , Δ ⊢

  Rules for definitional equality apply for contexts, types and terms.
    - For each, reflexive, transitive, and symmetric.

  Type Conversion:

  Γ ⊢ A type
  Γ ≡ Δ ⊢ ctx
  -----------------
  Δ ⊢ A type

  Γ ⊢ t : A
  Γ ≡ A ⊢ ctx

  These rules break uniqueness of derivations.  The same judgement might be
  derivable different ways, which causes problems for definitions of
  the interpretation function on the structure of terms.  We want all the
  interpretations to be the same.
-}

-- From Syntax to Semantics
-- ========================

-- Set-Theoretic Semantics
-- ========================

{-
  Goals:
    - To every closed type ⟨⟩ ⊢ A, we wish to assign a set ⟦A⟧.
    - To every closed term ⟨⟩ ⊢ t : A, we wish to assign an element ⟦t⟧ ∈ ⟦A⟧
      such that
        - If ⟨⟩ ⊢ A ≡ B then ⟦A⟧ ≡ ⟦B⟧
        - If t = u A then ⟦t⟧ = ⟦u⟧

  For non-empty contexts, given a dependent type with one free variable

  x : A ⊢ B type

  we want a family of sets ⟦B⟧ₐ for a ∈ ⟦A⟧.

  For two variables

  x : A, y : B ⊢ C type

  "Balloon Diagrams"

  From there, it's pretty clear how to go on.

  Giving a term is akin to picking a point in each one of the top-most balloons
  for each point in the base.

  x : A , y : B ⊢ C type
  ----------------------
  x : A : Π (y : B) . C type

  "Ballon Diagram Here" by forming cartesian products of the top level and omit the middle balloons.

  x : A , y : B ⊢ C type
  ----------------------
  x : A : Σ (y : B) . C type

  "Ballon Diagram Here" by forming disjoint unions of the top level and omit the middle balloons.

  x : A , y : A ⊢ Id(x, y) type

  "Ballon Diagram Here" by exponentiation where top layer of baloons is ⊤ or ⊥
  dependening on equality
-}

-- Problems Ahead
-- ==============

{-
  Hierarchies of families are really hard to manipulate and don't generalize to
  other kinds of mathematical structures that aren't sets.

  We instead need a more general category-theoretic notion.  But in category
  theory, families of objects indexed by other objects don't make sense out of
  the box.  So we use a trick:
-}

-- Display Maps
-- ============

{-
  ∘ Given a family (Bₐ)(a ∈ A) of sets, we construct a function
      p : ⊎ (a ∈ A) . Bₐ → A
      p (a, b) ↦ a
  ∘ Given f : B → A, we can construct a family of sets indexed by a ∈ A with
    fibers (f⁻¹(a))(a ∈ A) = ({ b | f b = a })(a ∈ A)

  These two operations are mutually inverse.  More formally:

  Theorem: These two operations form the "object parts" of functors
    ∘ Setᴬ → Set / A
    ∘ Set / A → Setᴬ

    Moreover, these functors establish an equivalence of categories Setᴬ ≃ Set / A

  Proof: Left as an exercise.  The intuition is balloon diagrams.

  Dually, consider the disjoint union of "balloons at all levels" and the
  obvious projection maps taking fibers to their indices.  Then a context
  is just a chain of arrows

  Example

  x : A, y : B, z : C ⊢ ctx

   ---
  |   | = ⟦x : A, y : B, z : C⟧ = ⟦x : A, y : B, ⊢ C type⟧
   ---
    ↓
   ---
  |   | = ⟦x : A, y : B⟧ = ⟦x : A ⊢ B type⟧
   ---
    ↓
   ---
  |   | = ⟦x : A⟧
   ---

   Example

   x : A, y : B ⊢ t : C

   ---
  |   | = ⟦x : A, y : B, z : C⟧ = ⟦x : A, y : B, ⊢ C type⟧
   ---
   ↑ ↓ = "Terms are just one-sided inverses - sections"
   ---
  |   | = ⟦x : A, y : B⟧ = ⟦x : A ⊢ B type⟧
   ---
    ↓
   ---
  |   | = ⟦x : A⟧
   ---
-}























--
