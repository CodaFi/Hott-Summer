-- --include-path=/Users/cfi/Library/Agda/agda-stdlib/src
-- TODO: Find a way to add the freaking standard library to my include path in
-- Atom. Why is this so hard?
module Formalization.Notes where

open import Data.Product

modus-ponens : {P Q : Set} → ((P → Q) × P) → Q
modus-ponens (f , x) = f x

transitivity : {P Q R : Set} → (P → Q) → (Q → R) → (P → R)
transitivity f g x = g (f x)
