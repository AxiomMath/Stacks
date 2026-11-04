module

public import Mathlib.RingTheory.AdjoinRoot
import StacksCore.Tactic.StacksAttribute

/-! Adjoining roots of polynomials -/

@[expose] public section

add_to_stacks 09FI "third part" AdjoinRoot.instField
add_to_stacks 09FI "fourth part" AdjoinRoot.of
add_to_stacks 09G7 finrank_quotient_span_eq_natDegree

open Polynomial

instance (R : Type*) [CommRing R] [Subsingleton R] (f : R[X]) : Subsingleton (AdjoinRoot f) :=
  (algebraMap R (AdjoinRoot f)).codomain_trivial

/-- For a monic polynomial `f` over a nontrivial commutative ring `R`, the rank of
`AdjoinRoot f` as an `R`-module equals the degree of `f`. -/
@[stacks 09G7, simp]
theorem Polynomial.Monic.finrank_adjoinRoot {R : Type*} [CommRing R] [Nontrivial R]
    {f : R[X]} (hf : f.Monic) : Module.finrank R (AdjoinRoot f) = f.natDegree :=
  (AdjoinRoot.powerBasis' hf).finrank
