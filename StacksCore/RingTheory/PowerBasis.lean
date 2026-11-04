module

public import Mathlib.RingTheory.PowerBasis

/-! # Basis consisting of powers of an element -/

@[expose] public section

open Polynomial

/-- If `f` is a monic polynomial of degree `b.dim` annihilating the generator of a power basis
`b`, then `f` is the minimal polynomial of `b.gen`. -/
theorem PowerBasis.minpoly_gen_eq
    {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    (b : PowerBasis R S) {f : R[X]}
    (hf : f.aeval b.gen = 0) (hfm : f.Monic) (hfd : f.natDegree = b.dim) :
    minpoly R b.gen = f := by
  nontriviality R
  refine minpoly.eq_of_linearIndependent _ _ hfm hf f.natDegree (degree_eq_natDegree hfm.ne_zero) ?_
  convert b.basis.linearIndependent; simp; grind
