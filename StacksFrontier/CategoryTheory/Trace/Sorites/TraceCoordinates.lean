module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.ProjectiveTrace

/-!
# Group-algebra coordinates for the trace of a finite projective module

Over a group algebra the group trace of an endomorphism is read off from the coefficients of
the identity element of the group along the diagonal of any presentation of the module as a
direct summand of a finite free module.

## Main results

* `splitExpansion`: a vector of a finite projective module expanded against a splitting.
* `groupTrace_eq_coeff_sum`: the group trace as a sum of coefficients of the identity.
-/

@[expose] public section

open scoped MonoidAlgebra

open CategoryTheory.FilteredDerived

namespace Stacks.Trace

/-- A vector of a finite projective module is the sum of its coordinates against the images
of the standard basis under a splitting. -/
theorem splitExpansion (R : Type*) (P : Type*) [Ring R] [AddCommGroup P] [Module R P]
    {n : ℕ} (p : (Fin n → R) →ₗ[R] P) (i : P →ₗ[R] (Fin n → R))
    (h : p.comp i = LinearMap.id) (x : P) :
    x = ∑ j, i x j • p (standardBasisVector R (Fin n) j) := by
  simpa [show p (i x) = x from LinearMap.congr_fun h x] using
    congr(p $(standardBasisVector_decomp R (Fin n) (i x)))

/-- The group trace is the image in the additive commutator quotient of the sum of the
coefficients of the identity along the diagonal of a splitting. -/
theorem groupTrace_eq_coeff_sum (R : Type*) (G : Type*) [Ring R] [Group G]
    (P : Type*) [AddCommGroup P] [Module R[G] P]
    [Module.Finite R[G] P] [Module.Projective R[G] P]
    {ι : Type*} [Fintype ι] (p : (ι → R[G]) →ₗ[R[G]] P)
    (i : P →ₗ[R[G]] (ι → R[G])) (hpi : p.comp i = LinearMap.id)
    (f : Module.End R[G] P) :
    groupTrace R G P f = additiveCommutatorQuotientMk R
        (∑ j, (i (f (p (standardBasisVector R[G] ι j))) j).coeff 1) := by
  show epsilon R G (projectiveModuleTrace R[G] P f) = _
  simp [projectiveModuleTrace_eq_of_split R[G] P f p i hpi, freeModuleTrace_apply, epsilon_mk]

end Stacks.Trace
