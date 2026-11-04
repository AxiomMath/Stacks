module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.FiniteType
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChainBasis
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeTower

/-!
# Finitely many variables in each degree

The finite assertion of [Stacks, Tag 09PN] asks for a Tate resolution with finitely many
variables in every degree, degree zero included. This file collects two consequences of that
finiteness.

In degree zero it is a finite polynomial presentation: a finite-type algebra is a quotient of a
polynomial ring on finitely many variables, and the index type can be placed in whatever
universe the resolution needs.

In positive degrees it is freeness of every homogeneous piece: a graded divided-power
polynomial algebra with finitely many variables in each degree over a free coefficient algebra
is free over the base ring in every degree, by `free_grade_of_finite_indices`, and a polynomial
coefficient algebra is free.

## Main results

* `DividedPowers.TateResolution.exists_finite_polynomial_presentation` — a finite-type algebra
  is presented by a polynomial ring on a finite index type in the given universe.
* `DividedPowers.TateResolution.IndexedPresentation.finite_indices` — the structure's own index
  family is finite when the prescribed one is.
* `DividedPowers.TateResolution.IndexedPresentation.free_grade` — every homogeneous piece of a
  presentation on a finite family of variables over a free coefficient algebra is free.
* `DividedPowers.TateResolution.free_grade_of_finite_newIndices` — the same for the algebra on
  the limiting family of a degree recursion each of whose rungs adjoins finitely many
  variables.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

/-- A finite-type algebra is the quotient of a polynomial ring on finitely many variables, with
the variables indexed by a type in any prescribed universe. -/
public theorem exists_finite_polynomial_presentation (R : Type u) (S : Type v) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (σ : Type (max u v)) (_ : Finite σ) (φ : MvPolynomial σ R →ₐ[R] S),
      Function.Surjective φ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  refine ⟨ULift.{max u v} (Fin n), inferInstance,
    f.comp (MvPolynomial.renameEquiv R Equiv.ulift).toAlgHom, ?_⟩
  exact hf.comp (MvPolynomial.renameEquiv R Equiv.ulift).surjective

namespace IndexedPresentation

variable {R : Type u} {P : Type v} [CommRing R] [CommRing P] [Algebra R P]
  {idx : ℕ → Type (max u v w)}

/-- The index family of the polynomial algebra of a presentation is finite in every degree when
the prescribed family of variables is. -/
public theorem finite_indices (T : IndexedPresentation.{u, v, w} R P idx)
    (hfin : ∀ n : ℕ, Finite (idx n)) (n : ℕ) : Finite (T.polynomial.indices n) := by
  rw [congrFun T.indices_eq n]
  exact hfin n

/-- Every homogeneous piece of a presentation on a finite family of variables over a free
coefficient algebra is free over the base ring. This is `free_grade_of_finite_indices` for a
prescribed family of variables. -/
public theorem free_grade [Module.Free R P] (T : IndexedPresentation.{u, v, w} R P idx)
    (hfin : ∀ n : ℕ, Finite (idx n)) (m : ℕ) : Module.Free R (T.grade m) :=
  free_grade_of_finite_indices T.polynomial (T.finite_indices hfin) m

end IndexedPresentation

/-- Every homogeneous piece of the algebra on the limiting family of a degree recursion is free
over the base ring, as soon as each rung adjoins finitely many variables. -/
public theorem free_grade_of_finite_newIndices (R : Type u) (P : Type v) [CommRing R]
    [CommRing P] [Algebra R P] [Module.Free R P]
    (newIdx : (ℕ → Type (max u v w)) → ℕ → Type (max u v w))
    (hfin : ∀ (f : ℕ → Type (max u v w)) (n : ℕ), Finite (newIdx f n)) (m : ℕ) :
    Module.Free R ((chosenPresentation.{u, v, w} R P (towerLimit newIdx)).grade m) :=
  (chosenPresentation.{u, v, w} R P (towerLimit newIdx)).free_grade
    (finite_towerLimit hfin) m

end DividedPowers.TateResolution

end
