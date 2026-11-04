module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.ProjectiveConnectingMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The connecting map on central simple algebras

Let `K` be a field with separable algebraic closure `Kˢᵉᵖ`. A central simple `K`-algebra of
degree `d` has a class in `H¹(Gal(Kˢᵉᵖ/K), PGL_d(Kˢᵉᵖ))`, and the connecting map of the scalar
central extension sends that class to a class in `H²(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)ˣ)`. This file assembles
the composite and shows that it depends on the algebra only through its isomorphism class.

## Main definitions

* `Stacks.GaloisCohomology.brauerDeltaOfDegree`: the composite on central simple algebras of a
  fixed degree.
* `Stacks.GaloisCohomology.brauerDeltaOfCSA`: the composite on central simple algebras, the
  degree being read off the algebra.

## Main results

* `Stacks.GaloisCohomology.brauerDeltaOfCSA_eq_of_algEquiv`: isomorphic central simple algebras
  have the same class.

## Implementation notes

The class in nonabelian `H¹` is the one of
[Stacks, Tag 03R6](https://stacks.math.columbia.edu/tag/03R6), which is defined on isomorphism
classes of algebras of a fixed degree; invariance under isomorphism is therefore inherited,
once the degrees are identified, and no choice of splitting or of lift enters the formula.

## References

* [Stacks Project, Tag 03R7](https://stacks.math.columbia.edu/tag/03R7)
-/

@[expose] public noncomputable section

open scoped MatrixGroups

namespace Stacks.GaloisCohomology

universe u v

variable (K : Type u) [Field K] (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep]

/-- The class in `H²(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)ˣ)` of a central simple `K`-algebra of degree `d`: the
connecting map of the scalar central extension applied to its projective cohomology class. -/
@[sga "4½ Arcata 3.1.2"]
def brauerDeltaOfDegree (d : ℕ) (hd : 0 < d) (a : CentralSimpleAlgebraOfDegree.{u, v} K d) :
    TwoCohomology K Ksep :=
  pglConnectingMap hd (centralSimpleAlgebraClassEquivPGLH1 K Ksep d hd.ne' (Quotient.mk _ a))

/-- The class in `H²(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)ˣ)` of a central simple `K`-algebra. -/
@[sga "4½ Arcata 3.1.2"]
def brauerDeltaOfCSA (A : CSA.{u, v} K) : TwoCohomology K Ksep :=
  brauerDeltaOfDegree K Ksep (Algebra.IsCentralSimple.degree K A)
    (Algebra.IsCentralSimple.degree_pos K A) ⟨A, rfl⟩

/-- The class of a central simple algebra is its class as an algebra of its own degree. -/
theorem brauerDeltaOfCSA_eq (A : CSA.{u, v} K) (d : ℕ) (hd : 0 < d)
    (hA : Algebra.IsCentralSimple.degree K A = d) :
    brauerDeltaOfCSA K Ksep A = brauerDeltaOfDegree K Ksep d hd ⟨A, hA⟩ := by
  subst hA
  rfl

/-- Isomorphic central simple algebras of a given degree have the same class. -/
theorem brauerDeltaOfDegree_eq_of_algEquiv (d : ℕ) (hd : 0 < d)
    (a b : CentralSimpleAlgebraOfDegree.{u, v} K d) (e : a.1 ≃ₐ[K] b.1) :
    brauerDeltaOfDegree K Ksep d hd a = brauerDeltaOfDegree K Ksep d hd b := by
  have h : (Quotient.mk _ a : CentralSimpleAlgebraClass.{u, v} K d) = Quotient.mk _ b :=
    Quotient.sound (Relation.EqvGen.rel _ _ ⟨e⟩)
  simp only [brauerDeltaOfDegree, h]

/-- Isomorphic central simple algebras have the same class. -/
theorem brauerDeltaOfCSA_eq_of_algEquiv (A B : CSA.{u, v} K) (e : A ≃ₐ[K] B) :
    brauerDeltaOfCSA K Ksep A = brauerDeltaOfCSA K Ksep B := by
  have hrank : Module.finrank K A = Module.finrank K B := e.toLinearEquiv.finrank_eq
  have hdeg : Algebra.IsCentralSimple.degree K A = Algebra.IsCentralSimple.degree K B := by
    simp only [Algebra.IsCentralSimple.degree, hrank]
  rw [brauerDeltaOfCSA_eq K Ksep A _ (Algebra.IsCentralSimple.degree_pos K A) rfl,
    brauerDeltaOfCSA_eq K Ksep B _ (Algebra.IsCentralSimple.degree_pos K A) hdeg.symm]
  exact brauerDeltaOfDegree_eq_of_algEquiv K Ksep _ _ _ _ e

end Stacks.GaloisCohomology
