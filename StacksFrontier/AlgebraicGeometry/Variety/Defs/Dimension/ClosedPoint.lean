module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula

/-!
# Dimension at a closed point of a scheme over a field

For a scheme locally of finite type over a field, the local dimension of the underlying
topological space at a closed point equals the Krull dimension of the local ring at that point:
the residue field at a closed point is a finite extension of the base field, so the
transcendence-degree term of the dimension formula vanishes.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_eq_krullDimOfRing_stalk` identifies the local
  dimension at a closed point with the dimension of its local ring.

## Implementation notes

A locally algebraic `k`-scheme is represented by its structure morphism to `Spec k`, equipped
with a `LocallyOfFiniteType` instance. The dimension of the scheme at a point is
`topologicalKrullDimAt`, while the dimension of the local ring is `ringKrullDim` applied to the
stalk of the structure sheaf.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- At a closed point of a scheme locally of finite type over a field, the local dimension of
the scheme equals the Krull dimension of its local ring. -/
@[stacks 0A21 "dimension_at_closed_point"]
theorem topologicalKrullDimAt_eq_krullDimOfRing_stalk
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    topologicalKrullDimAt X x = ringKrullDim (X.presheaf.stalk x) := by
  have h := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X f x
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : LocallyOfFiniteType (X.fromSpecResidueField x) := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hx; infer_instance
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp] at hcomp
  simp only [← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  let : Algebra.FiniteType k (X.residueField x) := by
    show RingHom.FiniteType (algebraMap k (X.residueField x))
    convert hcomp using 1
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← Scheme.Γevaluation_naturality]
    simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  let : Module.Finite k (X.residueField x) := finite_of_finite_type_of_isJacobsonRing _ _
  let : Algebra.IsAlgebraic k (X.residueField x) := Algebra.IsAlgebraic.of_finite _ _
  simpa [trdeg_eq_zero] using h

end AlgebraicGeometry

end
