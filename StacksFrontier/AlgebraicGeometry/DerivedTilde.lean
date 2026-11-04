module

public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Quasicoherent

/-!
# Derived sheafification on an affine scheme is exact

For a commutative ring `R`, derived sheafification `D(R) ⥤ D_QCoh(𝒪_{Spec R})` is an exact functor
of triangulated categories.

## Main results

* `AlgebraicGeometry.derivedTilde_isTriangulated`: derived sheafification takes distinguished
  triangles to distinguished triangles.

## Implementation notes

The functor `(tilde.functor R).mapDerivedCategory` is exact, and complexes with quasi-coherent
cohomology form a triangulated subcategory
(`AlgebraicGeometry.derivedQuasicoherent_isTriangulated`), so exactness of the corestriction
follows from `CategoryTheory.ObjectProperty.isTriangulated_lift`.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ u

namespace AlgebraicGeometry

/-- Derived sheafification on an affine scheme is exact as a functor of triangulated
categories. -/
instance derivedTilde_isTriangulated (R : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} R)] [HasDerivedCategory.{w₂} (Spec R).Modules] :
    (derivedTilde R).IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right (derivedTildeCompι R)]
  infer_instance

end AlgebraicGeometry

end
