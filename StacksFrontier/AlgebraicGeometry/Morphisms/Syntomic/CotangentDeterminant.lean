module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.QuasiFinite
public import StacksFrontier.RingTheory.CompleteIntersection.CotangentDeterminant

/-!
# The local Jacobian picture of the determinant of the naive cotangent complex

Around every point of the source of a locally quasi-finite syntomic morphism of schemes there
are affine opens `V = Spec B ⊆ Y` and `U = Spec A ⊆ X` with `f(V) ⊆ U` and a presentation
`B = A[x_1, …, x_n]/(f_1, …, f_n)` with as many relations as variables which is a relative global
complete intersection. For such a presentation the naive cotangent complex is the two-term
complex `(f)/(f)² → ⨁ᵢ B dxᵢ` with free terms of the same rank, its differential is the Jacobian
matrix in the basis of the relation classes and the basis `dxᵢ`, its determinant line is free of
rank one, and its canonical section is the Jacobian determinant times the generator.

## Main results

* `AlgebraicGeometry.exists_square_presentation_hasJacobianDelta`: the local picture around a
  point of the source.

## References

* [Stacks Project, Tag 0FKC](https://stacks.math.columbia.edu/tag/0FKC)
-/

namespace AlgebraicGeometry

universe u

@[expose] public section

/-- Around every point of the source of a locally quasi-finite syntomic morphism of schemes there
is a square relative global complete intersection presentation `B = A[x_1, …, x_n]/(f_1, …, f_n)`
with the local Jacobian picture of the determinant of its naive cotangent complex: the conormal
module is free on the classes of the relations, the differential is the Jacobian matrix in that
basis and the basis `dxᵢ`, the determinant line is free of rank one on the generator matching
those two bases, and the canonical section is the Jacobian determinant times that generator. -/
@[stacks 0FKC "the local picture around a point of the source of a locally quasi-finite
syntomic morphism; the presentation is chosen by Tag 0BWE part (5)"]
theorem exists_square_presentation_hasJacobianDelta {Y X : Scheme.{u}} {f : Y ⟶ X}
    (hqf : LocallyQuasiFinite f) (hf : Syntomic f) (y : Y) :
    ∃ (V : Y.affineOpens) (U : X.affineOpens) (_ : y ∈ V.1) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      ∃ (n : ℕ) (P : Algebra.Presentation Γ(X, U.1) Γ(Y, V.1) (Fin n) (Fin n))
          (hP : P.IsRelativeGlobalCompleteIntersection),
        letI := hP
        P.HasJacobianDelta := by
  obtain ⟨V, U, hyV, hVU, n, P, hP⟩ :=
    hasLocalSquareRelativeGlobalCompleteIntersection_of_locallyQuasiFinite_syntomic hqf hf y
  refine ⟨V, U, hyV, hVU, n, P, hP, ?_⟩
  let _ : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let _ := hP
  exact P.hasJacobianDelta

end

end AlgebraicGeometry
