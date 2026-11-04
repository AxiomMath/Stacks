module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.FormsDirectSum

/-!
# The grading on Kähler differentials

For a commutative algebra graded by an additive commutative monoid, the module of Kähler
differentials is the internal direct sum of its homogeneous components. This is the exterior
degree one case of the corresponding statement for differential forms.

## Main results

* `KaehlerDifferential.isInternal_gradedDifferentialComponent` states that the homogeneous
  differential components form an internal direct-sum decomposition.

## Implementation notes

The assumptions that the algebra is the direct sum of its homogeneous submodules, that
multiplication adds degrees, and that scalars have degree zero are packaged by Mathlib's
`GradedAlgebra` class. The `DecidableEq G` parameter is part of Mathlib's interface for internal
direct sums and is harmless. The degree-one case is transported from differential forms along the
canonical equivalence between the first exterior power and the module of differentials, which is
injective, so independence and spanning both transport.

## References

* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9)
-/

@[expose] public section

namespace KaehlerDifferential

universe u v w

/-- **Stacks Project, Tag 0FU9.** The Kähler differentials of a graded
commutative algebra are the internal direct sum of their homogeneous
components. -/
@[stacks 0FU9 "differentials_direct_sum"]
theorem isInternal_gradedDifferentialComponent
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [GradedAlgebra gr] :
    DirectSum.IsInternal (gradedDifferentialComponent gr) := by
  let e := (exteriorPower.oneEquiv A (KaehlerDifferential R A)).restrictScalars R
  have hP :=
    isInternal_gradedDifferentialFormComponent gr
      (DirectSum.Decomposition.isInternal gr) 1
  show DirectSum.IsInternal
    (fun i ↦ (gradedDifferentialFormComponent gr 1 i).map e.toLinearMap)
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨e.toLinearMap.iSupIndep_map e.injective hP.submodule_iSupIndep,
    by rw [← Submodule.map_iSup, hP.submodule_iSup_eq_top, Submodule.map_top,
      LinearEquiv.range]⟩

end KaehlerDifferential
