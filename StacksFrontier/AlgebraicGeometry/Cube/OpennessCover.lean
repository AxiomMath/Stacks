module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Finite affine covers of quasi-compact schemes, indexed in the scheme's universe

A quasi-compact scheme has a finite cover by affine opens, indexed by a finite type in the
universe of the scheme. This is the form in which the Čech complexes of the openness step of the
theorem of the cube ([Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)) are set up.

## Main results

* `AlgebraicGeometry.Cube.Openness.exists_finite_affine_cover`: the statement above.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Cube.Openness

/-- **A quasi-compact scheme has a finite affine open cover**, indexed by a finite type in the
universe of the scheme. -/
theorem exists_finite_affine_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (I : Type u) (_ : Fintype I) (U : I → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ (⊤ : X.Opens) = ⨆ i, U i := by
  obtain ⟨s, hs, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by simpa using isCompact_univ)
  exact ⟨s, hs.fintype, fun i => i.1.1, fun i => i.1.2, by rw [e, iSup_subtype']⟩

end AlgebraicGeometry.Cube.Openness

end
