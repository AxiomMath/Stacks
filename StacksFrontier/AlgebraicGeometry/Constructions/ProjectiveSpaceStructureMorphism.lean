module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety

/-!
# The structure morphism of projective space over a scheme

The structure morphism `ℙⁿ_S ⟶ S` of projective `n`-space over a scheme `S` is separated,
quasi-compact, satisfies the existence and the uniqueness part of the valuative criterion, and
universally closed. These are the four assertions of Tag 01NH.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.projectiveSpaceOver.valuativeCriterion_existence`: the existence part of the
  valuative criterion for `ℙⁿ_S ⟶ S`.
* `AlgebraicGeometry.projectiveSpaceOver.valuativeCriterion_uniqueness`: the uniqueness part.

## Implementation notes

Separatedness and quasi-compactness are already in the library: `ℙⁿ_S` is the base change of
`Proj ℤ[T₀, …, Tₙ]` along `S ⟶ Spec ℤ`, and both properties are stable under base change.
`Stacks.HProjective.isSeparated_over` is separatedness and
`AlgebraicGeometry.projectiveSpaceOver.quasiCompact` is quasi-compactness, so this file records
Tag 01NH on them rather than restating them.

Universal closedness is one of the three components of properness, which the library proves for
`ℙⁿ_S ⟶ S` in `StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper`, and the
instance `AlgebraicGeometry.projectiveSpaceOver.isProper` there carries Tag 01NH for it. The
existence part of the valuative criterion is then equivalent to universal closedness for a
quasi-compact morphism, by Tag 01KF, and the uniqueness part follows from separatedness by
Tag 01KZ. This inverts the order of the Stacks proof, which obtains universal closedness from the
valuative criterion, but the two implications are both available and the properness instance is
the one the library already carries.

## References

* [Stacks Project, Tag 01NH](https://stacks.math.columbia.edu/tag/01NH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

add_to_stacks 01NH "separated" Stacks.HProjective.isSeparated_over

add_to_stacks 01NH "quasi-compact" AlgebraicGeometry.projectiveSpaceOver.quasiCompact

namespace AlgebraicGeometry.projectiveSpaceOver

/-- **Stacks 01NH (3), existence.** The structure morphism of projective `n`-space over a scheme
`S` satisfies the existence part of the valuative criterion. -/
@[stacks 01NH "existence part of the valuative criterion"]
theorem valuativeCriterion_existence (n : ℕ) (S : Scheme.{u}) :
    ValuativeCriterion.Existence (projectiveSpaceOver n S ↘ S) := by
  have h : UniversallyClosed (projectiveSpaceOver n S ↘ S) := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact h.1

/-- **Stacks 01NH (3), uniqueness.** The structure morphism of projective `n`-space over a scheme
`S` satisfies the uniqueness part of the valuative criterion. -/
@[stacks 01NH "uniqueness part of the valuative criterion"]
theorem valuativeCriterion_uniqueness (n : ℕ) (S : Scheme.{u}) :
    ValuativeCriterion.Uniqueness (projectiveSpaceOver n S ↘ S) :=
  IsSeparated.valuativeCriterion _

end AlgebraicGeometry.projectiveSpaceOver
