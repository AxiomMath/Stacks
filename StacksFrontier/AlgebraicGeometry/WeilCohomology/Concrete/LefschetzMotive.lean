module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Motives
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLineCorrespondenceAlgebra

/-!
# The Lefschetz motive

Let `k` be a field, `X = P¹_k` and `x` a `k`-rational point of `X`, and let
`c₂ = [X × x] ∈ Corr⁰(X, X)` be the idempotent of Example 0FG6. Remark 0FGE calls the motive
`(X, c₂, 0)` the *Lefschetz motive*; in the literature it is written `L`, `𝐋`, `𝐐(-1)` or
`h²(P¹_k)`.

## Main definitions

* `Stacks.WeilCohomology.ChowMotiveCat.lefschetzMotive`: the Lefschetz motive `(P¹_k, c₂, 0)` in
  the category `M_k` of Chow motives.

## Implementation notes

The motive is built with `Stacks.WeilCohomology.ChowMotiveCat.mk'` from the actual projective
line `Stacks.WeilCohomology.projectiveLineObj k`, the actual correspondence
`c₂ = Stacks.WeilCohomology.projectiveLineFibrePointCorr x hx` and its idempotence
`Stacks.WeilCohomology.projectiveLine_fibrePoint_comp_fibrePoint` (Example 0FG6), so any other
occurrence of `ChowMotiveCat.mk' (projectiveLineObj k) (projectiveLineFibrePointCorr x hx) _ 0`
is definitionally this motive.

## References

* [Stacks Project, Tag 0FGE](https://stacks.math.columbia.edu/tag/0FGE)
* [Stacks Project, Tag 0FG6](https://stacks.math.columbia.edu/tag/0FG6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

namespace ChowMotiveCat

variable {k : Type u} [Field k]
  (x : (fieldChowSituation k).S ⟶ relativeProjectiveLine (Spec (CommRingCat.of k)))
  (hx : x ≫ (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
    𝟙 (fieldChowSituation k).S)

/-- The composition rule `c₂ ∘ c₂ = c₂` of Example 0FG6, as an identity in
`Corr⁰(P¹_k, P¹_k)`: the form in which `Stacks.WeilCohomology.ChowMotiveCat.mk'` takes the
idempotence of a projector. -/
theorem comp_projectiveLineFibrePointCorr :
    (canonicalCorrespondenceCompositionData k).comp (projectiveLineFibrePointCorr x hx)
      (projectiveLineFibrePointCorr x hx) = projectiveLineFibrePointCorr x hx := by
  apply homOf_injective 0
  change homOf (0 + 0) _ = _
  rw [← homOf_comp_homOf, homOf, DirectSum.lof_eq_of]
  exact projectiveLine_fibrePoint_comp_fibrePoint x hx

/-- The *Lefschetz motive* `(P¹_k, c₂, 0)`: the projective line, cut down by the projector
`c₂ = [P¹_k × x]` of Example 0FG6 attached to a `k`-rational point `x`, with no twist. In the
literature it is denoted `L`, `𝐋`, `𝐐(-1)` or `h²(P¹_k)`. -/
@[stacks 0FGE "the Lefschetz motive (X, c_2, 0) for X = P^1_k, written L, bold L, Q(-1) or
h^2(P^1_k)"]
def lefschetzMotive : ChowMotiveCat k :=
  mk' (projectiveLineObj k) (projectiveLineFibrePointCorr x hx)
    (comp_projectiveLineFibrePointCorr x hx) 0

/-- The underlying scheme of the Lefschetz motive is the projective line `P¹_k`. -/
@[simp]
theorem lefschetzMotive_scheme : (lefschetzMotive x hx).scheme = projectiveLineObj k :=
  rfl

/-- The projector of the Lefschetz motive is `c₂ = [P¹_k × x]`. -/
@[simp]
theorem lefschetzMotive_projector :
    (lefschetzMotive x hx).projector = projectiveLineFibrePointCorr x hx :=
  mk'_projector _ _ _ _

/-- The twist of the Lefschetz motive is `0`. -/
@[simp]
theorem lefschetzMotive_twist : (lefschetzMotive x hx).twist = 0 :=
  rfl

end ChowMotiveCat

end Stacks.WeilCohomology

end
