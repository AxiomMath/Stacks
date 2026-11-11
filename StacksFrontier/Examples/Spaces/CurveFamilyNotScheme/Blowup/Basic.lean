module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic

/-!
# The blowup of a surface at a point of a curve, set-theoretically

In the construction of Stacks 0D5E, `π : Z ⟶ Y` is the blowup of the surface `Y` at a closed
point `y` of the central fibre `Y₀`, `E = π⁻¹(y)` is the exceptional divisor and `C` is the strict
transform of `Y₀`. This file sets up the blowup at a closed point of an arbitrary locally
Noetherian scheme, the exceptional set and the strict transform of a closed subset as sets, and
proves the set-theoretic facts the non-representability argument uses: `π` is proper, hence a
closed map, `π` maps `E` to `y`, and `π⁻¹(Y₀) ⊆ E ∪ C`.

## Main definitions

* `Stacks.Examples.CurveFamilyNotScheme.pointIdeal`: the reduced ideal sheaf of a closed point.
* `Stacks.Examples.CurveFamilyNotScheme.pointBlowup`: the blowup at a closed point, with
  structure morphism `Stacks.Examples.CurveFamilyNotScheme.pointBlowupToBase`.
* `Stacks.Examples.CurveFamilyNotScheme.exceptionalSet`: `π⁻¹(y)`.
* `Stacks.Examples.CurveFamilyNotScheme.strictTransformSet`: the closure of `π⁻¹(V ∖ {y})`.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.isProper_pointBlowupToBase`: `π` is proper.
* `Stacks.Examples.CurveFamilyNotScheme.preimage_subset_exceptionalSet_union`:
  `π⁻¹(V) ⊆ E ∪ C`.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

variable {Y : Scheme.{u}} (y : Y) (hy : IsClosed ({y} : Set Y))

/-- The reduced ideal sheaf of a closed point. -/
abbrev pointIdeal : Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)

/-- The blowup of `Y` at the closed point `y`. -/
abbrev pointBlowup : Scheme.{u} := blowUp (pointIdeal y hy)

/-- The blowup morphism `π : Z ⟶ Y` at the closed point `y`. -/
abbrev pointBlowupToBase : pointBlowup y hy ⟶ Y := blowUpToBase (pointIdeal y hy)

/-- **The blowup at a closed point of a locally Noetherian scheme is proper.** -/
instance isProper_pointBlowupToBase [IsLocallyNoetherian Y] :
    IsProper (pointBlowupToBase y hy) :=
  isProper_blowUpToBase_of_fg _ fun U => by
    haveI := IsLocallyNoetherian.component_noetherian U
    exact IsNoetherian.noetherian _

/-- The exceptional set `E = π⁻¹(y)`. -/
def exceptionalSet : Set (pointBlowup y hy) := pointBlowupToBase y hy ⁻¹' {y}

/-- The strict transform of a subset `V ⊆ Y`, as a set: the closure of `π⁻¹(V ∖ {y})`. -/
def strictTransformSet (V : Set Y) : Set (pointBlowup y hy) :=
  closure (pointBlowupToBase y hy ⁻¹' (V \ {y}))

/-- The strict transform of a subset is closed. -/
theorem isClosed_strictTransformSet (V : Set Y) : IsClosed (strictTransformSet y hy V) :=
  isClosed_closure

/-- The exceptional set is closed. -/
theorem isClosed_exceptionalSet : IsClosed (exceptionalSet y hy) :=
  hy.preimage (pointBlowupToBase y hy).continuous

/-- The exceptional set maps to `y`. -/
theorem pointBlowupToBase_eq_of_mem_exceptionalSet {z : pointBlowup y hy}
    (hz : z ∈ exceptionalSet y hy) : pointBlowupToBase y hy z = y := hz

/-- The preimage of `V` lies in the union of the exceptional set and the strict transform of
`V`. -/
theorem preimage_subset_exceptionalSet_union (V : Set Y) :
    pointBlowupToBase y hy ⁻¹' V ⊆ exceptionalSet y hy ∪ strictTransformSet y hy V := by
  intro z hz
  by_cases hzy : pointBlowupToBase y hy z = y
  · exact Or.inl hzy
  · exact Or.inr (subset_closure ⟨hz, hzy⟩)

end Stacks.Examples.CurveFamilyNotScheme

end
