module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.Blowup.Basic
public import StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.RationalSingularPointsResolution

/-!
# The blowup of a regular surface at a closed point is regular and integral

Let `Y` be a locally Noetherian scheme and `y` a closed point whose local ring is regular of
dimension two. In the construction of [Stacks, Tag 0D5E] the blowup `π : Z ⟶ Y` of `Y` at `y`
is again regular when `Y` is ([Stacks, Tag 0AGR], read pointwise), integral when `Y` is, and an
isomorphism over `Y ∖ {y}` ([Stacks, Tag 02OS]).

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.isRegular_pointBlowup`: `Z` is regular if `Y` is.
* `Stacks.Examples.CurveFamilyNotScheme.isIntegral_pointBlowup`: `Z` is integral if `Y` is.
* `Stacks.Examples.CurveFamilyNotScheme.isIso_pointBlowupToBase_restrict_compl`: `π` is an
  isomorphism over the complement of `y`.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

variable {Y : Scheme.{u}} (y : Y) (hy : IsClosed ({y} : Set Y))

/-- The complement of the closed point `y`, as an open of `Y`. -/
def complPointOpen : Y.Opens := ⟨{y}ᶜ, hy.isOpen_compl⟩

/-- The support of the point ideal is the point. -/
theorem coe_support_pointIdeal : ((pointIdeal y hy).support : Set Y) = {y} :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- **The blowup at `y` is an isomorphism over `Y ∖ {y}`.** -/
theorem isIso_pointBlowupToBase_restrict_compl :
    IsIso (pointBlowupToBase y hy ∣_ complPointOpen y hy) :=
  isIso_blowUpToBase_restrict_of_subset_compl_support _ _ fun z hz hz' => by
    rw [coe_support_pointIdeal] at hz'
    exact hz hz'

/-- The blowup at a closed point of a locally Noetherian scheme is locally Noetherian, being of
finite type over it. -/
instance isLocallyNoetherian_pointBlowup [IsLocallyNoetherian Y] :
    IsLocallyNoetherian (pointBlowup y hy) :=
  LocallyOfFiniteType.isLocallyNoetherian (pointBlowupToBase y hy)

/-- **The blowup of a regular scheme at a closed point with two-dimensional local ring is
regular.** -/
theorem isRegular_pointBlowup [IsLocallyNoetherian Y] (hreg : IsRegular Y)
    (hydim : ringKrullDim (Y.presheaf.stalk y) = 2) : IsRegular (pointBlowup y hy) :=
  isRegular_of_stalks fun w =>
    isRegularLocalRing_stalk_blowUp_of_isRegularLocalRing_stalk_blowUpToBase _ y hy rfl
      (hreg.isRegularLocalRing_stalk y) hydim w (hreg.isRegularLocalRing_stalk _)

/-- The point ideal of a closed point with two-dimensional local ring on an integral scheme is
not the zero ideal sheaf. -/
theorem pointIdeal_ne_bot [IsIntegral Y] (hydim : ringKrullDim (Y.presheaf.stalk y) = 2) :
    pointIdeal y hy ≠ ⊥ := by
  intro h
  have h1 : ((pointIdeal y hy).support : Set Y) = Set.univ := by
    rw [h, Scheme.IdealSheafData.support_bot]
    rfl
  rw [coe_support_pointIdeal] at h1
  have hmem : genericPoint Y ∈ ({y} : Set Y) := h1 ▸ Set.mem_univ _
  exact ne_genericPoint_of_ringKrullDim_stalk_eq_two y hydim (Set.mem_singleton_iff.mp hmem).symm

/-- **The blowup of an integral scheme at a closed point with two-dimensional local ring is
integral.** -/
theorem isIntegral_pointBlowup [IsIntegral Y] (hydim : ringKrullDim (Y.presheaf.stalk y) = 2) :
    IsIntegral (pointBlowup y hy) :=
  isIntegral_blowUp _ (pointIdeal_ne_bot y hy hydim)

end Stacks.Examples.CurveFamilyNotScheme

end
