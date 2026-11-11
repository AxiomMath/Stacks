module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.Instance.FormalNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension

/-!
# The local rings of the blown-up cubic surface have dimension at most two

In the construction of [Stacks, Tag 0D5E], `π : Z ⟶ Y` is the blowup of the cubic surface `Y` at
the chosen closed point `y` of the central fibre. This file shows that `π` is birational (it is an
isomorphism over `Y ∖ {y}`, which contains the generic points of `Y` and `Z`), hence, being
proper, preserves dimension, so that `dim Z = dim Y = 2` and every local ring of `Z` has Krull
dimension at most two.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.isBirational_cubicBlowupToBase`: `π` is birational.
* `Stacks.Examples.CurveFamilyNotScheme.topologicalKrullDim_cubicBlowup`: `dim Z = 2`.
* `Stacks.Examples.CurveFamilyNotScheme.ringKrullDim_stalk_cubicBlowup_le_two`: every local ring
  of `Z` has Krull dimension at most two.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

variable (k : Type u) [Field k] [IsAlgClosed k] [Uncountable k] (h3 : ringChar k ≠ 3)

/-- The blown-up cubic surface `Z` is integral. -/
instance isIntegral_cubicBlowup : IsIntegral (cubicBlowup k h3) :=
  isIntegral_pointBlowup _ _ (ringKrullDim_stalk_cubicSurface k h3 _ (isClosed_chosenPoint k h3))

/-- **The blowup `π : Z ⟶ Y` of the cubic surface at the chosen point is birational**: it is an
isomorphism over `Y ∖ {y}`, which contains the generic point of `Y` and whose inverse image
contains the generic point of `Z`. -/
theorem isBirational_cubicBlowupToBase :
    IsBirational (pointBlowupToBase (chosenPoint k h3) (isClosed_chosenPoint k h3)) := by
  set f := pointBlowupToBase (chosenPoint k h3) (isClosed_chosenPoint k h3)
  set U := complPointOpen (chosenPoint k h3) (isClosed_chosenPoint k h3)
  have hiso : IsIso (f ∣_ U) := isIso_pointBlowupToBase_restrict_compl _ _
  have hY : genericPoint (cubicSurface k) ∈ U := fun h =>
    ne_genericPoint_of_ringKrullDim_stalk_eq_two _
      (ringKrullDim_stalk_cubicSurface k h3 _ (isClosed_chosenPoint k h3)) h.symm
  have hne : (f ⁻¹ᵁ U : Set (cubicBlowup k h3)).Nonempty := by
    obtain ⟨z, -⟩ := (f ∣_ U).surjective ⟨_, hY⟩
    exact ⟨z.1, z.2⟩
  have hZ : genericPoint (cubicBlowup k h3) ∈ f ⁻¹ᵁ U :=
    ((genericPoint_spec (cubicBlowup k h3)).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).2
      (by simpa using hne)
  refine isBirational_of_isIso_morphismRestrict f U hiso ?_ ?_
  · intro x hx
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    exact hZ
  · intro x hx
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    exact hY

/-- **The blown-up cubic surface has dimension two**: the proper birational morphism
`π : Z ⟶ Y` preserves dimension. -/
theorem topologicalKrullDim_cubicBlowup :
    topologicalKrullDim (cubicBlowup k h3) = 2 := by
  rw [(isBirational_cubicBlowupToBase k h3).topologicalKrullDim_eq_of_isClosedMap
    (pointBlowupToBase _ _).isClosedMap, topologicalKrullDim_cubicSurface k h3]

/-- **Every local ring of the blown-up cubic surface has Krull dimension at most two.** -/
theorem ringKrullDim_stalk_cubicBlowup_le_two (z : cubicBlowup k h3) :
    ringKrullDim ((cubicBlowup k h3).presheaf.stalk z) ≤ 2 := by
  rw [← topologicalKrullDim_cubicBlowup k h3,
    topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  exact le_iSup (fun x : cubicBlowup k h3 => ringKrullDim ((cubicBlowup k h3).presheaf.stalk x)) z

end Stacks.Examples.CurveFamilyNotScheme

end
