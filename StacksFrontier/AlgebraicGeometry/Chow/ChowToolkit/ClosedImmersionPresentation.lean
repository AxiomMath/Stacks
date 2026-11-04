module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction

/-!
# Moving a presentation by integral components across a closed immersion

A `k`-cycle on a scheme `X` is the locally finite sum of the fundamental cycles of integral
closed subschemes of delta-dimension `k` (Stacks 02RW). If the cycle vanishes off a closed
subscheme `j : Z ⟶ X`, every member of such a presentation carrying a nonzero coefficient lies
inside `Z`, and the presentation ought to be readable as a presentation of the cycle's inverse
image on `Z`.

This file supplies that step. For an integral closed subscheme `V ⊆ X` whose generic point lies
in the image of `j`, `Stacks.Chow.integralComponentAbove` is the integral closed subscheme of `Z`
on the closure of the unique point of `Z` above that generic point. It has the same
delta-dimension over the base, its support is carried by the inverse image of the support of `V`,
and its fundamental cycle is the inverse image of the fundamental cycle of `V`. Summing over the
family turns a presentation on `X` into a presentation on `Z`.

## Main definitions

* `Stacks.Chow.integralComponentAbove` — the integral closed subscheme of `Z` above an integral
  closed subscheme of `X` whose generic point lies in the image of a closed immersion.

## Main results

* `Stacks.Chow.schemeDeltaDimension_integralComponentAbove` — it has the same delta-dimension.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_integralComponentAbove_apply` — its fundamental
  cycle is the inverse image of the fundamental cycle downstairs.
* `Stacks.Chow.cyclePullbackAlongClosedImmersion_apply_of_presentation` — a presentation by
  integral components, read on the closed subscheme.
* `Stacks.Chow.extendCycleGroup_cyclePullbackAlongClosedImmersion_apply_of_presentation` — and
  then a rule on the integral components of the closed subscheme, read off the transported
  presentation.

## References

* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (j : Z ⟶ X) [IsClosedImmersion j]

/-! ### The component above an integral closed subscheme of the image -/

/-- **The generic point of a closed subscheme of `X` contained in the image of a closed
immersion, read on `Z`.** A closed immersion is injective on points, so this is the unique point
of `Z` above the generic point. -/
def genericPointAbove (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hmem : genericPointOf V hV ∈ Set.range j.base) : Z :=
  hmem.choose

omit [IsClosedImmersion j] in
/-- The image under `j` of `genericPointAbove j V hV hmem` is the generic point of `V`. -/
@[simp]
theorem base_genericPointAbove (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hmem : genericPointOf V hV ∈ Set.range j.base) :
    j.base (genericPointAbove j V hV hmem) = genericPointOf V hV :=
  hmem.choose_spec

/-- **The integral closed subscheme of `Z` above an integral closed subscheme `V ⊆ X` whose
generic point lies in the image of a closed immersion `j : Z ⟶ X`**: the reduced induced
structure on the closure of the point of `Z` above the generic point of `V`. -/
def integralComponentAbove (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hmem : genericPointOf V hV ∈ Set.range j.base) : Z.IdealSheafData :=
  integralComponentAt (genericPointAbove j V hV hmem)

omit [IsClosedImmersion j] in
/-- The closed subscheme `integralComponentAbove j V hV hmem` of `Z` is integral. -/
theorem isIntegral_integralComponentAbove (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hmem : genericPointOf V hV ∈ Set.range j.base) :
    IsIntegral (integralComponentAbove j V hV hmem).subscheme :=
  isIntegral_integralComponentAt _

omit [IsClosedImmersion j] in
/-- The generic point of `integralComponentAbove j V hV hmem` is
`genericPointAbove j V hV hmem`. -/
@[simp]
theorem genericPointOf_integralComponentAbove (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme) (hmem : genericPointOf V hV ∈ Set.range j.base) :
    genericPointOf (integralComponentAbove j V hV hmem)
        (isIntegral_integralComponentAbove j V hV hmem) =
      genericPointAbove j V hV hmem :=
  genericPointOf_integralComponentAt _

omit [IsClosedImmersion j] in
/-- **The component above `V` is carried by the inverse image of `V`.** Its support is the
closure of a point above the generic point of `V`, and a closed immersion is continuous. -/
theorem coe_support_integralComponentAbove_subset (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme) (hmem : genericPointOf V hV ∈ Set.range j.base) :
    ((integralComponentAbove j V hV hmem).support : Set Z) ⊆
      j.base ⁻¹' ((V).support : Set X) := by
  rw [integralComponentAbove, coe_support_integralComponentAt,
    support_eq_closure_genericPointOf V hV]
  refine (IsClosed.closure_subset_iff ?_).mpr ?_
  · exact isClosed_closure.preimage j.continuous
  · rw [Set.singleton_subset_iff, Set.mem_preimage, base_genericPointAbove]
    exact subset_closure rfl

/-- **The component above `V` has the delta-dimension of `V`.** Both are the relative dimension
of the generic point, and the relative dimension of a point is unchanged by a closed immersion. -/
theorem schemeDeltaDimension_integralComponentAbove (hj : j ≫ sX = sZ) (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme) (hmem : genericPointOf V hV ∈ Set.range j.base) {k : ℤ}
    (hDim : schemeDeltaDimension C (V.subschemeι ≫ sX) = (k : EInt)) :
    schemeDeltaDimension C ((integralComponentAbove j V hV hmem).subschemeι ≫ sZ) =
      (k : EInt) := by
  refine schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sZ _ ?_
  rw [← hj, relativeDimension_comp_closedImmersion, base_genericPointAbove]
  exact relativeDimension_genericPointOf C sX V hV hDim

/-- **The fundamental cycle of the component above `V` is the inverse image of the fundamental
cycle of `V`.** Both have coefficient `1` at the generic point and `0` elsewhere, and a closed
immersion matches up the two generic points injectively. -/
theorem cycleAssociatedToClosedSubscheme_integralComponentAbove_apply (hj : j ≫ sX = sZ)
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hmem : genericPointOf V hV ∈ Set.range j.base) {k : ℤ}
    (hDim : schemeDeltaDimension C (V.subschemeι ≫ sX) = (k : EInt)) (z : Z) :
    (cycleAssociatedToClosedSubscheme C sZ
        (integralComponentAbove j V hV hmem).subschemeι k).1 z =
      (cycleAssociatedToClosedSubscheme C sX V.subschemeι k).1 (j.base z) := by
  by_cases hz : z = genericPointAbove j V hV hmem
  · subst hz
    rw [base_genericPointAbove,
      cycleAssociatedToClosedSubscheme_integral_apply C sX V hV hDim]
    have h1 := cycleAssociatedToClosedSubscheme_integral_apply C sZ
      (integralComponentAbove j V hV hmem) (isIntegral_integralComponentAbove j V hV hmem)
      (schemeDeltaDimension_integralComponentAbove C sX sZ j hj V hV hmem hDim)
    rwa [genericPointOf_integralComponentAbove] at h1
  · rw [cycleAssociatedToClosedSubscheme_integral_apply_of_ne C sZ
      (integralComponentAbove j V hV hmem) (isIntegral_integralComponentAbove j V hV hmem) k
      (by rwa [genericPointOf_integralComponentAbove]),
      cycleAssociatedToClosedSubscheme_integral_apply_of_ne C sX V hV k ?_]
    rw [← base_genericPointAbove j V hV hmem]
    exact fun he ↦ hz (j.isClosedEmbedding.injective he)

omit [IsClosedImmersion j] in
/-- **The components above a locally finite family are a locally finite family.** Each is carried
by the inverse image of the corresponding member, and the inverse images of a locally finite
family under a continuous map are locally finite (Stacks 02R9). -/
theorem locallyFinite_support_integralComponentAbove {J : Type*} (V : J → X.IdealSheafData)
    (hV : ∀ i, IsIntegral (V i).subscheme)
    (hmem : ∀ i, genericPointOf (V i) (hV i) ∈ Set.range j.base)
    (hLocal : LocallyFinite fun i ↦ ((V i).support : Set X)) :
    LocallyFinite fun i ↦
      ((integralComponentAbove j (V i) (hV i) (hmem i)).support : Set Z) :=
  (hLocal.preimage_continuous j.continuous).subset fun i ↦
    coe_support_integralComponentAbove_subset j (V i) (hV i) (hmem i)

/-! ### A presentation, read on the closed subscheme -/

/-- **A presentation by integral components moves across a closed immersion.** If a `k`-cycle `α`
on `X` is the locally finite sum `∑ n_i [V_i]` of fundamental cycles of integral closed
subschemes of delta-dimension `k`, each of whose generic points lies in the image of a closed
immersion `j : Z ⟶ X`, then the inverse image of `α` on `Z` is the corresponding locally finite
sum of the fundamental cycles of the components above the `V_i`.

Only the coefficientwise identity is needed: the inverse image of a cycle along a closed
immersion reads off the coefficient at the image point, and the fundamental cycle of the component
above `V_i` is the inverse image of the fundamental cycle of `V_i`. -/
theorem cyclePullbackAlongClosedImmersion_apply_of_presentation (hj : j ≫ sX = sZ) {k : ℤ}
    {J : Type*} (V : J → X.IdealSheafData) (hV : ∀ i, IsIntegral (V i).subscheme)
    (hDim : ∀ i, schemeDeltaDimension C ((V i).subschemeι ≫ sX) = (k : EInt))
    (hmem : ∀ i, genericPointOf (V i) (hV i) ∈ Set.range j.base) (n : J → ℤ)
    (α : CycleGroup C sX k)
    (hα : ∀ x : X, α.1 x = ∑ᶠ i : J, n i *
      (cycleAssociatedToClosedSubscheme C sX (V i).subschemeι k).1 x) (z : Z) :
    (cyclePullbackAlongClosedImmersion C sZ sX j hj k α).1 z =
      ∑ᶠ i : J, n i * (cycleAssociatedToClosedSubscheme C sZ
        (integralComponentAbove j (V i) (hV i) (hmem i)).subschemeι k).1 z := by
  rw [cyclePullbackAlongClosedImmersion_apply, hα (j.base z)]
  exact finsum_congr fun i ↦ congrArg (n i * ·)
    (cycleAssociatedToClosedSubscheme_integralComponentAbove_apply C sX sZ j hj (V i) (hV i)
      (hmem i) (hDim i) z).symm

/-- **A rule on the integral components of a closed subscheme, read off a presentation
upstairs.** This is `Stacks.Chow.IntegralComponentRule.extendCycleGroup_apply_of_presentation`
for the family transported by
`Stacks.Chow.cyclePullbackAlongClosedImmersion_apply_of_presentation`: a `(k+1)`-cycle on `X`
presented by integral closed subschemes lying inside a closed subscheme `Z ⊆ X` is, on `Z`, the
same locally finite combination of the components above them, and a rule on integral components
of `Z` is therefore the corresponding combination of its values on those components. -/
theorem extendCycleGroup_cyclePullbackAlongClosedImmersion_apply_of_presentation (hj : j ≫ sX = sZ)
    {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {g : Y ⟶ Z} {k : ℤ}
    (R : IntegralComponentRule C sZ sY g k) {J : Type u} (V : J → X.IdealSheafData)
    (hV : ∀ i, IsIntegral (V i).subscheme)
    (hDim : ∀ i, schemeDeltaDimension C ((V i).subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt))
    (hmem : ∀ i, genericPointOf (V i) (hV i) ∈ Set.range j.base)
    (hLocal : LocallyFinite fun i ↦ ((V i).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C sX (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ i : J, n i *
      (cycleAssociatedToClosedSubscheme C sX (V i).subschemeι (k + 1)).1 x) (y : Y) :
    (R.extendCycleGroup
        (cyclePullbackAlongClosedImmersion C sZ sX j hj (k + 1) α)).1 y =
      ∑ᶠ i : J, n i * (R.cycle (integralComponentAbove j (V i) (hV i) (hmem i))
        (isIntegral_integralComponentAbove j (V i) (hV i) (hmem i))
        (schemeDeltaDimension_integralComponentAbove C sX sZ j hj (V i) (hV i)
          (hmem i) (hDim i))).1 y :=
  R.extendCycleGroup_apply_of_presentation
    (fun i ↦ integralComponentAbove j (V i) (hV i) (hmem i))
    (fun i ↦ isIntegral_integralComponentAbove j (V i) (hV i) (hmem i))
    (fun i ↦ schemeDeltaDimension_integralComponentAbove C sX sZ j hj (V i) (hV i)
      (hmem i) (hDim i))
    (locallyFinite_support_integralComponentAbove j V hV hmem hLocal) n _
    (cyclePullbackAlongClosedImmersion_apply_of_presentation C sX sZ j hj V hV hDim hmem n α hα) y

/-! ### The hypothesis on the generic points, from a containment of supports -/

/-- **A closed subscheme carried by another has its generic point in the image.** The support of
an integral closed subscheme is the closure of its generic point, and the image of the closed
immersion of a quasi-coherent ideal sheaf is its support. -/
theorem mem_range_subschemeι_genericPointOf (V I : X.IdealSheafData)
    (hV : IsIntegral V.subscheme) (hsub : ((V).support : Set X) ⊆ (I.support : Set X)) :
    genericPointOf V hV ∈ Set.range I.subschemeι.base := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  refine hsub ?_
  rw [support_eq_closure_genericPointOf V hV]
  exact subset_closure rfl

end Stacks.Chow

end
