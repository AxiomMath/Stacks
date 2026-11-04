module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# Pushing a cycle forward from an integral closed subscheme

This file defines the pushforward of a cycle along the closed immersion of a closed subscheme,
and shows that a sum `∑_i c_i` of cycles supported on a locally finite family of sets again has
locally finite support; together they give meaning to sums of cycles of the shape
`∑_i (Z_i → X)_* c_i`, where `{Z_i}` is a locally finite family of integral closed subschemes of
`X` and `c_i` is a cycle on `Z_i`.

The pushforward is the weighted pushforward `AlgebraicCycle.map`. A closed immersion is injective
on points and induces an isomorphism on residue fields, so it transports the coefficient at a
point of the subscheme to its image.

## Main definitions

* `Stacks.Chow.closedSubschemeCyclePushforward` — the pushforward of a cycle along the closed
  immersion of a closed subscheme.

## Main results

* `TopologicalSpace.IsImmediateSpecialization.map_of_isClosedEmbedding`,
  `TopologicalSpace.DimensionFunction.compClosedEmbedding` — a dimension function pulls back
  along a closed embedding, so a closed subscheme of a scheme carrying one carries one.
* `Stacks.Chow.locallyFiniteSupport_finsum` — a sum of cycles indexed by a locally finite family
  of sets containing their supports again has locally finite support.
* `Stacks.Chow.closedSubschemeCyclePushforward_apply`,
  `Stacks.Chow.closedSubschemeCyclePushforward_apply_of_notMem_range` — the coefficients of the
  pushforward.
* `Stacks.Chow.support_closedSubschemeCyclePushforward_subset` — the pushforward is supported on
  the closed subscheme.
* `Stacks.Chow.principalDivisorPushforward_eq` — the pushforward of a principal divisor, as used
  for rational equivalence, is this construction applied to the principal cycle.
* `Stacks.Chow.schemeDeltaDimension_integralComponentAt_of_coheight_one` — on an integral scheme
  of delta-dimension `n` the integral closed subscheme attached to a point of codimension one
  has delta-dimension `n - 1`.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace TopologicalSpace

/-! ### Dimension functions along a closed embedding -/

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/-- A closed embedding preserves immediateness of a specialization. -/
theorem IsImmediateSpecialization.map_of_isClosedEmbedding {f : Z → Y}
    (hf : Topology.IsClosedEmbedding f) {z z' : Z} (h : IsImmediateSpecialization z z') :
    IsImmediateSpecialization (f z) (f z') := by
  obtain ⟨hspec, hne, hmid⟩ := h
  refine ⟨hspec.map hf.continuous, fun he ↦ hne (hf.injective he), fun w hw hw' ↦ ?_⟩
  obtain ⟨z'', rfl⟩ := hw.mem_closed hf.isClosed_range ⟨z, rfl⟩
  exact (hmid z'' (hf.isInducing.specializes_iff.1 hw) (hf.isInducing.specializes_iff.1 hw')).imp
    (congrArg f) (congrArg f)

/-- The pullback `d ∘ f` of a dimension function `d` along a closed embedding `f`. -/
def DimensionFunction.compClosedEmbedding {f : Z → Y} (hf : Topology.IsClosedEmbedding f)
    (d : DimensionFunction Y) : DimensionFunction Z where
  toFun := d ∘ f
  strictAnti_specializes := by
    intro _ _ h hne
    exact d.strictAnti_specializes (h.map hf.continuous) fun he ↦ hne (hf.injective he)
  step_immediate := by
    intro _ _ h
    exact d.step_immediate (h.map_of_isClosedEmbedding hf)

/-- The pullback of `d` along `f` takes the value `d (f z)` at `z`. -/
@[simp]
theorem DimensionFunction.compClosedEmbedding_apply {f : Z → Y}
    (hf : Topology.IsClosedEmbedding f) (d : DimensionFunction Y) (z : Z) :
    d.compClosedEmbedding hf z = d (f z) := rfl

end TopologicalSpace

namespace Stacks.Chow

/-! ### Sums over a locally finite family of cycles -/

/-- A formal sum `∑_i c_i` of integer-valued functions, each supported in the corresponding
member of a locally finite family of sets, again has locally finite support. -/
theorem locallyFiniteSupport_finsum {Z : Type*} [TopologicalSpace Z] {ι : Type*} (E : ι → Set Z)
    (hE : LocallyFinite E) (c : ι → Z → ℤ) (hc : ∀ i, LocallyFiniteSupport (c i))
    (hsub : ∀ i, Function.support (c i) ⊆ E i) :
    LocallyFiniteSupport (fun z ↦ ∑ᶠ i, c i z) := by
  intro z₀
  obtain ⟨t, ht, hfin⟩ := hE z₀
  choose V hV hVfin using fun i : ι ↦ hc i z₀
  refine ⟨t ∩ ⋂ i ∈ {i | (E i ∩ t).Nonempty}, V i, ?_, ?_⟩
  · exact Filter.inter_mem ht ((Filter.biInter_mem hfin).2 fun i _ ↦ hV i)
  · refine Set.Finite.subset (hfin.biUnion fun i _ ↦ hVfin i) ?_
    rintro z ⟨⟨hzt, hzV⟩, hz⟩
    replace hz : (∑ᶠ i, c i z) ≠ 0 := hz
    obtain ⟨i, hi⟩ : ∃ i : ι, c i z ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (finsum_eq_zero_of_forall_eq_zero h)
    have hiE : i ∈ {i | (E i ∩ t).Nonempty} := ⟨z, hsub i hi, hzt⟩
    exact Set.mem_biUnion hiE ⟨Set.mem_iInter₂.1 hzV i hiE, hi⟩

/-! ### Pushing a cycle forward along a closed immersion -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)

/-- The pushforward to `X` of a cycle on a closed subscheme `W ⊆ X`, along the closed immersion
of `W`, with the weights of proper pushforward. -/
def closedSubschemeCyclePushforward (W : X.IdealSheafData) (c : AlgebraicCycle W.subscheme ℤ) :
    AlgebraicCycle X ℤ :=
  AlgebraicCycle.map W.subschemeι (relativeDimension C.dimensionFunction (W.subschemeι ≫ p))
    (relativeDimension C.dimensionFunction p) c

/-- The coefficient of the pushforward at `x` is a sum over the fibre of the closed immersion. -/
private theorem closedSubschemeCyclePushforward_eq_finsum (W : X.IdealSheafData)
    (c : AlgebraicCycle W.subscheme ℤ) (x : X) :
    closedSubschemeCyclePushforward C p W c x = ∑ᶠ y ∈ W.subschemeι.base ⁻¹' {x}, c y *
      (AlgebraicCycle.mapCoeff W.subschemeι
        (relativeDimension C.dimensionFunction (W.subschemeι ≫ p))
        (relativeDimension C.dimensionFunction p) y : ℤ) := rfl

/-- The pushforward of a cycle along a closed immersion carries the coefficient at a point of
the subscheme to its image. -/
@[simp]
theorem closedSubschemeCyclePushforward_apply (W : X.IdealSheafData)
    (c : AlgebraicCycle W.subscheme ℤ) (z : W.subscheme) :
    closedSubschemeCyclePushforward C p W c (W.subschemeι.base z) = c z := by
  have hinj : Function.Injective W.subschemeι.base := W.subschemeι.isClosedEmbedding.injective
  have hfib : W.subschemeι.base ⁻¹' {W.subschemeι.base z} = {z} := by
    ext y; simp [hinj.eq_iff]
  have hweight : ∀ y : W.subscheme, (AlgebraicCycle.mapCoeff W.subschemeι
      (relativeDimension C.dimensionFunction (W.subschemeι ≫ p))
      (relativeDimension C.dimensionFunction p) y : ℤ) = 1 := fun y ↦ by
    have h := relativeDimension_comp_closedImmersion C.dimensionFunction W.subschemeι p y
    simp [AlgebraicCycle.mapCoeff, h, residueDegree_eq_one_of_isClosedImmersion]
  rw [closedSubschemeCyclePushforward_eq_finsum, hfib, finsum_mem_singleton, hweight z, mul_one]

/-- The pushforward of a cycle along a closed immersion vanishes away from the closed
subscheme. -/
theorem closedSubschemeCyclePushforward_apply_of_notMem_range (W : X.IdealSheafData)
    (c : AlgebraicCycle W.subscheme ℤ) {x : X} (hx : x ∉ Set.range W.subschemeι.base) :
    closedSubschemeCyclePushforward C p W c x = 0 := by
  rw [closedSubschemeCyclePushforward_eq_finsum, Set.preimage_singleton_eq_empty.2 hx]
  simp

/-- The pushforward of a cycle along a closed immersion is supported on the closed
subscheme. -/
theorem support_closedSubschemeCyclePushforward_subset (W : X.IdealSheafData)
    (c : AlgebraicCycle W.subscheme ℤ) :
    Function.support (closedSubschemeCyclePushforward C p W c) ⊆ (W.support : Set X) := by
  intro x hx
  by_contra hxW
  exact hx (closedSubschemeCyclePushforward_apply_of_notMem_range C p W c
    (by rwa [W.range_subschemeι]))

/-- The pushforward of the principal divisor of a rational function on an integral closed
subscheme is the pushforward of the principal cycle of that function. -/
theorem principalDivisorPushforward_eq [LocallyOfFiniteType p] (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (g : (rationalFunctions W.subscheme)ˣ) :
    principalDivisorPushforward C p W hW g =
      letI := hW
      letI : IsLocallyNoetherian W.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
      closedSubschemeCyclePushforward C p W (principalCycle W.subscheme
        ((rationalFunctionsEquivFunctionField W.subscheme).1
          (g : rationalFunctions W.subscheme))) :=
  rfl

/-! ### The delta-dimension of the integral closed subscheme attached to a point -/

/-- On an integral scheme of delta-dimension `n` over the base, the integral closed subscheme
attached to a point of codimension one has delta-dimension `n - 1`, given a dimension function
`d` on `X` agreeing with `Stacks.Chow.relativeDimension`. -/
theorem schemeDeltaDimension_integralComponentAt_of_coheight_one [LocallyOfFiniteType p]
    [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) {d : DimensionFunction X}
    (hd : ∀ y, d y = relativeDimension C.dimensionFunction p y) {x : X}
    (hx : Order.coheight x = 1) :
    schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) = ((n - 1 : ℤ) : EInt) := by
  have _ := isIntegral_integralComponentAt (X := X) x
  rw [schemeDeltaDimension_eq_genericPoint C ((integralComponentAt x).subschemeι ≫ p),
    relativeDimension_comp_closedImmersion,
    show (integralComponentAt x).subschemeι.base
        (genericPoint (integralComponentAt x).subscheme) = x from
      genericPointOf_integralComponentAt x,
    ← deltaDimension_closure_singleton C p x]
  exact congrArg (fun z : ℤ => (z : EInt))
    (deltaDimension_closure_singleton_of_coheight_one C p hn hd hx)

end Stacks.Chow

end
