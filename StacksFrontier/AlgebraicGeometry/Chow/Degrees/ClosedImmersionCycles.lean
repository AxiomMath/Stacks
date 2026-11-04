module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# Cycles along a closed immersion

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, and let `i : Z ⟶ X` be a closed immersion from a scheme `Z`
again locally of finite type over `S`. Proper pushforward along `i` transports the coefficient
of a cycle on `Z` at `z` to the coefficient at `i z`, and vanishes away from the image of `i`.

In the other direction a `k`-cycle on `X` pulls back along `i` to a `k`-cycle on `Z`, and
discarding the coefficients of a `k`-cycle on `X` outside a subset of `X` gives again a
`k`-cycle.

## Main definitions

* `Stacks.Chow.cyclePullbackAlongClosedImmersion` — the `k`-cycle on `Z` whose coefficient at `z`
  is the coefficient of a given `k`-cycle on `X` at `i z`.
* `Stacks.Chow.cycleRestrict` — the `k`-cycle obtained from a `k`-cycle on `X` by discarding the
  coefficients outside a subset of `X`.

## Main results

* `Stacks.Chow.properPushforward_apply_of_isClosedImmersion` — along a closed immersion the
  coefficient of the proper pushforward is the unweighted locally finite sum over the fibre.
* `Stacks.Chow.properPushforward_apply_image_of_isClosedImmersion`,
  `Stacks.Chow.properPushforward_apply_of_notMem_range` — the two values that sum takes: the
  coefficient at `i z` is the coefficient at `z`, and the coefficient off the image of `i` is
  zero.
* `Stacks.Chow.properPushforward_cyclePullbackAlongClosedImmersion_apply` — pushing a pulled-back
  cycle forward again is the restriction of the original cycle to the image of the immersion.

## References

* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}}

/-! ### Proper pushforward along a closed immersion -/

section ClosedImmersion

variable (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (k : ℤ)

/-- The coefficient of the proper pushforward of a `k`-cycle along a closed immersion is the plain
locally finite sum of the coefficients over the fibre. -/
theorem properPushforward_apply_of_isClosedImmersion (c : CycleGroup C sZ k) (y : X) :
    (properPushforward C sZ sX i hi k c).1 y = ∑ᶠ z ∈ i.base ⁻¹' {y}, c.1 z := by
  rw [properPushforward_apply]
  simp_rw [← hi, relativeDimension_comp_closedImmersion C.dimensionFunction i sX,
    residueDegree_eq_one_of_isClosedImmersion i]
  simp

/-- Proper pushforward along a closed immersion `i` carries the coefficient at `z` to the
coefficient at `i z`. -/
theorem properPushforward_apply_image_of_isClosedImmersion (c : CycleGroup C sZ k) (z : Z) :
    (properPushforward C sZ sX i hi k c).1 (i.base z) = c.1 z := by
  have hfibre : i.base ⁻¹' {i.base z} = {z} := by
    ext w
    simp [i.isClosedEmbedding.injective.eq_iff]
  rw [properPushforward_apply_of_isClosedImmersion, hfibre, finsum_mem_singleton]

/-- Proper pushforward along a closed immersion vanishes away from the image. -/
theorem properPushforward_apply_of_notMem_range (c : CycleGroup C sZ k) {y : X}
    (hy : y ∉ Set.range i.base) : (properPushforward C sZ sX i hi k c).1 y = 0 := by
  rw [properPushforward_apply_of_isClosedImmersion, Set.preimage_singleton_eq_empty.2 hy,
    finsum_mem_empty]

/-- The pullback of a `k`-cycle on `X` along a closed immersion `i : Z ⟶ X` over the base: the
coefficient at `z` is the coefficient of the given cycle at `i z`. -/
def cyclePullbackAlongClosedImmersion (c : CycleGroup C sX k) : CycleGroup C sZ k :=
  ⟨{ toFun := fun z ↦ c.1 (i.base z)
     supportWithinDomain' := by simp
     supportLocallyFiniteWithinDomain' := fun z _ ↦ by
       obtain ⟨t, ht, hfin⟩ := c.1.locallyFiniteSupport (i.base z)
       exact ⟨i.base ⁻¹' t, i.continuous.continuousAt.preimage_mem_nhds ht,
         (hfin.preimage fun _ _ _ _ hab ↦ i.isClosedEmbedding.injective hab).subset
           fun w hw ↦ ⟨hw.1, by simpa [Function.mem_support] using hw.2⟩⟩ },
    by
      rw [mem_cyclesOfDimension_iff_forall_point]
      intro z hz
      rw [← hi, relativeDimension_comp_closedImmersion]
      exact (mem_cyclesOfDimension_iff_forall_point C sX k c.1).1 c.2 (i.base z)
        (by simpa using hz)⟩

/-- The coefficient of the pullback of `c` along `i` at `z` is the coefficient of `c` at `i z`. -/
@[simp]
theorem cyclePullbackAlongClosedImmersion_apply (c : CycleGroup C sX k) (z : Z) :
    (cyclePullbackAlongClosedImmersion C sZ sX i hi k c).1 z = c.1 (i.base z) :=
  rfl

end ClosedImmersion

/-! ### Restricting a cycle to a subset -/

section Restrict

variable (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (k : ℤ)

/-- The restriction of a `k`-cycle on `X` to a subset `s ⊆ X`: the coefficients inside `s` are
kept and those outside are discarded. -/
def cycleRestrict (c : CycleGroup C sX k) (s : Set X) : CycleGroup C sX k :=
  ⟨{ toFun := s.indicator c.1
     supportWithinDomain' := by simp
     supportLocallyFiniteWithinDomain' := fun x _ ↦ by
       obtain ⟨t, ht, hfin⟩ := c.1.locallyFiniteSupport x
       refine ⟨t, ht, hfin.subset (Set.inter_subset_inter_right _ ?_)⟩
       rw [Set.support_indicator]
       exact Set.inter_subset_right },
    by
      rw [mem_cyclesOfDimension_iff_forall_point]
      intro x hx
      refine (mem_cyclesOfDimension_iff_forall_point C sX k c.1).1 c.2 x fun h ↦ hx ?_
      simp [Set.indicator_apply_eq_zero, h]⟩

/-- The coefficient of the restriction of `c` to `s` at `x` is the indicator of `s` applied to
the coefficients of `c` at `x`. -/
@[simp]
theorem cycleRestrict_apply (c : CycleGroup C sX k) (s : Set X) (x : X) :
    (cycleRestrict C sX k c s).1 x = s.indicator c.1 x :=
  rfl

/-- Inside the subset the restriction keeps the coefficient. -/
theorem cycleRestrict_apply_of_mem (c : CycleGroup C sX k) {s : Set X} {x : X} (hx : x ∈ s) :
    (cycleRestrict C sX k c s).1 x = c.1 x := by
  rw [cycleRestrict_apply, Set.indicator_of_mem hx]

/-- Outside the subset the restriction has coefficient zero. -/
theorem cycleRestrict_apply_of_notMem (c : CycleGroup C sX k) {s : Set X} {x : X} (hx : x ∉ s) :
    (cycleRestrict C sX k c s).1 x = 0 := by
  rw [cycleRestrict_apply, Set.indicator_of_notMem hx]

end Restrict

/-! ### Pushing a pulled-back cycle forward again -/

/-- Pulling a `k`-cycle on `X` back along a closed immersion `i : Z ⟶ X` and pushing it forward
again restricts it to the image of `i`: at a point of the image the coefficient is unchanged, and
off the image it is zero. -/
theorem properPushforward_cyclePullbackAlongClosedImmersion_apply (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : i ≫ sX = sZ) (k : ℤ) (c : CycleGroup C sX k) (y : X) :
    (properPushforward C sZ sX i hi k (cyclePullbackAlongClosedImmersion C sZ sX i hi k c)).1 y =
      (Set.range i.base).indicator c.1 y := by
  by_cases hy : y ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hy
    rw [properPushforward_apply_image_of_isClosedImmersion,
      cyclePullbackAlongClosedImmersion_apply, Set.indicator_of_mem (Set.mem_range_self z)]
  · rw [properPushforward_apply_of_notMem_range C sZ sX i hi k _ hy,
      Set.indicator_of_notMem hy]

end Stacks.Chow

end
