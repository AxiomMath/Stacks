module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InfiniteSumsRationalEquivalence

/-!
# Flat pullback of a locally finite sum of cycles

In Situation 0EDT let `f : X ⟶ Y` be a flat morphism of good algebraic spaces of relative
dimension `r`, and let `α_i ∈ Z_m(Y)` be cycles supported on the members `T_i` of a locally
finite collection of subsets of `|Y|`. The pullbacks `f^*α_i` are supported on the inverse
images `|f|^{-1}(T_i)`, which again form a locally finite collection, and

`f^*(∑ α_i) = ∑ f^*α_i`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.flatPullbackMap_locallyFiniteCycleSum`:
  `f^*(∑ α_i) = ∑ f^*α_i`.

## References

* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) {I : Type v}

/-- The pullback `f^*α` of a cycle supported on `T ⊆ |Y|` is supported on `|f|^{-1}(T)`. -/
theorem subspacePointSet_subset_of_flatPullbackMap_ne_zero (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (T : Set (points D.site D.base D.base_mem Y)) (α : CycleGroup D sY m)
    (hαT : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
      α.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn α).1 W ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X W.subspace ⊆
      pointsMap D.site D.base D.base_mem X f ⁻¹' T := by
  obtain ⟨A, hA⟩ := exists_ne_zero_of_flatPullbackCoeff_ne_zero D sX hX sY hY f hbase r hflat hr
    m α W hW
  exact (subspacePointSet_subset_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr A W
    hA.2).trans (Set.preimage_mono (hαT A hA.1))

/-- **Flat pullback commutes with locally finite sums**: `f^*(∑ α_i) = ∑ f^*α_i`, the sum on
the right being over the locally finite collection of inverse images `|f|^{-1}(T_i)`. -/
theorem flatPullbackMap_locallyFiniteCycleSum (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (T : I → Set (points D.site D.base D.base_mem Y)) (hT : LocallyFinite T)
    (α : I → CycleGroup D sY m)
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem Y),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T i) :
    flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
        (locallyFiniteCycleSum D sY m T hT α hαT) =
      locallyFiniteCycleSum D sX n (fun i => pointsMap D.site D.base D.base_mem X f ⁻¹' T i)
        (hT.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem f))
        (fun i => flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn (α i))
        (fun i => subspacePointSet_subset_of_flatPullbackMap_ne_zero D sX hX sY hY f hbase r
          hflat hr m n hmn (T i) (α i) (hαT i)) := by
  classical
  refine Subtype.ext (funext fun W => ?_)
  change flatPullbackCoeff D sX hX sY hY f hbase r hflat hr m
      (locallyFiniteCycleSum D sY m T hT α hαT) W =
    ∑ᶠ i : I, flatPullbackCoeff D sX hX sY hY f hbase r hflat hr m (α i) W
  by_cases hex : ∃ A, flatPullbackMult D sX hX sY hY f hbase r hflat hr A W ≠ 0
  · obtain ⟨A, hA⟩ := hex
    have hone : ∀ A', A' ≠ A →
        flatPullbackMult D sX hX sY hY f hbase r hflat hr A' W = 0 := fun A' hA' => by
      by_contra h
      exact hA' (eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr A' A W h hA)
    have hsingle : ∀ β : CycleGroup D sY m,
        flatPullbackCoeff D sX hX sY hY f hbase r hflat hr m β W =
          β.1 A * flatPullbackMult D sX hX sY hY f hbase r hflat hr A W := fun β =>
      finsum_eq_single _ A fun A' hA' => by rw [hone A' hA', mul_zero]
    rw [hsingle, finsum_congr fun i => hsingle (α i), locallyFiniteCycleSum_apply,
      finsum_mul]
  · push Not at hex
    have hzero : ∀ β : CycleGroup D sY m,
        flatPullbackCoeff D sX hX sY hY f hbase r hflat hr m β W = 0 := fun β =>
      finsum_eq_zero_of_forall_eq_zero fun A => by rw [hex A, mul_zero]
    rw [hzero, finsum_congr fun i => hzero (α i), finsum_zero]

end AlgebraicGeometry.Space.PrivateChern

end
