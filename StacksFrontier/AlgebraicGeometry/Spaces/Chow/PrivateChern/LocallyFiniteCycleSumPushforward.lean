module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InfiniteSumsRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles

/-!
# Proper pushforward of a locally finite sum of cycles

In Situation 0EDT let `f : X ⟶ Y` be a quasi-compact morphism of good algebraic spaces and let
`α_i ∈ Z_k(X)` be cycles supported on the members `T_i` of a locally finite collection of closed
subsets of `|X|`. The pushforwards `f_*α_i` are supported on the closures of the images
`|f|(T_i)`, which form a locally finite collection by Stacks 0ENZ, and

`f_*(∑ α_i) = ∑ f_*α_i`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.properCyclePushforward_locallyFiniteCycleSum`:
  `f_*(∑ α_i) = ∑ f_*α_i`.

## References

* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
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
    {f : X ⟶ Y} (hfB : f ≫ sY = sX) (hf : IsQuasiCompact D.site D.base D.base_mem f)
    {I : Type v}

/-- If `α Z ≠ 0` with `Z ⊆ T`, the closure of the image of `Z` lies in the closure of `|f|(T)`. -/
private theorem subspacePointSet_subset_closure_image_of_closureImage_eq (k : ℤ)
    (T : Set (points D.site D.base D.base_mem X)) (α : CycleGroup D sX k)
    (hαT : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (hαZ : α.1 Z ≠ 0)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (him : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) f Z = Z') :
    subspacePointSet D.site D.base D.base_mem Y Z'.subspace ⊆
      closure (pointsMap D.site D.base D.base_mem X f '' T) := by
  rw [← him, ← closure_image_cycleSupportFamily D sY hY f α.1 hαZ,
    cycleSupportFamily_of_ne_zero D α.1 hαZ]
  exact closure_mono (Set.image_mono (hαT Z hαZ))

/-- The pushforward `f_*α` of a cycle supported on `T ⊆ |X|` is supported on the closure of
`|f|(T)`. -/
theorem subspacePointSet_subset_of_properCyclePushforward_ne_zero (k : ℤ)
    (T : Set (points D.site D.base D.base_mem X)) (α : CycleGroup D sX k)
    (hαT : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hZ' : (properCyclePushforward D sX hX sY hY hfB hf k α).1 Z' ≠ 0) :
    subspacePointSet D.site D.base D.base_mem Y Z'.subspace ⊆
      closure (pointsMap D.site D.base D.base_mem X f '' T) := by
  obtain ⟨Z, hZne, hZim, -⟩ := exists_of_properPushforwardCoeff_ne_zero D sX hX sY hY f α.1 hZ'
  exact subspacePointSet_subset_closure_image_of_closureImage_eq D sX sY hY k T α hαT Z hZne Z'
    hZim

/-- **Proper pushforward commutes with locally finite sums**: `f_*(∑ α_i) = ∑ f_*α_i`, the sum
on the right being over the locally finite collection of the closures of the images
`|f|(T_i)` (Stacks 0ENZ). -/
theorem properCyclePushforward_locallyFiniteCycleSum (k : ℤ)
    (T : I → Set (points D.site D.base D.base_mem X)) (hTc : ∀ i, IsClosed (T i))
    (hT : LocallyFinite T) (α : I → CycleGroup D sX k)
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T i) :
    properCyclePushforward D sX hX sY hY hfB hf k (locallyFiniteCycleSum D sX k T hT α hαT) =
      locallyFiniteCycleSum D sY k
        (fun i => closure (pointsMap D.site D.base D.base_mem X f '' T i))
        (locallyFinite_closure_image_pointsMap D sX hX sY hY hfB hf T hTc hT).1
        (fun i => properCyclePushforward D sX hX sY hY hfB hf k (α i))
        (fun i => subspacePointSet_subset_of_properCyclePushforward_ne_zero D sX hX sY hY hfB hf k
          (T i) (α i) (hαT i)) := by
  classical
  refine Subtype.ext (funext fun Z' => ?_)
  show properCyclePushforwardCoeff D sX hX sY hY f
      (locallyFiniteCycleSumCoeff D sX k α) Z' =
    ∑ᶠ i : I, properCyclePushforwardCoeff D sX hX sY hY f (α i).1 Z'
  set ξ := Z'.ambientGenericPoint D.site D.base D.base_mem
  obtain ⟨V, hV, hVfin⟩ :=
    (locallyFinite_closure_image_pointsMap D sX hX sY hY hfB hf T hTc hT).1 ξ
  set F := {i : I | ((closure (pointsMap D.site D.base D.base_mem X f '' T i)) ∩ V).Nonempty}
  have hF : F.Finite := hVfin
  set S := ⋃ i ∈ F, {Z : IntegralClosedSubspace D.site D.base D.base_mem X | (α i).1 Z ≠ 0 ∧
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f Z = Z'}
  have hS : S.Finite := hF.biUnion fun i _ =>
    finite_properCycleFibre D sX hX sY hY hfB hf (α i).1 (α i).2.1 Z'
  set g : I → IntegralClosedSubspace D.site D.base D.base_mem X → ℤ := fun i Z =>
    (α i).1 Z * properCycleMult D sX hX sY hY f Z Z'
  have hg : ∀ i Z, g i Z ≠ 0 → i ∈ F ∧ Z ∈ S := by
    intro i Z hgiZ
    have hαZ : (α i).1 Z ≠ 0 := left_ne_zero_of_mul hgiZ
    have him := ((properCycleMult_ne_zero_iff D sX hX sY hY f Z Z').1
      (right_ne_zero_of_mul hgiZ)).1
    have hiF : i ∈ F := by
      refine ⟨ξ, ?_, mem_of_mem_nhds hV⟩
      exact subspacePointSet_subset_closure_image_of_closureImage_eq D sX sY hY k (T i) (α i)
        (hαT i) Z hαZ Z' him ⟨_, rfl⟩
    exact ⟨hiF, Set.mem_biUnion hiF ⟨hαZ, him⟩⟩
  have hinner : ∀ Z, (Function.support fun i => g i Z) ⊆ hF.toFinset := fun Z i hi => by
    simpa using (hg i Z hi).1
  have hinner' : ∀ i, (Function.support fun Z => g i Z) ⊆ hS.toFinset := fun i Z hZ => by
    simpa using (hg i Z hZ).2
  calc properCyclePushforwardCoeff D sX hX sY hY f (locallyFiniteCycleSumCoeff D sX k α) Z'
      = ∑ᶠ Z, ∑ᶠ i, g i Z := finsum_congr fun Z => by
        simp only [g, locallyFiniteCycleSumCoeff, finsum_mul]
    _ = ∑ Z ∈ hS.toFinset, ∑ i ∈ hF.toFinset, g i Z := by
        rw [finsum_eq_sum_of_support_subset _ (s := hS.toFinset) ?_]
        · exact Finset.sum_congr rfl fun Z _ => finsum_eq_sum_of_support_subset _ (hinner Z)
        · intro Z hZ
          obtain ⟨i, hi⟩ : ∃ i, g i Z ≠ 0 := by
            by_contra h
            push Not at h
            exact hZ (finsum_eq_zero_of_forall_eq_zero h)
          simpa using (hg i Z hi).2
    _ = ∑ i ∈ hF.toFinset, ∑ Z ∈ hS.toFinset, g i Z := Finset.sum_comm
    _ = ∑ᶠ i, ∑ᶠ Z, g i Z := by
        rw [finsum_eq_sum_of_support_subset _ (s := hF.toFinset) ?_]
        · exact Finset.sum_congr rfl fun i _ =>
            (finsum_eq_sum_of_support_subset _ (hinner' i)).symm
        · intro i hi
          obtain ⟨Z, hZ⟩ : ∃ Z, g i Z ≠ 0 := by
            by_contra h
            push Not at h
            exact hi (finsum_eq_zero_of_forall_eq_zero h)
          simpa using (hg i Z hZ).1
    _ = ∑ᶠ i : I, properCyclePushforwardCoeff D sX hX sY hY f (α i).1 Z' := rfl

end AlgebraicGeometry.Space.PrivateChern

end
