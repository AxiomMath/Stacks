module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InfiniteSumsRationalEquivalence

/-!
# The cap product with a first Chern class of a locally finite sum of cycles

In Situation 0EDT let `X/B` be good, let `ℒ` be invertible on `X` and let `α_i ∈ Z_{k+1}(X)` be
cycles supported on the members `T_i` of a locally finite collection of subsets of `|X|`. The
cap products `c₁(ℒ) ∩ α_i` of Stacks 0EQJ, for any component rule, are supported on the same
`T_i`, and

`c₁(ℒ) ∩ ∑ α_i = ∑ c₁(ℒ) ∩ α_i`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.firstChernCapCycleMap_locallyFiniteCycleSum`:
  `c₁(ℒ) ∩ ∑ α_i = ∑ c₁(ℒ) ∩ α_i`.

## References

* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) (chern : FirstChernComponentCycleRule D sX k)
    {I : Type v}

/-- Iterated `finsum`s commute when the nonzero terms lie in a finite product of sets. -/
private theorem finsum_comm_of_ne_zero_mem {A B : Type*} (f : A → B → ℤ) (s : Finset A)
    (t : Finset B) (h : ∀ a b, f a b ≠ 0 → a ∈ s ∧ b ∈ t) :
    ∑ᶠ a, ∑ᶠ b, f a b = ∑ᶠ b, ∑ᶠ a, f a b := by
  have hs : ∀ b, ∑ᶠ a, f a b = ∑ a ∈ s, f a b := fun b =>
    finsum_eq_sum_of_support_subset _ fun a ha => by simpa using (h a b ha).1
  have ht : ∀ a, ∑ᶠ b, f a b = ∑ b ∈ t, f a b := fun a =>
    finsum_eq_sum_of_support_subset _ fun b hb => by simpa using (h a b hb).2
  simp only [hs, ht]
  rw [finsum_eq_sum_of_support_subset (s := s), finsum_eq_sum_of_support_subset (s := t),
    Finset.sum_comm]
  · intro b hb
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    simpa using (h a b ha).2
  · intro a ha
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
    simpa using (h a b hb).1

/-- The cap product `c₁(ℒ) ∩ α` of a cycle supported on `T ⊆ |X|` is supported on `T`. -/
theorem subspacePointSet_subset_of_firstChernCapCycleMap_ne_zero
    (T : Set (points D.site D.base D.base_mem X)) (α : CycleGroup D sX (k + 1))
    (hαT : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : (firstChernCapCycleMap D sX hX k chern α).1 Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T := by
  obtain ⟨W, hW, hWZ⟩ := exists_ne_zero_of_firstChernCapCoeff_ne_zero D sX hX k chern α Z hZ
  exact (subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX k chern W Z
    hWZ).trans (hαT W hW)

/-- **The cap product commutes with locally finite sums**: `c₁(ℒ) ∩ ∑ α_i = ∑ c₁(ℒ) ∩ α_i`,
over the same locally finite collection of supports. -/
theorem firstChernCapCycleMap_locallyFiniteCycleSum
    (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)
    (α : I → CycleGroup D sX (k + 1))
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T i) :
    firstChernCapCycleMap D sX hX k chern (locallyFiniteCycleSum D sX (k + 1) T hT α hαT) =
      locallyFiniteCycleSum D sX k T hT (fun i => firstChernCapCycleMap D sX hX k chern (α i))
        (fun i => subspacePointSet_subset_of_firstChernCapCycleMap_ne_zero D sX hX k chern (T i)
          (α i) (hαT i)) := by
  classical
  refine Subtype.ext (funext fun Z => ?_)
  show firstChernCapCoeff D sX hX k chern (locallyFiniteCycleSum D sX (k + 1) T hT α hαT) Z =
    ∑ᶠ i : I, firstChernCapCoeff D sX hX k chern (α i) Z
  set ξ := pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
    (Z.genericPoint D.site D.base D.base_mem)
  have hξ : ξ ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := ⟨_, rfl⟩
  obtain ⟨V, hV, hVfin⟩ := hT ξ
  set F := {i : I | (T i ∩ V).Nonempty}
  have hF : F.Finite := hVfin
  set S := ⋃ i ∈ F, {W : IntegralClosedSubspace D.site D.base D.base_mem X | (α i).1 W ≠ 0 ∧
      ξ ∈ subspacePointSet D.site D.base D.base_mem X W.subspace}
  have hS : S.Finite := hF.biUnion fun i _ => by
    obtain ⟨Vi, hVi, hVifin⟩ := (α i).2.1 ξ
    refine hVifin.subset ?_
    rintro W ⟨hW, hξW⟩
    exact ⟨ξ, by simpa [hW] using hξW, mem_of_mem_nhds hVi⟩
  set g : I → IntegralClosedSubspace D.site D.base D.base_mem X → ℤ := fun i W =>
    (α i).1 W * (firstChernComponentCycle D sX hX k chern W).1 Z
  have hg : ∀ i W, g i W ≠ 0 → i ∈ F ∧ W ∈ S := by
    intro i W hgiW
    have hαW : (α i).1 W ≠ 0 := left_ne_zero_of_mul hgiW
    have hξW : ξ ∈ subspacePointSet D.site D.base D.base_mem X W.subspace :=
      subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX k chern W Z
        (right_ne_zero_of_mul hgiW) hξ
    have hiF : i ∈ F := ⟨ξ, hαT i W hαW hξW, mem_of_mem_nhds hV⟩
    exact ⟨hiF, Set.mem_biUnion hiF ⟨hαW, hξW⟩⟩
  calc firstChernCapCoeff D sX hX k chern (locallyFiniteCycleSum D sX (k + 1) T hT α hαT) Z
      = ∑ᶠ W, ∑ᶠ i, g i W := finsum_congr fun W => by
        simp only [g, locallyFiniteCycleSum_apply, finsum_mul]
    _ = ∑ᶠ i, ∑ᶠ W, g i W := finsum_comm_of_ne_zero_mem (fun W i => g i W) hS.toFinset
        hF.toFinset fun W i hi => by simpa using (hg i W hi).symm
    _ = ∑ᶠ i : I, firstChernCapCoeff D sX hX k chern (α i) Z := rfl

end AlgebraicGeometry.Space.PrivateChern

end
