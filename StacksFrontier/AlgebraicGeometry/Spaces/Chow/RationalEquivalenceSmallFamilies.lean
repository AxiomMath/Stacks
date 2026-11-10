module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowLocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceLocallyFiniteSums
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus

/-!
# Witnessing families of rational equivalences are small

In Situation 0EDT let `X/B` be good. A `k`-cycle on `X` is rationally equivalent to zero,
Stacks 0EQ6, when it is a sum `∑ (i_j)_* div(f_j)` over a locally finite family `{W_j}_{j ∈ J}`
of integral closed subspaces. The index type `J` lives in an arbitrary universe; this file shows
that the choice of universe does not matter once it contains the universe of the site.

It also shows that if `β` is rationally equivalent to zero on a closed subspace `Y ⊆ X`, then
`i_*β` is rationally equivalent to zero within `|Y|`, in the sense of
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin`.

## Main results

* `AlgebraicGeometry.Space.small_of_locallyFinite_subspacePointSet`: a locally finite family of
  integral closed subspaces is indexed by a small type.
* `AlgebraicGeometry.Space.IsRationallyEquivalentToZero.down`: rational equivalence to zero with
  witnesses indexed in any universe implies it with witnesses indexed in the universe of the
  site.
* `AlgebraicGeometry.Space.IsCycleFamilySumWithin.down`: the same for locally finite sums of an
  arbitrary prescribed class of cycles within a set, such as the canonical principal divisors.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithin_cycleGroupClosedPushforward`: the
  pushforward of a cycle rationally equivalent to zero on a closed subspace is rationally
  equivalent to zero within that subspace.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Small

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The index type of a locally finite family of integral closed subspaces of an algebraic space
is small. -/
theorem small_of_locallyFinite_subspacePointSet (hX : IsAlgebraicSpace B S hS X) {J : Type w}
    (W : J → IntegralClosedSubspace B S hS X)
    (hW : LocallyFinite fun j => subspacePointSet B S hS X (W j).subspace) : Small.{u} J := by
  have : Small.{u} (points B S hS X) := small_points B S hS hX
  set g : J → points B S hS X := fun j => (W j).ambientGenericPoint B S hS
  have hfin : ∀ x, Finite {j // g j = x} := by
    intro x
    obtain ⟨V, hV, hVfin⟩ := hW x
    refine (hVfin.subset fun j (hj : g j = x) => ?_).to_subtype
    subst hj
    exact ⟨_, ⟨_, rfl⟩, mem_of_mem_nhds hV⟩
  exact small_of_injective (Equiv.sigmaFiberEquiv g).symm.injective

end Small

section Lower

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ}

/-- Reindexing a locally finite family of cycles along an equivalence does not change its sum. -/
private theorem cycleFamilySum_comp_equiv {J J' : Type*}
    {W : J → IntegralClosedSubspace D.site D.base D.base_mem X} (e : J' ≃ J)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k) :
    cycleFamilySum D sX hX (fun i => W (e i)) (hWfin.comp_injective e.injective) k
      (fun i => c (e i)) = cycleFamilySum D sX hX W hWfin k c := by
  refine Subtype.ext (funext fun Z => ?_)
  rw [cycleFamilySum_apply, cycleFamilySum_apply]
  exact finsum_comp_equiv e (f := fun j =>
    (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z)

/-- A cycle rationally equivalent to zero through a family indexed in any universe is rationally
equivalent to zero through one indexed in the universe of the site. -/
theorem IsRationallyEquivalentToZero.down {α : CycleGroup D sX k}
    (h : IsRationallyEquivalentToZero.{w} D sX hX k α) :
    IsRationallyEquivalentToZero.{u} D sX hX k α := by
  obtain ⟨J, W, hWfin, c, hdim, hprin, hα⟩ := h
  have := small_of_locallyFinite_subspacePointSet D.site D.base D.base_mem hX.1 W hWfin
  set e := equivShrink.{u} J
  refine ⟨Shrink.{u} J, fun i => W (e.symm i), hWfin.comp_injective e.symm.injective,
    fun i => c (e.symm i), fun i => hdim _, fun i => hprin _, ?_⟩
  exact hα.trans (cycleFamilySum_comp_equiv D e.symm _ _).symm

/-- Membership in the subgroup of cycles rationally equivalent to zero does not depend on the
universe of the witnesses, once that universe contains the universe of the site. -/
theorem mem_rationalEquivalences_of_mem {α : CycleGroup D sX k}
    (h : α ∈ rationalEquivalences.{w} D sX hX k) : α ∈ rationalEquivalences.{u} D sX hX k :=
  IsRationallyEquivalentToZero.down D h

/-- A cycle which is a locally finite sum of members of a prescribed class of cycles within a set,
through a family indexed in any universe, is one through a family indexed in the universe of the
site. -/
theorem IsCycleFamilySumWithin.down
    {P : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      Set (CycleGroup D (W.subspace.ι ≫ sX) k)}
    {α : CycleGroup D sX k} {T : Set (points D.site D.base D.base_mem X)}
    (h : IsCycleFamilySumWithin.{u, w} D sX hX k P α T) :
    IsCycleFamilySumWithin.{u, u} D sX hX k P α T := by
  obtain ⟨J, W, hWfin, c, hsub, hP, hα⟩ := h
  have := small_of_locallyFinite_subspacePointSet D.site D.base D.base_mem hX.1 W hWfin
  set e := equivShrink.{u} J
  refine ⟨Shrink.{u} J, fun i => W (e.symm i), hWfin.comp_injective e.symm.injective,
    fun i => c (e.symm i), fun i => hsub _, fun i => hP _, ?_⟩
  exact hα.trans (cycleFamilySum_comp_equiv D e.symm _ _).symm

end Lower

section ClosedPushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)

include hY in
/-- If `β ∈ Z_k(Y)` is rationally equivalent to zero on a closed subspace `Y ⊆ X`, then
`i_*β ∈ Z_k(X)` is rationally equivalent to zero within `|Y|`. -/
theorem isRationallyEquivalentToZeroWithin_cycleGroupClosedPushforward (k : ℤ)
    {β : CycleGroup D (Y.ι ≫ sX) k}
    (hβ : IsRationallyEquivalentToZero.{v} D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) k β) :
    IsRationallyEquivalentToZeroWithin.{v} D sX hX k
      (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl k β)
      (subspacePointSet D.site D.base D.base_mem X Y) := by
  classical
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  obtain ⟨J, W, hWfin, c, hdim, hprin, rfl⟩ := hβ
  have himm : IsImmersion D.site D.base D.base_mem Y.ι :=
    isImmersion_of_isClosedImmersion D.site D.base D.base_mem hY.2
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
    hY.2
  choose m hm using fun n => IntegralClosedSubspace.exists_hom_closureImage D.site D.base
    D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) Y.ι (W n)
  have hmopen : ∀ n, IsOpenImmersion D.site D.base D.base_mem (m n) := fun n =>
    have := isIso_of_comp_ι_eq_of_subspacePointSet D sX hX Y hY (W n) _
      (subspacePointSet_closureSubspace_ι D sX hX Y hY (W n)) (m n) (hm n)
    isOpenImmersion_of_isIso D.site D.base D.base_mem (m n)
  choose c' hprin' hcc using fun n =>
    exists_isPrincipalDivisorCycle_closureImage D sX hX (Y.ι ≫ sX) hYgood himm rfl k (W n) (c n)
      (m n) (hmopen n) (hdim n) (hprin n)
  have hpts := fun n => subspacePointSet_closureSubspace_ι D sX hX Y hY (W n)
  have hW'fin : LocallyFinite fun n => subspacePointSet D.site D.base D.base_mem X
      (closureSubspace D sX hX Y.ι (W n)).subspace :=
    locallyFinite_of_isClosedEmbedding_extend hemb (e := id)
      (fun w hw => absurd rfl (hw w)) (fun n => (hpts n).subset) hWfin
  have hdim' : ∀ n, deltaDimension D sX (closureSubspace D sX hX Y.ι (W n)) = k + 1 := by
    intro n
    rw [IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) himm (W n)]
    exact hdim n
  refine ⟨J, fun n => closureSubspace D sX hX Y.ι (W n), hW'fin, c', fun n => ?_, hdim', hprin',
    ?_⟩
  · rw [hpts n]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  refine Subtype.ext (funext fun T => ?_)
  rw [cycleFamilySum_apply]
  have hterm := fun n => congrArg (fun e : CycleGroup D sX k => e.1 T)
    (cycleGroupClosedPushforward_integralClosedSubspacePushforward D sX hX Y hY k (W n) (hm n)
      (c n) (c' n) (hcc n))
  rw [← finsum_congr hterm]
  change cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
      (cycleFamilySum D (Y.ι ≫ sX) hYgood W hWfin k c).1 T = _
  by_cases hT : ∃ T0, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 T0 = T
  · obtain ⟨T0, rfl⟩ := hT
    rw [cycleClosedPushforward_apply_pushforward, cycleFamilySum_apply]
    refine finsum_congr fun n => ?_
    change _ = cycleClosedPushforward D hX.1 hY.1 _ hY.2 _ _
    rw [cycleClosedPushforward_apply_pushforward]
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 _ T
      fun T0 hT0 => hT ⟨T0, hT0⟩]
    exact (finsum_eq_zero_of_forall_eq_zero fun n =>
      cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 _ T
        fun T0 hT0 => hT ⟨T0, hT0⟩).symm

end ClosedPushforward

end AlgebraicGeometry.Space

end
