module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatInverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackPrincipalDivisorComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.RationalFunctionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.RatioComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.WeilDivisorOfInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackWeaklyAssociated

/-!
# The irreducible components of the source of a flat morphism to an integral space

In Situation 0EDT let `X/B` and `Y/B` be good, let `Y` be integral with `n = dim_δ(Y)` and let
`f : X ⟶ Y` be flat of relative dimension `r`. This file records the facts about the irreducible
components `X_i` of `X` which Stacks 0EQQ uses: every component has δ-dimension `n + r` and
dominates `Y` (Stacks 0EP5), so the pullback of a meromorphic section along `f|_{X_i}` is defined
(Stacks 0EN9); and an integral closed subspace of δ-dimension `n + r - 1` is a prime divisor of
`X`, its generic point having codimension one in `|X|`.

## Main results

* `AlgebraicGeometry.Space.deltaDimension_eq_add_of_mem_irreducibleComponents_of_isFlat`
* `AlgebraicGeometry.Space.pointsMap_ambientGenericPoint_eq_genericPoint_of_isFlat`
* `AlgebraicGeometry.Space.pullbacksMeromorphicSections_ι_comp_of_isFlat`
* `AlgebraicGeometry.Space.codimension_integralClosedSubspaceSupport_eq_one_of_isFlat`

## References

* [Stacks Project, Tag 0EP5](https://stacks.math.columbia.edu/tag/0EP5)
* [Stacks Project, Tag 0EN9](https://stacks.math.columbia.edu/tag/0EN9)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y) {n : ℤ}
    (hn : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))

/-- The integral closed subspace of `Y` carried by all of `|Y|`. -/
abbrev topIntegralClosedSubspace : IntegralClosedSubspace D.site D.base D.base_mem Y :=
  haveI : IrreducibleSpace (points D.site D.base D.base_mem Y) := hintY.2.2
  integralClosedSubspaceOfPoints D.site D.base D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY)
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩

include hn in
/-- The δ-dimension of the integral closed subspace carried by all of `|Y|` is `n`. -/
theorem deltaDimension_topIntegralClosedSubspace :
    deltaDimension D sY (topIntegralClosedSubspace D sY hY hintY) = n := by
  rw [deltaDimension_eq_of_isGenericPoint D sY hY.1 _ (genericPoint D.site D.base D.base_mem hY.1
    hintY), deltaValue_genericPoint_eq_of_deltaDimensionClosed D sY hY hintY hn]
  rw [subspacePointSet_integralClosedSubspaceOfPoints]
  exact isGenericPoint_genericPoint D.site D.base D.base_mem hY.1 hintY

/-- An irreducible component of `|X|` is a component of the inverse image of all of `|Y|`. -/
theorem exists_preimageComponent_eq_of_mem_irreducibleComponents
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : subspacePointSet D.site D.base D.base_mem X W.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X)) :
    ∃ C : irreducibleComponents
        ((topIntegralClosedSubspace D sY hY hintY).preimagePointSet D.site D.base D.base_mem f),
      (topIntegralClosedSubspace D sY hY hintY).preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C = W := by
  set T := (topIntegralClosedSubspace D sY hY hintY).preimagePointSet D.site D.base D.base_mem f
    with hT
  have hcT : W.ambientGenericPoint D.site D.base D.base_mem ∈ T := by
    change pointsMap D.site D.base D.base_mem X f _ ∈ subspacePointSet D.site D.base D.base_mem Y _
    rw [subspacePointSet_integralClosedSubspaceOfPoints]
    trivial
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({⟨_, hcT⟩} : Set T)) isIrreducible_singleton.closure
  refine ⟨⟨C, hC⟩, ?_⟩
  set K := (topIntegralClosedSubspace D sY hY hintY).preimageComponent D.site D.base D.base_mem f
    hX.1 (D.isDecentSpace_of_isGood sX hX) hY.1 ⟨C, hC⟩ with hK
  have hKpts := (topIntegralClosedSubspace D sY hY hintY).subspacePointSet_preimageComponent
    D.site D.base D.base_mem f hX.1 (D.isDecentSpace_of_isGood sX hX) hY.1 ⟨C, hC⟩
  have hWK : subspacePointSet D.site D.base D.base_mem X W.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X K.subspace := by
    rw [← (W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1).def]
    refine closure_minimal ?_ (isClosed_range_pointsMap_integralClosedSubspace D.site D.base
      D.base_mem hX.1 K)
    rw [Set.singleton_subset_iff, hK, hKpts]
    exact ⟨⟨_, hcT⟩, hsub (subset_closure rfl), rfl⟩
  have heq : subspacePointSet D.site D.base D.base_mem X K.subspace =
      subspacePointSet D.site D.base D.base_mem X W.subspace :=
    (hW.2 (isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem K)
      hWK).antisymm hWK
  exact injective_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
    (IrreducibleCloseds.ext heq)

include hX hbase hflat hr hintY hn in
/-- **Stacks 0EP5 at the irreducible components of the source.** Every irreducible component of
`|X|` has δ-dimension `n + r`. -/
theorem deltaDimension_eq_add_of_mem_irreducibleComponents_of_isFlat
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : subspacePointSet D.site D.base D.base_mem X W.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X)) :
    deltaDimension D sX W = n + r := by
  obtain ⟨C, hC⟩ := exists_preimageComponent_eq_of_mem_irreducibleComponents D sX hX sY hY f
    hintY W hW
  rw [← hC, IntegralClosedSubspace.deltaDimension_preimageComponent_of_isFlat D sX hX sY hY
    hbase r hflat hr, deltaDimension_topIntegralClosedSubspace D sY hY hintY hn]

include sX hX hflat in
/-- **Stacks 0EP5, dominance.** The generic point of an irreducible component of `|X|` maps to
the generic point of `Y`. -/
theorem pointsMap_ambientGenericPoint_eq_genericPoint_of_isFlat
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : subspacePointSet D.site D.base D.base_mem X W.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X)) :
    pointsMap D.site D.base D.base_mem X f (W.ambientGenericPoint D.site D.base D.base_mem) =
      genericPoint D.site D.base D.base_mem hY.1 hintY := by
  obtain ⟨C, hC⟩ := exists_preimageComponent_eq_of_mem_irreducibleComponents D sX hX sY hY f
    hintY W hW
  have hdom := IntegralClosedSubspace.closure_image_subspacePointSet_preimageComponent_of_isFlat
    D sX hX sY hY hflat (topIntegralClosedSubspace D sY hY hintY) C
  rw [hC, subspacePointSet_integralClosedSubspaceOfPoints] at hdom
  have hdom' : closure (pointsMap D.site D.base D.base_mem X f ''
      subspacePointSet D.site D.base D.base_mem X W.subspace) = Set.univ := hdom
  have hgen : IsGenericPoint (pointsMap D.site D.base D.base_mem X f
      (W.ambientGenericPoint D.site D.base D.base_mem)) (Set.univ : Set (points D.site D.base
        D.base_mem Y)) := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hdom']
    refine closure_minimal ?_ isClosed_closure
    rw [← (W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1).def]
    exact (image_closure_subset_closure_image
      (continuous_pointsMap D.site D.base D.base_mem f)).trans (by rw [Set.image_singleton])
  have := t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY)
  exact hgen.eq (isGenericPoint_genericPoint D.site D.base D.base_mem hY.1 hintY)

include sX hX hY hflat hintY in
/-- **Stacks 0EN9 along the restriction of `f` to an irreducible component.** Meromorphic
sections pull back along `f|_W : W ⟶ Y` for an irreducible component `W` of `X`: a weakly
associated point of the integral space `W` is its generic point, which `f` carries to the generic
point of `Y`, a point of codimension zero. -/
theorem pullbacksMeromorphicSections_ι_comp_of_isFlat
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : subspacePointSet D.site D.base D.base_mem X W.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X)) :
    PullbacksMeromorphicSections D.site D.base D.base_mem (W.subspace.ι ≫ f) := by
  refine pullbacksMeromorphicSections_of_mapsTo_codimensionZero D.site D.base D.base_mem
    (X := ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩) (Y := ⟨Y, hY.1⟩) (W.subspace.ι ≫ f)
    fun x hx => ?_
  have hx0 := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    D.site D.base D.base_mem W.isClosedSubspace.1 W.isIntegralSpace x hx
  have hxgen := mem_genericPoints_of_localRingDimension_eq_zero D.site D.base D.base_mem
    W.isClosedSubspace.1 W.isIntegralSpace.isDecentSpace hx0
  have := W.quasiSober_points D.site D.base D.base_mem
  have := W.irreducibleSpace_points D.site D.base D.base_mem
  have := W.t0Space_points D.site D.base D.base_mem
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hxgen
  have hxW : x = W.genericPoint D.site D.base D.base_mem := hxgen
  rw [hxW, pointsMap_comp_apply]
  change localRingDimension D.site D.base D.base_mem
    (pointsMap D.site D.base D.base_mem X f (W.ambientGenericPoint D.site D.base D.base_mem)) = 0
  rw [pointsMap_ambientGenericPoint_eq_genericPoint_of_isFlat D sX hX sY hY f hflat hintY W hW]
  refine localRingDimension_eq_zero_of_mem_genericPoints D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) ?_
  have : QuasiSober (points D.site D.base D.base_mem Y) :=
    quasiSober_points_of_isDecentSpace D.site D.base D.base_mem hY.1 hintY.2.1
  have : IrreducibleSpace (points D.site D.base D.base_mem Y) := hintY.2.2
  have := t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1 hintY.2.1
  rw [genericPoints_eq_singleton]
  exact rfl

include sY hY hbase hflat hr hintY hn in
/-- **An integral closed subspace of δ-dimension `n + r - 1` has codimension one in `|X|`.** The
δ-function of `X` is a dimension function (Stacks 0EDN) taking the value `n + r` at the generic
point of every irreducible component (Stacks 0EP5) and at most `n + r` everywhere. -/
theorem codimension_integralClosedSubspaceSupport_eq_one_of_isFlat
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : deltaDimension D sX Z = n + r - 1) :
    codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1 := by
  obtain ⟨P, hP, -⟩ := exists_primeDivisor_toIntegralClosedSubspace_eq_of_isFlat D sX hX sY hY f
    hbase r hr hflat hintY hn Z hZ
  rw [← hP]
  exact P.codimension_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1

end AlgebraicGeometry.Space

end
