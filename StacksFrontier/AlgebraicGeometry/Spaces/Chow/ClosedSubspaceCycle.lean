module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative

/-!
# The cycle of a closed subspace

In Situation 0EDT let `X/B` be good and let `Y ⊆ X` be a closed subspace with `dim_δ(Y) ≤ k`.
The *`k`-cycle associated to `Y`* is `[Y]_k = ∑ m_{Z, Y} [Z]`, the sum running over the
irreducible components `Z` of `Y` of δ-dimension `k`, with `m_{Z, Y}` the multiplicity of `Z` in
`Y`. As a coefficient family on the integral closed subspaces of `X` it is
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace`, which assigns to `Z` the multiplicity of `Z`
in `Y` when `Z` has δ-dimension `k`, and `0` otherwise, read at the canonical geometric point
`AlgebraicGeometry.Space.canonicalGeometricPoint`.

## Main definitions

* `AlgebraicGeometry.Space.closedSubspaceCycle`: the `k`-cycle `[Y]_k` of a closed subspace
  `Y ⊆ X` whose δ-dimension is at most `k`.

## Main results

* `AlgebraicGeometry.Space.subspacePointSet_subset_of_closedSubspaceCycle_ne_zero`: an
  integral closed subspace with nonzero coefficient in `[Y]_k` is contained in `|Y|`.
* `AlgebraicGeometry.Space.exists_irreducibleComponents_of_cycleCoeffOfClosedSubspace_ne_zero`:
  under the bound `dim_δ(Y) ≤ k`, such a subspace has point set an irreducible component of
  `|Y|`.
* `AlgebraicGeometry.Space.locallyFinite_cycleCoeffOfClosedSubspace` and
  `AlgebraicGeometry.Space.closedSubspaceCycleCoeff_mem_cyclesOfDimension`: the coefficient
  family is locally finite, hence a `k`-cycle.
* `AlgebraicGeometry.Space.closedSubspaceCycle_apply_closedSubspaceComponentImage`: the
  coefficient at the image of an integral closed subspace of `Y` is the multiplicity there.
* `AlgebraicGeometry.Space.closedSubspaceCycle_apply_eq_zero_of_forall_ne`: the coefficient at a
  subspace not carried by `Y` vanishes.

## References

* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The point set of a closed subspace of an algebraic space is closed. -/
theorem isClosed_subspacePointSet_of_isClosedSubspace
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) :
    IsClosed (subspacePointSet D.site D.base D.base_mem X Y) :=
  isClosed_range_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX Y.ι hY.2

/-- The δ-dimension of a closed subspace is the δ-dimension of its point set. -/
theorem deltaDimensionSubspace_eq_deltaDimensionClosed (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y) :
    deltaDimensionSubspace D sX hX Y hY =
      deltaDimensionClosed D sX hX (subspacePointSet D.site D.base D.base_mem X Y)
        (isClosed_subspacePointSet_of_isClosedSubspace D hX.1 Y hY) :=
  rfl

/-- An integral closed subspace with a nonzero coefficient in `[Y]_k` has δ-dimension `k`. -/
private theorem deltaDimension_eq_of_coeffOfClosedSubspace_ne_zero (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : cycleCoeffOfClosedSubspace D sX hX Y hY k γ Z ≠ 0) : deltaDimension D sX Z = k := by
  by_contra h
  exact hZ (by rw [cycleCoeffOfClosedSubspace, ite_eq_right h])

/-- An integral closed subspace with a nonzero coefficient in `[Y]_k` has its point set
contained in `|Y|`. -/
private theorem subspacePointSet_subset_of_coeffOfClosedSubspace_ne_zero (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : cycleCoeffOfClosedSubspace D sX hX Y hY k γ Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X Y := by
  by_cases hex : ∃ W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
      closedSubspaceComponentImage D sX hX Y hY W = Z
  · obtain ⟨W, rfl⟩ := hex
    rw [IntegralClosedSubspace.subspacePointSet_pushforward]
    exact Set.image_subset_range _ _
  · exact absurd (cycleCoeffOfClosedSubspace_eq_zero D sX hX Y hY k γ Z
      fun W hW ↦ hex ⟨W, hW⟩) hZ

/-- Let `Y ⊆ X` be a closed subspace of a good algebraic space `X/B` with `dim_δ(Y) ≤ k`. An
integral closed subspace whose coefficient in `[Y]_k` is nonzero has for its point set an
irreducible component of `|Y|`. -/
theorem exists_irreducibleComponents_of_cycleCoeffOfClosedSubspace_ne_zero (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : cycleCoeffOfClosedSubspace D sX hX Y hY k γ Z ≠ 0) :
    ∃ C : irreducibleComponents (subspacePointSet D.site D.base D.base_mem X Y),
      subspacePointSet D.site D.base D.base_mem X Z.subspace =
        Subtype.val '' (C : Set (subspacePointSet D.site D.base D.base_mem X Y)) := by
  have hTcl : IsClosed (subspacePointSet D.site D.base D.base_mem X Y) :=
    isClosed_subspacePointSet_of_isClosedSubspace D hX.1 Y hY
  have hmem : Z.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X Y :=
    subspacePointSet_subset_of_coeffOfClosedSubspace_ne_zero D sX hX Y hY k γ Z hZ ⟨_, rfl⟩
  obtain ⟨C, hC⟩ := isGenericPoint_of_deltaDimensionClosed_le D sX hX
    (subspacePointSet D.site D.base D.base_mem X Y) hTcl
    (Z.ambientGenericPoint D.site D.base D.base_mem) hmem k hdim
    (deltaDimension_eq_of_coeffOfClosedSubspace_ne_zero D sX hX Y hY k γ Z hZ)
  refine ⟨C, ?_⟩
  have himg := hTcl.isClosedEmbedding_subtypeVal.closure_image_eq
    ({⟨Z.ambientGenericPoint D.site D.base D.base_mem, hmem⟩} :
      Set (subspacePointSet D.site D.base D.base_mem X Y))
  rw [Set.image_singleton, hC] at himg
  exact (Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1).symm.trans himg

/-- The point sets of the integral closed subspaces with nonzero coefficient in `[Y]_k` form a
locally finite collection, when the closed subspace `Y` has δ-dimension at most `k`. -/
theorem locallyFinite_cycleCoeffOfClosedSubspace (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt)) :
    LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if cycleCoeffOfClosedSubspace D sX hX Y hY k γ Z = 0 then
        (∅ : Set (points D.site D.base D.base_mem X))
      else subspacePointSet D.site D.base D.base_mem X Z.subspace := by
  have hN := isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem hX.1
    D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian
  have hTcl : IsClosed (subspacePointSet D.site D.base D.base_mem X Y) :=
    isClosed_subspacePointSet_of_isClosedSubspace D hX.1 Y hY
  intro p
  obtain ⟨t, htp, hfin⟩ := locallyFinite_irreducibleComponents_of_isClosed D.site D.base
    D.base_mem X hX.1 hN (subspacePointSet D.site D.base D.base_mem X Y) hTcl p
  refine ⟨t, htp, (hfin.image (closedSetComponent D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) (subspacePointSet D.site D.base D.base_mem X Y)
    hTcl)).subset ?_⟩
  rintro Z ⟨q, hq, hqt⟩
  rw [Set.mem_ite_empty_left] at hq
  obtain ⟨C, hC⟩ := exists_irreducibleComponents_of_cycleCoeffOfClosedSubspace_ne_zero D sX
    hX Y hY k γ hdim Z hq.1
  exact ⟨C, ⟨q, hC.subset hq.2, hqt⟩,
    eq_closedSetComponent D.site D.base D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX)
      (subspacePointSet D.site D.base D.base_mem X Y) hTcl C Z hC⟩

/-- The coefficient family of `[Y]_k` is a `k`-cycle when `Y` has δ-dimension at most `k`. -/
theorem closedSubspaceCycleCoeff_mem_cyclesOfDimension (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt)) :
    cycleCoeffOfClosedSubspace D sX hX Y hY k γ ∈ cyclesOfDimension D sX k := by
  exact ⟨locallyFinite_cycleCoeffOfClosedSubspace D sX hX Y hY k γ hdim,
    deltaDimension_eq_of_coeffOfClosedSubspace_ne_zero D sX hX Y hY k γ⟩

/-- In Situation 0EDT let `X/B` be good, let `Y ⊆ X` be a closed subspace and assume
`dim_δ(Y) ≤ k`. The *`k`-cycle associated to `Y`* is `[Y]_k = ∑ m_{Z, Y} [Z]`, the sum over the
irreducible components `Z` of `Y` of δ-dimension `k`, with `m_{Z, Y}` the multiplicity of `Z` in
`Y`; as an element of `Z_k(X)` it is the coefficient family
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace` at the canonical geometric points. -/
@[stacks 0EE9 "part (2): the k-cycle [Y]_k of a closed subspace; the multiplicity at each point
  is independent of the choice of geometric representative by Lemma 0EE1
  (closedSubspaceMultiplicity_eq_toNat_geometricLength) and positive by Lemma 0EE4
  (closedSubspaceMultiplicity_pos)"]
def closedSubspaceCycle (sX : X ⟶ D.space) (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt)) : CycleGroup D sX k :=
  ⟨cycleCoeffOfClosedSubspace D sX hX Y hY k
      (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor),
    closedSubspaceCycleCoeff_mem_cyclesOfDimension D sX hX Y hY k
      (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor) hdim⟩

/-- The coefficient of an integral closed subspace in `[Y]_k` is the value of the coefficient
family `cycleCoeffOfClosedSubspace`, read at the canonical geometric representative of each point
of `|Y|`. -/
@[simp]
theorem closedSubspaceCycle_coe (sX : X ⟶ D.space) (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt)) :
    (closedSubspaceCycle D sX hX Y hY k hdim).1 =
      cycleCoeffOfClosedSubspace D sX hX Y hY k
        (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor) :=
  rfl

/-- The coefficient of `[Y]_k` at the image of an integral closed subspace `W ⊆ Y` is the
multiplicity of that image in `Y`, when the image has δ-dimension `k`. -/
theorem closedSubspaceCycle_apply_closedSubspaceComponentImage (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt))
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    (closedSubspaceCycle D sX hX Y hY k hdim).1
        (closedSubspaceComponentImage D sX hX Y hY W) =
      if deltaDimension D sX (closedSubspaceComponentImage D sX hX Y hY W) = k then
        ((geometricLength D.site D.base D.base_mem ⟨Y.toFunctor, hY.1⟩
          (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor
            (W.ambientGenericPoint D.site D.base D.base_mem))
          (SheafOfModules.unit _)).toNat : ℤ)
      else 0 :=
  cycleCoeffOfClosedSubspace_closedSubspaceComponentImage D sX hX Y hY k
    (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor) W

/-- The coefficient of `[Y]_k` at an integral closed subspace of `X` which is not the image of
one of `Y` vanishes. -/
theorem closedSubspaceCycle_apply_eq_zero_of_forall_ne (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
      closedSubspaceComponentImage D sX hX Y hY W ≠ Z) :
    (closedSubspaceCycle D sX hX Y hY k hdim).1 Z = 0 :=
  cycleCoeffOfClosedSubspace_eq_zero D sX hX Y hY k
    (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor) Z hZ

/-- The point set of an integral closed subspace with a nonzero coefficient in `[Y]_k` is
contained in `|Y|`. -/
theorem subspacePointSet_subset_of_closedSubspaceCycle_ne_zero (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : (closedSubspaceCycle D sX hX Y hY k hdim).1 Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X Y :=
  subspacePointSet_subset_of_coeffOfClosedSubspace_ne_zero D sX hX Y hY k
    (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor) Z hZ

end AlgebraicGeometry.Space

end
