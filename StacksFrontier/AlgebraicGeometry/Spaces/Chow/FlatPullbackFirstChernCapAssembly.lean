module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapAdditive
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSumsCanonical

/-!
# Flat pullback and the cap product with a first Chern class: the passage to a general cycle

In Situation 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be flat of relative
dimension `r`.  Fix component rules of Stacks 0EQJ on `Y` (in degree `k`) and on `X` (in degree
`k + r`).  For an integral closed subspace `W ⊆ Y` of δ-dimension `k + 1` the *defect* at `W` is
the `(k + r)`-cycle

`f^*(i_{W,*}(c₁ ∩ [W])) - c₁ ∩ f^*[W]`

on `X`.  This file proves that for every `(k + 1)`-cycle `α` on `Y`

`f^*(c₁ ∩ α) - c₁ ∩ f^*α = ∑_W α_W · (defect at W)`

coefficientwise, a locally finite sum, and deduces, by Stacks 0EQ8 at the canonical embeddings of
Stacks 0ENK, that `f^*(c₁ ∩ α) - c₁ ∩ f^*α` is rationally equivalent to zero as soon as every
integer multiple of every defect is rationally equivalent to zero by integral closed subspaces
lying in `f^{-1}(W)`.

## Main definitions

* `flatChernDefectCoeff`: the coefficients of the defect at `W`.
* `flatChernDefect`: the defect at `W`, as a cycle.

## Main results

* `flatPullbackMap_firstChernCapCycleMap_sub_apply`: the coefficientwise identity above.
* `isRationallyEquivalentToZeroCanonical_flatPullbackMap_firstChernCapCycleMap_sub`: if every
  integer multiple of every defect is rationally equivalent to zero, then so is
  `f^*(c₁ ∩ α) - c₁ ∩ f^*α`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The integral closed subspaces at which a cycle has a nonzero coefficient and whose point set
contains a given point form a finite set. -/
theorem finite_setOf_ne_zero_and_mem_subspacePointSet (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space} {m : ℤ}
    (β : CycleGroup D sX m) (p : points D.site D.base D.base_mem X) :
    {V : IntegralClosedSubspace D.site D.base D.base_mem X | β.1 V ≠ 0 ∧
      p ∈ subspacePointSet D.site D.base D.base_mem X V.subspace}.Finite := by
  obtain ⟨U, hU, hUfin⟩ := β.2.1 p
  refine hUfin.subset ?_
  rintro V ⟨hVne, hVp⟩
  exact ⟨_, by simpa [hVne] using hVp, mem_of_mem_nhds hU⟩

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (k : ℤ)
    (chernY : FirstChernComponentCycleRule D sY k)
    (chernX : FirstChernComponentCycleRule D sX (k + (r : ℤ)))

/-- The coefficient at `T ⊆ X` of the defect `f^*(i_{W,*}(c₁ ∩ [W])) - c₁ ∩ f^*[W]` at an
integral closed subspace `W ⊆ Y`, written out through the defining sums of the flat pullback of
Stacks 0EP8 and of the cap product of Stacks 0EQJ. -/
def flatChernDefectCoeff (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  (∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
      (firstChernComponentCycle D sY hY k chernY W).1 Z *
        flatPullbackMult D sX hX sY hY f hbase r hflat hr Z T) -
    ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      flatPullbackMult D sX hX sY hY f hbase r hflat hr W V *
        (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T

/-- **The defect at `W`.**  For an integral closed subspace `W ⊆ Y` of δ-dimension `k + 1`, the
`(k + r)`-cycle `f^*(i_{W,*}(c₁ ∩ [W])) - c₁ ∩ f^*[W]` on `X`. -/
def flatChernDefect (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hW : deltaDimension D sY W = k + 1) : CycleGroup D sX (k + (r : ℤ)) :=
  flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
      (firstChernComponentCycle D sY hY k chernY W) -
    firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
        (integralCycle D sY (k + 1) W hW))

/-- The coefficients of the defect are `AlgebraicGeometry.Space.flatChernDefectCoeff`. -/
theorem flatChernDefect_apply (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hW : deltaDimension D sY W = k + 1) (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (flatChernDefect D sX hX sY hY f hbase r hflat hr k chernY chernX W hW).1 T =
      flatChernDefectCoeff D sX hX sY hY f hbase r hflat hr k chernY chernX W T := by
  change (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
      (firstChernComponentCycle D sY hY k chernY W)).1 T -
    (firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
        (integralCycle D sY (k + 1) W hW))).1 T = _
  rw [flatPullbackMap_apply, firstChernCapCycleMap_apply, flatChernDefectCoeff]
  congr 1
  exact finsum_congr fun V => by
    rw [flatPullbackMap_integralCycle D sX hX sY hY f hbase r hflat hr (k + 1)
      (k + (r : ℤ) + 1) (by ring) W hW V]

/-- If an integral closed subspace `V ⊆ X` occurs in `f^*[W]` and its component cycle has a
nonzero coefficient at `T`, then `W` has δ-dimension `k + 1`. -/
theorem deltaDimension_eq_of_flatPullbackMult_mul_ne_zero
    {W : IntegralClosedSubspace D.site D.base D.base_mem Y}
    {V T : IntegralClosedSubspace D.site D.base D.base_mem X}
    (h : flatPullbackMult D sX hX sY hY f hbase r hflat hr W V *
      (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T ≠ 0) :
    deltaDimension D sY W = k + 1 := by
  have hm := left_ne_zero_of_mul h
  have hc := right_ne_zero_of_mul h
  have hV : deltaDimension D sX V = k + (r : ℤ) + 1 := by
    by_contra hne
    rw [firstChernComponentCycle_of_deltaDimension_ne D sX hX (k + (r : ℤ)) chernX hne] at hc
    exact hc rfl
  have hd := deltaDimension_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W V hm
  rw [hV] at hd
  lia

section Coefficients

variable (α : CycleGroup D sY (k + 1)) (T : IntegralClosedSubspace D.site D.base D.base_mem X)

/-- The point of `Y` under the generic point of `T`. -/
abbrev flatChernBasePoint : points D.site D.base D.base_mem Y :=
  pointsMap D.site D.base D.base_mem X f (T.ambientGenericPoint D.site D.base D.base_mem)

/-- The subspaces occurring in `α` through the image of the generic point of `T` form a finite
set. -/
theorem finite_flatChernSubspaces :
    {W : IntegralClosedSubspace D.site D.base D.base_mem Y | α.1 W ≠ 0 ∧
      flatChernBasePoint D f T ∈ subspacePointSet D.site D.base D.base_mem Y W.subspace}.Finite :=
  finite_setOf_ne_zero_and_mem_subspacePointSet D α _

/-- The subspaces at which a component cycle of a subspace occurring in `α` is nonzero and which
pass through the image of the generic point of `T` form a finite set. -/
theorem finite_flatChernComponentSubspaces :
    {Z : IntegralClosedSubspace D.site D.base D.base_mem Y |
      (∃ W : IntegralClosedSubspace D.site D.base D.base_mem Y, α.1 W ≠ 0 ∧
          (firstChernComponentCycle D sY hY k chernY W).1 Z ≠ 0) ∧
        flatChernBasePoint D f T ∈
          subspacePointSet D.site D.base D.base_mem Y Z.subspace}.Finite := by
  refine ((finite_flatChernSubspaces D sY f k α T).biUnion
    (t := fun W => {Z : IntegralClosedSubspace D.site D.base D.base_mem Y |
      (firstChernComponentCycle D sY hY k chernY W).1 Z ≠ 0 ∧
        flatChernBasePoint D f T ∈ subspacePointSet D.site D.base D.base_mem Y Z.subspace})
    fun W _ => finite_setOf_ne_zero_and_mem_subspacePointSet D _ _).subset ?_
  rintro Z ⟨⟨W, hWne, hccne⟩, hZp⟩
  exact Set.mem_biUnion (x := W)
    ⟨hWne, subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sY hY k chernY W Z hccne
      hZp⟩ ⟨hccne, hZp⟩

/-- The subspaces of `X` occurring in `f^*[W]`, for some `W` occurring in `α` through the image of
the generic point of `T`, with a nonzero component cycle at `T`, form a finite set. -/
theorem finite_flatChernPreimageSubspaces :
    {V : IntegralClosedSubspace D.site D.base D.base_mem X |
      ∃ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
        (α.1 W ≠ 0 ∧ flatChernBasePoint D f T ∈
          subspacePointSet D.site D.base D.base_mem Y W.subspace) ∧
        flatPullbackMult D sX hX sY hY f hbase r hflat hr W V ≠ 0 ∧
          (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T ≠ 0}.Finite := by
  refine ((finite_flatChernSubspaces D sY f k α T).biUnion
    (t := fun W => {V : IntegralClosedSubspace D.site D.base D.base_mem X |
      (flatPullbackIntegralCycle D sX hX sY hY f hbase r hflat hr W).1 V ≠ 0 ∧
        T.ambientGenericPoint D.site D.base D.base_mem ∈
          subspacePointSet D.site D.base D.base_mem X V.subspace})
    fun W _ => finite_setOf_ne_zero_and_mem_subspacePointSet D _ _).subset ?_
  rintro V ⟨W, hWA, hm, hc⟩
  exact Set.mem_biUnion (x := W) hWA
    ⟨hm, subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX (k + (r : ℤ)) chernX
      V T hc ⟨T.genericPoint D.site D.base D.base_mem, rfl⟩⟩

/-- **The commutator of the flat pullback and the cap product, coefficientwise.**  For a
`(k + 1)`-cycle `α` on `Y` and an integral closed subspace `T ⊆ X`, the coefficient at `T` of
`f^*(c₁ ∩ α) - c₁ ∩ f^*α` is `∑_W α_W · (defect at W)_T`. -/
theorem flatPullbackMap_firstChernCapCycleMap_sub_apply :
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
          (firstChernCapCycleMap D sY hY k chernY α)).1 T -
        (firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX
          (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
            α)).1 T =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
        α.1 W * flatChernDefectCoeff D sX hX sY hY f hbase r hflat hr k chernY chernX W T := by
  have hL : (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
        (firstChernCapCycleMap D sY hY k chernY α)).1 T =
      ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
        ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
          α.1 W * (firstChernComponentCycle D sY hY k chernY W).1 Z *
            flatPullbackMult D sX hX sY hY f hbase r hflat hr Z T := by
    rw [flatPullbackMap_apply]
    exact finsum_congr fun Z => by rw [firstChernCapCycleMap_apply, finsum_mul]
  have hR : (firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
          α)).1 T =
      ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
        ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
          α.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W V *
            (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T := by
    rw [firstChernCapCycleMap_apply]
    exact finsum_congr fun V => by rw [flatPullbackMap_apply, finsum_mul]
  have hvanL : ∀ (Z W : IntegralClosedSubspace D.site D.base D.base_mem Y),
      α.1 W * (firstChernComponentCycle D sY hY k chernY W).1 Z *
          flatPullbackMult D sX hX sY hY f hbase r hflat hr Z T ≠ 0 →
      Z ∈ {Z : IntegralClosedSubspace D.site D.base D.base_mem Y |
          (∃ W' : IntegralClosedSubspace D.site D.base D.base_mem Y, α.1 W' ≠ 0 ∧
              (firstChernComponentCycle D sY hY k chernY W').1 Z ≠ 0) ∧
            flatChernBasePoint D f T ∈ subspacePointSet D.site D.base D.base_mem Y Z.subspace} ∧
        W ∈ {W : IntegralClosedSubspace D.site D.base D.base_mem Y | α.1 W ≠ 0 ∧
          flatChernBasePoint D f T ∈ subspacePointSet D.site D.base D.base_mem Y W.subspace} := by
    intro Z W hZW
    have hαW : α.1 W ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hZW)
    have hccZ : (firstChernComponentCycle D sY hY k chernY W).1 Z ≠ 0 :=
      right_ne_zero_of_mul (left_ne_zero_of_mul hZW)
    have hpZ := mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr
      Z T (right_ne_zero_of_mul hZW)
    exact ⟨⟨⟨W, hαW, hccZ⟩, hpZ⟩,
      ⟨hαW, subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sY hY k chernY W Z
        hccZ hpZ⟩⟩
  have hvanR : ∀ (V : IntegralClosedSubspace D.site D.base D.base_mem X)
      (W : IntegralClosedSubspace D.site D.base D.base_mem Y),
      α.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W V *
          (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T ≠ 0 →
      V ∈ {V : IntegralClosedSubspace D.site D.base D.base_mem X |
          ∃ W' : IntegralClosedSubspace D.site D.base D.base_mem Y,
            (α.1 W' ≠ 0 ∧ flatChernBasePoint D f T ∈
              subspacePointSet D.site D.base D.base_mem Y W'.subspace) ∧
            flatPullbackMult D sX hX sY hY f hbase r hflat hr W' V ≠ 0 ∧
              (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T ≠ 0} ∧
        W ∈ {W : IntegralClosedSubspace D.site D.base D.base_mem Y | α.1 W ≠ 0 ∧
          flatChernBasePoint D f T ∈ subspacePointSet D.site D.base D.base_mem Y W.subspace} := by
    intro V W hVW
    have hαW : α.1 W ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hVW)
    have hmV : flatPullbackMult D sX hX sY hY f hbase r hflat hr W V ≠ 0 :=
      right_ne_zero_of_mul (left_ne_zero_of_mul hVW)
    have hccV : (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T ≠ 0 :=
      right_ne_zero_of_mul hVW
    have hTV : T.ambientGenericPoint D.site D.base D.base_mem ∈
        subspacePointSet D.site D.base D.base_mem X V.subspace :=
      subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX (k + (r : ℤ)) chernX
        V T hccV ⟨T.genericPoint D.site D.base D.base_mem, rfl⟩
    have hpW : flatChernBasePoint D f T ∈
        subspacePointSet D.site D.base D.base_mem Y W.subspace :=
      subspacePointSet_subset_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W V
        hmV hTV
    exact ⟨⟨W, ⟨hαW, hpW⟩, hmV, hccV⟩, ⟨hαW, hpW⟩⟩
  have hfinS := finite_flatChernSubspaces D sY f k α T
  have hsuppL : (Function.support fun W : IntegralClosedSubspace D.site D.base D.base_mem Y =>
      ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
        α.1 W * (firstChernComponentCycle D sY hY k chernY W).1 Z *
          flatPullbackMult D sX hX sY hY f hbase r hflat hr Z T).Finite := by
    refine hfinS.subset fun W hW => ?_
    by_contra hnot
    exact hW (finsum_eq_zero_of_forall_eq_zero fun Z => by
      by_contra hZ
      exact hnot (hvanL Z W hZ).2)
  have hsuppR : (Function.support fun W : IntegralClosedSubspace D.site D.base D.base_mem Y =>
      ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
        α.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W V *
          (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T).Finite := by
    refine hfinS.subset fun W hW => ?_
    by_contra hnot
    exact hW (finsum_eq_zero_of_forall_eq_zero fun V => by
      by_contra hV
      exact hnot (hvanR V W hV).2)
  rw [hL, hR,
    finsum_exchange_of_vanishing _ (finite_flatChernComponentSubspaces D sY hY f k chernY α T)
      hfinS hvanL,
    finsum_exchange_of_vanishing _
      (finite_flatChernPreimageSubspaces D sX hX sY hY f hbase r hflat hr k chernX α T)
      hfinS hvanR,
    ← finsum_sub_distrib hsuppL hsuppR]
  refine finsum_congr fun W => ?_
  rw [flatChernDefectCoeff, mul_sub, mul_finsum, mul_finsum]
  congr 1
  · exact finsum_congr fun Z => mul_assoc _ _ _
  · exact finsum_congr fun V => mul_assoc _ _ _

end Coefficients

/-- If for every integral closed subspace `W ⊆ Y` of δ-dimension `k + 1` every integer multiple
of the defect at `W` is rationally equivalent to zero, at the canonical embeddings of Stacks 0ENK,
by integral closed subspaces of `X` lying in `f^{-1}(W)`, then for every `(k + 1)`-cycle `α` on
`Y` the cycle `f^*(c₁ ∩ α) - c₁ ∩ f^*α` is rationally equivalent to zero. -/
theorem isRationallyEquivalentToZeroCanonical_flatPullbackMap_firstChernCapCycleMap_sub
    (hdefect : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (hW : deltaDimension D sY W = k + 1) (a : ℤ),
      IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sX hX (k + (r : ℤ))
        (a • flatChernDefect D sX hX sY hY f hbase r hflat hr k chernY chernX W hW)
        (pointsMap D.site D.base D.base_mem X f ⁻¹'
          subspacePointSet D.site D.base D.base_mem Y W.subspace))
    (α : CycleGroup D sY (k + 1)) :
    IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX (k + (r : ℤ))
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
          (firstChernCapCycleMap D sY hY k chernY α) -
        firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX
          (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
            α)) := by
  classical
  let J := {W : IntegralClosedSubspace D.site D.base D.base_mem Y // α.1 W ≠ 0}
  refine isRationallyEquivalentToZeroCanonical_finsum.{u + 1} D sX hX (k + (r : ℤ))
    (J := J)
    (fun j => α.1 j.1 • flatChernDefect D sX hX sY hY f hbase r hflat hr k chernY chernX j.1
      (α.2.2 j.1 j.2))
    (fun j => pointsMap D.site D.base D.base_mem X f ⁻¹'
      subspacePointSet D.site D.base D.base_mem Y j.1.subspace)
    ((locallyFinite_cycleSupport α).preimage_continuous
      (continuous_pointsMap D.site D.base D.base_mem f))
    (fun j => hdefect j.1 (α.2.2 j.1 j.2) (α.1 j.1)) fun T => ?_
  change (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
          (firstChernCapCycleMap D sY hY k chernY α)).1 T -
        (firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX
          (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
            α)).1 T = _
  rw [flatPullbackMap_firstChernCapCycleMap_sub_apply]
  have hj : ∀ j : J, ((α.1 j.1 • flatChernDefect D sX hX sY hY f hbase r hflat hr k chernY chernX
      j.1 (α.2.2 j.1 j.2) : CycleGroup D sX (k + (r : ℤ))) :
        IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) T =
      α.1 j.1 * flatChernDefectCoeff D sX hX sY hY f hbase r hflat hr k chernY chernX j.1 T :=
    fun j => by
      rw [AddSubgroup.coe_zsmul, Pi.smul_apply, flatChernDefect_apply, smul_eq_mul]
  rw [finsum_congr hj]
  refine Eq.trans ?_ (finsum_subtype_eq_finsum_cond
    (f := fun W =>
      α.1 W * flatChernDefectCoeff D sX hX sY hY f hbase r hflat hr k chernY chernX W T)
    (fun W => α.1 W ≠ 0)).symm
  refine finsum_congr fun W => ?_
  by_cases hW : α.1 W = 0
  · rw [hW, zero_mul, finsum_eq_if, ite_eq_right (not_not.2 rfl)]
  · rw [finsum_eq_if, ite_eq_left hW]

end AlgebraicGeometry.Space

end
