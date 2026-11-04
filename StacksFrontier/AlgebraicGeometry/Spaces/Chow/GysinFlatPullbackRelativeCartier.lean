module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.TrivialRestrictionGysin
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeEffectiveCartierRelativeDimension

/-!
# The refined Gysin map of a relative effective Cartier divisor on a flat pullback

In Situation 0EDT let `X, Y/B` be good, let `p : X ⟶ Y` be flat of relative dimension `r + 1`
and let `E ⊆ X` be a relative effective Cartier divisor on `X/Y` (Stacks 0EPP). By
`AlgebraicGeometry.Space.hasRelativeDimension_comp_of_isRelativeEffectiveCartierDivisor` the
restriction `p|_E : E ⟶ Y` is flat of relative dimension `r`, so both sides of the first
identity of Stacks 0ERE,

`i^* p^* α = (p|_E)^* α`,

are defined on cycles: `p^* α` is a `(k + r + 2)`-cycle on `X`, `i^*` is the refined Gysin map of
Stacks 0ER1 at the level of cycles, `AlgebraicGeometry.Space.gysinCycleMap`, and `(p|_E)^* α` is a
`(k + r + 1)`-cycle on `E`.

This file records two steps of the source's proof. First, no integral closed subspace occurring
in `p^*[W]`, for `W ⊆ Y` integral of δ-dimension `k + 1`, is contained in `E`; so on `p^* α` only
clause (1)(a) of Stacks 0ER1 is used, and the component rule `c₁(ℒ|_W) ∩ [W]` of clause (1)(b)
plays no role. Second, the identity for a general cycle `α = ∑ n_W [W]` follows from the identity
for each `[W]`, which is Stacks 0ER7 for the closed subspace `p^{-1}(W)`, meeting `E` in the
effective Cartier divisor `(p|_E)^{-1}(W)` of `p^{-1}(W)` (Stacks 0EPN).

## Main results

* `AlgebraicGeometry.Space.hasRelativeDimension_ι_comp`: `p|_E` has relative dimension `r`.
* `AlgebraicGeometry.Space.not_le_of_flatPullbackMult_ne_zero`: the non-containment.
* `AlgebraicGeometry.Space.gysinCycleMap_flatPullbackMap_eq_of_forall_integral`: the passage from
  `α = [W]` to a general cycle.

## Implementation notes

The source deduces the non-containment from Stacks 0EPN: `E ∩ p^{-1}(W)` is an effective Cartier
divisor on `p^{-1}(W)`, hence contains no irreducible component of it. Here it is a dimension
count instead, which needs only the relative dimension of `p|_E`: an integral closed subspace of
`p^{-1}(W)` of δ-dimension `k + r + 2` contained in `E` would lie in `(p|_E)^{-1}(W)`, whose
δ-dimension is at most `k + 1 + r` by Stacks 0EPB, part (1).

## References

* [Stacks Project, Tag 0ERE](https://stacks.math.columbia.edu/tag/0ERE)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
* [Stacks Project, Tag 0EPN](https://stacks.math.columbia.edu/tag/0EPN)
* [Stacks Project, Tag 0EPP](https://stacks.math.columbia.edu/tag/0EPP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (p : X ⟶ Y) (hbase : p ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem p)

include hbase in
/-- A relative effective Cartier divisor `E` on `X/Y` restricts `p` to a morphism `E ⟶ Y` of
relative dimension `r` when `p` has relative dimension `r + 1`. -/
theorem hasRelativeDimension_ι_comp (hr : HasRelativeDimension (r + 1) D.site D.base D.base_mem p)
    (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) E) :
    HasRelativeDimension r D.site D.base D.base_mem (E.1.ι ≫ p) :=
  hasRelativeDimension_comp_of_isRelativeEffectiveCartierDivisor D.site D.base D.base_mem
    (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y, hY.1⟩)
    (isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace p sY
      (hbase ▸ hX.2.2)) r hr E hE

/-- **No subspace occurring in `p^*[W]` is contained in a relative effective Cartier divisor.**
Let `W ⊆ Y` be an integral closed subspace and `W' ⊆ X` an integral closed subspace with a
nonzero coefficient in `p^*[W]`. Then `W'` is not contained in `E`.

The δ-dimension of `W'` is `dim_δ(W) + r + 1`. If `W' ⊆ E`, its generic point would be a point
of `(p|_E)^{-1}(W)`, whose δ-dimension is at most `dim_δ(W) + r` because `p|_E` has relative
dimension `r` (Stacks 0EPB, part (1)); the δ-function of `E` is the restriction of the one of
`X`, the inclusion being locally quasi-finite. -/
theorem not_le_of_flatPullbackMult_ne_zero
    (hr : HasRelativeDimension (r + 1) D.site D.base D.base_mem p)
    (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) E)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW' : flatPullbackMult D sX hX sY hY p hbase (r + 1) hflat hr W W' ≠ 0) :
    ¬ W'.subspace ≤ E.1 := by
  intro hle
  have hEg : D.IsGood (E.1.ι ≫ sX) := isGood_closedSubspace D sX hX E
  have hEr := hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr E hE
  -- the generic point of `W'` lies on `E`
  set ξ := W'.ambientGenericPoint D.site D.base D.base_mem
  have hξE : ξ ∈ subspacePointSet D.site D.base D.base_mem X E.1 :=
    subspacePointSet_mono_of_le D hle ⟨_, rfl⟩
  obtain ⟨e, he⟩ := hξE
  -- and over a point of `W`
  have hpξ := mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY p hbase (r + 1)
    hflat hr W W' hW'
  have heW : e ∈ subspacePointSet D.site D.base D.base_mem E.1.toFunctor
      (W.subspace.preimage (E.1.ι ≫ p)) := by
    rw [subspacePointSet_preimage, Set.mem_preimage, pointsMap_comp, Function.comp_apply, he]
    exact hpξ
  -- the δ-dimension bound on `(p|_E)^{-1}(W)`
  have hbound := deltaDimensionSubspace_preimage_integralClosedSubspace_le D (E.1.ι ≫ sX) hEg sY
    hY (E.1.ι ≫ p) (comp_structureMorphism_eq D (E.1.ι ≫ sX) sX sY E.1.ι p rfl hbase) r hE.2 hEr W
  rw [deltaDimensionSubspace_eq_deltaDimensionClosed, deltaDimensionClosed_le_coe_iff] at hbound
  have he' := hbound e heW
  have hlqf : IsLocallyQuasiFinite D.site D.base D.base_mem E.1.ι :=
    isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem E.1.ι
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem E.2.2)
  have hcomp : inducedDimensionValue D.site D.base D.base_mem D.delta (E.1.ι ≫ sX) e =
      inducedDimensionValue D.site D.base D.base_mem D.delta sX ξ := by
    rw [← he]
    exact D.deltaValue_comp_of_isLocallyQuasiFinite E.2.1 hX.1 E.1.ι sX hlqf hX.2.2 e
  have hdimW' := deltaDimension_eq_of_flatPullbackMult_ne_zero D sX hX sY hY p hbase (r + 1)
    hflat hr W W' hW'
  have hξval : deltaDimension D sX W' =
      inducedDimensionValue D.site D.base D.base_mem D.delta sX ξ :=
    deltaDimension_eq_of_isGenericPoint D sX hX.1 W' ξ
      (W'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1)
  rw [hcomp, ← hξval, hdimW'] at he'
  push_cast at he'
  omega

/-- **The refined Gysin map on a flat pullback, from integral cycles.** Let
`rule : GysinComponentRule D sX E (k + r + 1)` be a component rule for the Gysin map of `E` and
suppose that for every integral closed subspace `W ⊆ Y` of δ-dimension `k + 1`, the Gysin map
sends `p^*[W]` to `(p|_E)^*[W]`, coefficientwise:

`∑_{W'} m_{W', p^{-1}(W)} · (i^*[W'])_T = m_{T, (p|_E)^{-1}(W)}` for every `T ⊆ E`.

Then `i^* p^* α = (p|_E)^* α` for every `(k + 1)`-cycle `α` on `Y`.

This is the passage of the source from `α = [W]` to a general cycle `α = ∑ n_W [W]`, which is not
formal because a cycle is an infinite formal sum: at a fixed `T ⊆ E` the sums that occur are
finite, by local finiteness of `α` at the image of the generic point of `T` and of each `p^*[W]`
at that generic point. -/
theorem gysinCycleMap_flatPullbackMap_eq_of_forall_integral
    (hr : HasRelativeDimension (r + 1) D.site D.base D.base_mem p)
    (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) E) (k : ℤ)
    (rule : GysinComponentRule D sX E (k + r + 1))
    (hW : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY W = k + 1 →
      ∀ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
        ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X,
            flatPullbackMult D sX hX sY hY p hbase (r + 1) hflat hr W W' *
              (gysinComponentCycle D sX E (isGood_closedSubspace D sX hX E) (k + r + 1) rule
                W').1 T =
          flatPullbackMult D (E.1.ι ≫ sX) (isGood_closedSubspace D sX hX E) sY hY (E.1.ι ≫ p)
            (comp_structureMorphism_eq D (E.1.ι ≫ sX) sX sY E.1.ι p rfl hbase) r hE.2
            (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr E hE) W T)
    (α : CycleGroup D sY (k + 1)) :
    gysinCycleMap D sX E (isGood_closedSubspace D sX hX E) (k + r + 1) rule
        (flatPullbackMap D sX hX sY hY p hbase (r + 1) hflat hr (k + 1) (k + r + 1 + 1)
          (by push_cast; ring) α) =
      flatPullbackMap D (E.1.ι ≫ sX) (isGood_closedSubspace D sX hX E) sY hY (E.1.ι ≫ p)
        (comp_structureMorphism_eq D (E.1.ι ≫ sX) sX sY E.1.ι p rfl hbase) r hE.2
        (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr E hE) (k + 1) (k + r + 1)
        (by ring) α := by
  classical
  set hEg := isGood_closedSubspace D sX hX E
  set hEb := comp_structureMorphism_eq D (E.1.ι ≫ sX) sX sY E.1.ι p rfl hbase
  set hEr := hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr E hE
  refine Subtype.ext (funext fun T => ?_)
  rw [gysinCycleMap_apply, flatPullbackMap_apply]
  simp only [flatPullbackMap_apply]
  set m := flatPullbackMult D sX hX sY hY p hbase (r + 1) hflat hr
  set mE := flatPullbackMult D (E.1.ι ≫ sX) hEg sY hY (E.1.ι ≫ p) hEb r hE.2 hEr
  set c := fun W' : IntegralClosedSubspace D.site D.base D.base_mem X =>
    (gysinComponentCycle D sX E hEg (k + r + 1) rule W').1 T
  -- the point of `X` below the generic point of `T`, and its image in `Y`
  set t := pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι
    (T.ambientGenericPoint D.site D.base D.base_mem)
  set y := pointsMap D.site D.base D.base_mem X p t
  have hct : ∀ W', c W' ≠ 0 → t ∈ subspacePointSet D.site D.base D.base_mem X W'.subspace :=
    fun W' hW' => subspacePointSet_subset_of_gysinComponentCycle_ne_zero D sX E hEg (k + r + 1)
      rule W' T hW' ⟨_, rfl⟩
  have hmy : ∀ W W', m W W' ≠ 0 → t ∈ subspacePointSet D.site D.base D.base_mem X W'.subspace →
      y ∈ subspacePointSet D.site D.base D.base_mem Y W.subspace :=
    fun W W' hm ht => subspacePointSet_subset_of_flatPullbackMult_ne_zero D sX hX sY hY p hbase
      (r + 1) hflat hr W W' hm ht
  have hmEy : ∀ W, mE W T ≠ 0 → y ∈ subspacePointSet D.site D.base D.base_mem Y W.subspace := by
    intro W hm
    have h := subspacePointSet_subset_of_flatPullbackMult_ne_zero D (E.1.ι ≫ sX) hEg sY hY
      (E.1.ι ≫ p) hEb r hE.2 hEr W T hm ⟨T.genericPoint D.site D.base D.base_mem, rfl⟩
    rwa [Set.mem_preimage, pointsMap_comp, Function.comp_apply] at h
  -- the finitely many `W` that can contribute
  obtain ⟨V, hV, hVfin⟩ := α.2.1 y
  set SW : Set (IntegralClosedSubspace D.site D.base D.base_mem Y) :=
    {W | α.1 W ≠ 0 ∧ y ∈ subspacePointSet D.site D.base D.base_mem Y W.subspace}
  have hSW : SW.Finite := by
    refine hVfin.subset fun W hW => ⟨y, ?_, mem_of_mem_nhds hV⟩
    simpa [hW.1] using hW.2
  -- for each of them, the finitely many `W'`
  have hSW' : ∀ W, {W' : IntegralClosedSubspace D.site D.base D.base_mem X |
      m W W' ≠ 0 ∧ t ∈ subspacePointSet D.site D.base D.base_mem X W'.subspace}.Finite := by
    intro W
    obtain ⟨V', hV', hV'fin⟩ :=
      (flatPullbackIntegralCycle D sX hX sY hY p hbase (r + 1) hflat hr W).2.1 t
    refine hV'fin.subset fun W' hW' => ⟨t, ?_, mem_of_mem_nhds hV'⟩
    have hne : (flatPullbackIntegralCycle D sX hX sY hY p hbase (r + 1) hflat hr W).1 W' ≠ 0 :=
      hW'.1
    simpa [hne] using hW'.2
  set FW := hSW.toFinset
  set FW' := (hSW.toFinset.biUnion fun W => (hSW' W).toFinset)
  have hmemFW' : ∀ W W', W ∈ SW → m W W' ≠ 0 →
      t ∈ subspacePointSet D.site D.base D.base_mem X W'.subspace → W' ∈ FW' := by
    intro W W' hW hm ht
    exact Finset.mem_biUnion.2 ⟨W, hSW.mem_toFinset.2 hW, (hSW' W).mem_toFinset.2 ⟨hm, ht⟩⟩
  -- the left-hand side as a finite double sum
  have hL : ∑ᶠ W', (∑ᶠ W, α.1 W * m W W') * c W' =
      ∑ W' ∈ FW', ∑ W ∈ FW, α.1 W * m W W' * c W' := by
    rw [finsum_eq_sum_of_support_subset (s := FW')]
    · refine Finset.sum_congr rfl fun W' _ => ?_
      by_cases hc : c W' = 0
      · simp [hc]
      rw [finsum_eq_sum_of_support_subset (s := FW), Finset.sum_mul]
      intro W hW
      have hW' : α.1 W * m W W' ≠ 0 := hW
      exact hSW.mem_toFinset.2 ⟨left_ne_zero_of_mul hW',
        hmy W W' (right_ne_zero_of_mul hW') (hct W' hc)⟩
    · intro W' hW'
      have h1 : (∑ᶠ W, α.1 W * m W W') * c W' ≠ 0 := hW'
      have hc : c W' ≠ 0 := right_ne_zero_of_mul h1
      have h2 : ∑ᶠ W, α.1 W * m W W' ≠ 0 := left_ne_zero_of_mul h1
      obtain ⟨W, hW⟩ : ∃ W, α.1 W * m W W' ≠ 0 := by
        by_contra hall
        push Not at hall
        exact h2 (finsum_eq_zero_of_forall_eq_zero hall)
      have ht := hct W' hc
      exact Finset.mem_coe.2 (hmemFW' W W' ⟨left_ne_zero_of_mul hW,
        hmy W W' (right_ne_zero_of_mul hW) ht⟩ (right_ne_zero_of_mul hW) ht)
  -- the right-hand side as a finite double sum
  have hR : ∑ᶠ W, α.1 W * mE W T = ∑ W ∈ FW, ∑ W' ∈ FW', α.1 W * m W W' * c W' := by
    rw [finsum_eq_sum_of_support_subset (s := FW)]
    · refine Finset.sum_congr rfl fun W hWF => ?_
      have hWS : W ∈ SW := hSW.mem_toFinset.1 hWF
      have hdim : deltaDimension D sY W = k + 1 := α.2.2 W hWS.1
      rw [← hW W hdim T, finsum_eq_sum_of_support_subset (s := FW'), Finset.mul_sum]
      · exact Finset.sum_congr rfl fun W' _ => by ring
      · intro W' hW'
        have h1 : m W W' * c W' ≠ 0 := hW'
        exact Finset.mem_coe.2 (hmemFW' W W' hWS (left_ne_zero_of_mul h1)
          (hct W' (right_ne_zero_of_mul h1)))
    · intro W hW
      have h1 : α.1 W * mE W T ≠ 0 := hW
      exact Finset.mem_coe.2 (hSW.mem_toFinset.2 ⟨left_ne_zero_of_mul h1,
        hmEy W (right_ne_zero_of_mul h1)⟩)
  show ∑ᶠ W', (∑ᶠ W, α.1 W * m W W') * c W' = ∑ᶠ W, α.1 W * mE W T
  rw [hL, hR, Finset.sum_comm]

end AlgebraicGeometry.Space

end
