module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.TopSegreFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackIdentity

/-!
# The top-degree identity on an integral subspace from an étale chart

Let `q : Q ⟶ Y` be a proper flat morphism of good algebraic spaces of relative dimension `d`,
`ℒ` invertible on `Q` and `Φ_Y(α) = q_*(c₁(ℒ)^d ∩ q^*α)`. For an integral closed subspace
`Z ⊆ Y` of δ-dimension `k` the cycle `Φ_Y([Z])` is supported on `|Z|`, hence is `n [Z]` for an
integer `n`, and the top-degree case of Stacks 0ERU is the assertion `n = 1`. This file shows
that `n = 1` follows from `Φ_W(g^*[Z]) ∼_rat g^*[Z]` on `|g|^{-1}|Z|` for an étale morphism
`g : W ⟶ Y` with `g^*[Z] ≠ 0`.

## Main results

* `eq_of_subset_of_deltaDimension_eq`: an integral closed subspace inside another of the same
  δ-dimension is equal to it.
* `eq_zsmul_integralCycle_of_subset`: a `k`-cycle supported on an integral closed subspace of
  δ-dimension `k` is a multiple of its cycle.
* `eq_zero_of_rationallyEquivalentOn_of_forall_deltaDimension_le`: rigidity on a set without
  subspaces of δ-dimension `k + 1`.
* `flatPullbackMap_integralCycle_ne_zero_of_isEtale`: the étale pullback of `[Z]` is nonzero as
  soon as the inverse image of `|Z|` is nonempty.
* `topSegreCycle_flatPullbackMap_integralCycle_eq_of_etale`: `Φ_Y([Z]) = [Z]` from an étale chart.

## References

* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0EDV](https://stacks.math.columbia.edu/tag/0EDV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})

section Rigidity

variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

include hX in
/-- An integral closed subspace whose point set lies in that of another of the same δ-dimension
is equal to it. -/
theorem eq_of_subset_of_deltaDimension_eq
    (W Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWZ : subspacePointSet D.site D.base D.base_mem X W.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X Z.subspace)
    (h : deltaDimension D sX W = deltaDimension D sX Z) : W = Z := by
  set ξ := pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι
    (W.genericPoint D.site D.base D.base_mem)
  set η := pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
    (Z.genericPoint D.site D.base D.base_mem)
  have hξW : IsGenericPoint ξ (subspacePointSet D.site D.base D.base_mem X W.subspace) :=
    isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hX.1 W
  have hηZ : IsGenericPoint η (subspacePointSet D.site D.base D.base_mem X Z.subspace) :=
    isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hX.1 Z
  have hspec : η ⤳ ξ := hηZ.specializes (hWZ ⟨_, rfl⟩)
  have hanti : ∀ ⦃x y : points D.site D.base D.base_mem X⦄, x ⤳ y → x ≠ y →
      inducedDimensionValue D.site D.base D.base_mem D.delta sX y <
        inducedDimensionValue D.site D.base D.base_mem D.delta sX x :=
    lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) D.isAlgebraicSpace
      (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
        D.isAlgebraicSpace D.quasiSeparated)
      D.locallyNoetherian D.universallyCatenary D.delta sX hX.2.2
  have hηξ : η = ξ := by
    by_contra hne
    have := hanti hspec hne
    change D.deltaValue sX ξ < D.deltaValue sX η at this
    have h' : D.deltaValue sX ξ = D.deltaValue sX η := h
    omega
  obtain ⟨V, -, hV⟩ := existsUnique_integralClosedSubspace_isGenericPoint_of_isGood D sX hX ξ
  rw [hV W hξW, hV Z (hηξ ▸ hηZ)]

include hX in
/-- A `k`-cycle supported on an integral closed subspace of δ-dimension `k` is a multiple of its
cycle, the multiple being its coefficient there. -/
theorem eq_zsmul_integralCycle_of_subset (k : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (hZ : deltaDimension D sX Z = k)
    (β : CycleGroup D sX k)
    (hβ : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      β.1 V ≠ 0 → subspacePointSet D.site D.base D.base_mem X V.subspace ⊆
        subspacePointSet D.site D.base D.base_mem X Z.subspace) :
    β = β.1 Z • integralCycle D sX k Z hZ := by
  refine Subtype.ext (funext fun V => ?_)
  rw [AddSubgroup.coe_zsmul, Pi.smul_apply, integralCycle_coe, smul_eq_mul]
  by_cases hV : V = Z
  · rw [hV, integralCycleCoeff_self, mul_one]
  · rw [integralCycleCoeff_eq_zero D Z hV, mul_zero]
    by_contra hne
    exact hV (eq_of_subset_of_deltaDimension_eq D sX hX V Z (hβ V hne)
      ((β.2.2 V hne).trans hZ.symm))

/-- If every integral closed subspace
with point set inside `T` has δ-dimension at most `k`, a `k`-cycle rationally equivalent to zero
on `T` is zero. -/
theorem eq_zero_of_rationallyEquivalentOn_of_forall_deltaDimension_le (k : ℤ)
    (T : Set (points D.site D.base D.base_mem X))
    (hT : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      subspacePointSet D.site D.base D.base_mem X V.subspace ⊆ T → deltaDimension D sX V ≤ k)
    {β : CycleGroup D sX k} (h : RationallyEquivalentOn.{u + 1} D sX hX k T β 0) : β = 0 := by
  obtain ⟨J, W, hWfin, c, hWdim, -, hWT, hsum⟩ := h
  have : IsEmpty J := ⟨fun j => by
    have := hT (W j) (hWT j)
    rw [hWdim j] at this
    omega⟩
  rw [sub_zero] at hsum
  subst hsum
  exact Subtype.ext (funext fun Z => by
    rw [cycleFamilySum_apply, finsum_of_isEmpty]
    rfl)

end Rigidity

section Etale

variable {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

include hX hY in
/-- Along a locally quasi-finite morphism `g : X ⟶ Y` over the base, an integral closed subspace
of `X` mapping into `|Z|` has δ-dimension at most that of `Z`. -/
theorem deltaDimension_le_of_subset_preimage {g : X ⟶ Y} (hg : g ≫ sY = sX)
    (hgq : IsLocallyQuasiFinite D.site D.base D.base_mem g)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (V : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hV : subspacePointSet D.site D.base D.base_mem X V.subspace ⊆
      pointsMap D.site D.base D.base_mem X g ⁻¹'
        subspacePointSet D.site D.base D.base_mem Y Z.subspace) :
    deltaDimension D sX V ≤ deltaDimension D sY Z := by
  set ξ := pointsMap D.site D.base D.base_mem V.subspace.toFunctor V.subspace.ι
    (V.genericPoint D.site D.base D.base_mem)
  set η := pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
    (Z.genericPoint D.site D.base D.base_mem)
  have hgξ : pointsMap D.site D.base D.base_mem X g ξ ∈
      subspacePointSet D.site D.base D.base_mem Y Z.subspace := hV ⟨_, rfl⟩
  have hηZ : IsGenericPoint η (subspacePointSet D.site D.base D.base_mem Y Z.subspace) :=
    isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hY.1 Z
  have hspec : η ⤳ pointsMap D.site D.base D.base_mem X g ξ := hηZ.specializes hgξ
  have hanti : ∀ ⦃x y : points D.site D.base D.base_mem Y⦄, x ⤳ y → x ≠ y →
      inducedDimensionValue D.site D.base D.base_mem D.delta sY y <
        inducedDimensionValue D.site D.base D.base_mem D.delta sY x :=
    lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) D.isAlgebraicSpace
      (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
        D.isAlgebraicSpace D.quasiSeparated)
      D.locallyNoetherian D.universallyCatenary D.delta sY hY.2.2
  have hcomp :
      D.deltaValue sX ξ = D.deltaValue sY (pointsMap D.site D.base D.base_mem X g ξ) := by
    rw [← D.deltaValue_comp_of_isLocallyQuasiFinite hX.1 hY.1 g sY hgq hY.2.2 ξ, hg]
  show D.deltaValue sX ξ ≤ D.deltaValue sY η
  rw [hcomp]
  by_cases he : η = pointsMap D.site D.base D.base_mem X g ξ
  · rw [he]
  · exact le_of_lt (hanti hspec he)

/-- For an étale `g : W ⟶ Y` and an integral closed subspace `Z ⊆ Y` with `|g|^{-1}|Z|` nonempty,
`g^*[Z] ≠ 0`. -/
theorem flatPullbackMap_integralCycle_ne_zero_of_isEtale
    {W : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sW : W ⟶ D.space) (hW : D.IsGood sW) {g : W ⟶ Y} (hg : g ≫ sY = sW)
    (hget : IsEtale D.site D.base D.base_mem g) (hgf : IsFlat D.site D.base D.base_mem g)
    (hg0 : HasRelativeDimension 0 D.site D.base D.base_mem g) (k : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) (hZ : deltaDimension D sY Z = k)
    (hT : (Z.preimagePointSet D.site D.base D.base_mem g).Nonempty) :
    flatPullbackMap D sW hW sY hY g hg 0 hgf hg0 k (k + ((0 : ℕ) : ℤ)) rfl
      (integralCycle D sY k Z hZ) ≠ 0 := by
  obtain ⟨x, hx⟩ := hT
  obtain ⟨C, hC, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({⟨x, hx⟩} : Set (Z.preimagePointSet D.site D.base D.base_mem g)) isIrreducible_singleton
  intro h
  have key := congrFun (Z.flatPullbackMap_integralCycle_eq_preimageComponentsCycle D sW hW sY hY
    hget hg k (k + ((0 : ℕ) : ℤ)) hZ rfl)
    (Z.preimageComponent D.site D.base D.base_mem g hW.1 (D.isDecentSpace_of_isGood sW hW) hY.1
      ⟨C, hC⟩)
  rw [h] at key
  exact ((Z.preimageComponentsCycle_ne_zero_iff D sW hW sY hY g _).2 ⟨⟨C, hC⟩, rfl⟩) key.symm

/-- The top-degree identity on an integral subspace, from an étale chart. Let
`Q_W = W ×_Y Q` for a proper flat `q : Q ⟶ Y` of relative dimension `d` and an étale (flat of
relative dimension `0` and locally quasi-finite) `g : W ⟶ Y`, and let `Z ⊆ Y` be integral of
δ-dimension `k` with `g^*[Z] ≠ 0`. If `Φ_W(g^*[Z]) ∼_rat g^*[Z]` on `|g|^{-1}|Z|`, where `Φ_W`
is built from `q_W` and `g'^*ℒ`, then `Φ_Y([Z]) = [Z]`. -/
theorem topSegreCycle_flatPullbackMap_integralCycle_eq_of_etale
    {Q W QW : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ) (sW : W ⟶ D.space) (hW : D.IsGood sW)
    (sQW : QW ⟶ D.space) (hQW : D.IsGood sQW)
    {q : Q ⟶ Y} {g : W ⟶ Y} {qW : QW ⟶ W} {g' : QW ⟶ Q} (sq : IsPullback g' qW q g)
    (hq : q ≫ sY = sQ) (hg : g ≫ sY = sW) (hqW : qW ≫ sW = sQW) (hg' : g' ≫ sQ = sQW)
    (hqp : IsProper D.site D.base D.base_mem q) (d : ℕ)
    (hqf : IsFlat D.site D.base D.base_mem q)
    (hqd : HasRelativeDimension d D.site D.base D.base_mem q)
    (hgf : IsFlat D.site D.base D.base_mem g)
    (hg0 : HasRelativeDimension 0 D.site D.base D.base_mem g)
    (hgq : IsLocallyQuasiFinite D.site D.base D.base_mem g)
    (hqWp : IsProper D.site D.base D.base_mem qW)
    (hqWf : IsFlat D.site D.base D.base_mem qW)
    (hqWd : HasRelativeDimension d D.site D.base D.base_mem qW)
    (hg'f : IsFlat D.site D.base D.base_mem g')
    (hg'0 : HasRelativeDimension 0 D.site D.base D.base_mem g')
    (L : Modules.{u, u} D.site D.base D.base_mem Q hQ.1)
    (hL : IsInvertibleModule (⟨Q, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (k n : ℤ) (hkn : k + (d : ℤ) = n)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) (hZ : deltaDimension D sY Z = k)
    (hne : flatPullbackMap D sW hW sY hY g hg 0 hgf hg0 k (k + ((0 : ℕ) : ℤ)) rfl
      (integralCycle D sY k Z hZ) ≠ 0)
    (hchart : RationallyEquivalentOn.{u + 1} D sW hW (k + ((0 : ℕ) : ℤ))
      (pointsMap D.site D.base D.base_mem W g ⁻¹'
        subspacePointSet D.site D.base D.base_mem Y Z.subspace)
      (topSegreCycle D sQW hQW sW hW hqW hqWp.2.1.2 (pullbackLine D sQW hQW sQ hQ g' L)
        (isInvertibleModule_pullbackLine D sQW hQW sQ hQ g' L hL) d (k + ((0 : ℕ) : ℤ))
        (n + ((0 : ℕ) : ℤ)) (by omega)
        (flatPullbackMap D sQW hQW sW hW qW hqW d hqWf hqWd (k + ((0 : ℕ) : ℤ))
          (n + ((0 : ℕ) : ℤ)) (by omega)
          (flatPullbackMap D sW hW sY hY g hg 0 hgf hg0 k (k + ((0 : ℕ) : ℤ)) rfl
            (integralCycle D sY k Z hZ))))
      (flatPullbackMap D sW hW sY hY g hg 0 hgf hg0 k (k + ((0 : ℕ) : ℤ)) rfl
        (integralCycle D sY k Z hZ))) :
    topSegreCycle D sQ hQ sY hY hq hqp.2.1.2 L hL d k n hkn
        (flatPullbackMap D sQ hQ sY hY q hq d hqf hqd k n hkn (integralCycle D sY k Z hZ)) =
      integralCycle D sY k Z hZ := by
  set T := subspacePointSet D.site D.base D.base_mem Y Z.subspace
  have hTc : IsClosed T := isClosed_range_pointsMap_integralClosedSubspace D.site D.base
    D.base_mem hY.1 Z
  have hZT : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y,
      (integralCycle D sY k Z hZ).1 V ≠ 0 →
        subspacePointSet D.site D.base D.base_mem Y V.subspace ⊆ T := fun V hV => by
    rw [eq_of_integralCycleCoeff_ne_zero D Z hV]
  obtain ⟨m, hm⟩ : ∃ m : ℤ, topSegreCycle D sQ hQ sY hY hq hqp.2.1.2 L hL d k n hkn
      (flatPullbackMap D sQ hQ sY hY q hq d hqf hqd k n hkn (integralCycle D sY k Z hZ)) =
        m • integralCycle D sY k Z hZ :=
    ⟨_, eq_zsmul_integralCycle_of_subset D sY hY k Z hZ _
      (subspacePointSet_subset_of_topSegreCycle_flatPullbackMap_ne_zero D sQ hQ sY hY hq
        hqp.2.1.2 d hqf hqd L hL k n hkn T hTc _ hZT)⟩
  set c := flatPullbackMap D sW hW sY hY g hg 0 hgf hg0 k (k + ((0 : ℕ) : ℤ)) rfl
    (integralCycle D sY k Z hZ)
  have hbc := rationallyEquivalentOn_flatPullbackMap_topSegreCycle D sY hY sQ hQ sW hW sQW hQW sq
    hq hg hqW hg' hqp d 0 hqf hqd hgf hg0 hqWp hqWf hqWd hg'f hg'0 L hL k n hkn T hTc _ hZT
  have hre := RationallyEquivalentOn.trans hbc hchart
  rw [hm, map_zsmul] at hre
  have hre0 := (rationallyEquivalentOn_iff_zero.{u + 1} D sW hW _).1 hre
  rw [show m • c - c = (m - 1) • c by rw [sub_smul, one_smul]] at hre0
  have hzero := eq_zero_of_rationallyEquivalentOn_of_forall_deltaDimension_le D sW hW
    (k + ((0 : ℕ) : ℤ)) _ (fun V hV => by
      have := deltaDimension_le_of_subset_preimage D sW hW sY hY hg hgq Z V hV
      omega) hre0
  have hn : m = 1 := by
    obtain ⟨V, hV⟩ : ∃ V, c.1 V ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Subtype.ext (funext h))
    have := congrArg (fun γ : CycleGroup D sW (k + ((0 : ℕ) : ℤ)) => γ.1 V) hzero
    simp only [AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul] at this
    rcases mul_eq_zero.1 this with h | h
    · omega
    · exact absurd h hV
  rw [hm, hn, one_smul]

end Etale

end AlgebraicGeometry.Space.PrivateChern

end
