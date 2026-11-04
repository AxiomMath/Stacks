module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatProperTopPowerReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapPow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.OpenRestrictionFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional

/-!
# The top power over an integral base from a nonempty open

Let `π : P → X` be proper and flat of relative dimension `n` with `X` integral of δ-dimension
`k`, and `ℒ` invertible on `P`. Then `π_*(c₁(ℒ)^n ∩ π^*[X]) = d [X]` for an integer `d`. If
`j : U → X` is a nonempty open with base change `π_U : P_U → U`, `j' : P_U → P`, and the top power
holds in `CH_k(U)` for `(π_U, j'^*ℒ)`, then `d = 1`.

## Main results

* `properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_top_of_isOpenImmersion`
  (in the namespace `AlgebraicGeometry.Space`): the identity `π_*(c₁(ℒ)^n ∩ π^*[X]) = [X]` of
  cycles from the top power on a nonempty open.

## References

* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Open

variable (D : BaseSpaceDimensionSituation.{u})
    {X P U PU : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (sU : U ⟶ D.space) (hU : D.IsGood sU) (sPU : PU ⟶ D.space) (hPU : D.IsGood sPU)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (hp : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) (hjB : j ≫ sX = sU)
    {j' : PU ⟶ P} {πU : PU ⟶ U} (hj'B : j' ≫ sP = sPU) (hπUB : πU ≫ sU = sPU)
    (sq : IsPullback j' πU π j)

include hX hj in
/-- The open immersion `j` is flat of relative dimension `0`. -/
theorem isFlat_and_hasRelativeDimension_zero_of_isOpenImmersion' :
    IsFlat D.site D.base D.base_mem j ∧ HasRelativeDimension 0 D.site D.base D.base_mem j :=
  ⟨isFlat_of_isEtale D.site D.base D.base_mem
      (isEtale_of_isOpenImmersion D.site D.base D.base_mem hj),
    hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem j hX.1
      (isEtale_of_isOpenImmersion D.site D.base D.base_mem hj)⟩

include hX hU hj hjB in
/-- Every integral closed subspace of an open subspace of an integral space has at most the
δ-dimension of the whole space. -/
theorem deltaDimension_le_of_isOpenImmersion_of_isIntegralSpace
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem U) :
    deltaDimension D sU W ≤
      deltaDimension D sX (IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint) := by
  have h := IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hU.1
    (D.isDecentSpace_of_isGood sX hX) (isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj) W
  subst hjB
  rw [← h]
  refine (deltaDimension_le_and_eq_of_subspacePointSet_subset D sX hX ?_).1
  exact (Set.subset_univ _).trans_eq
    (IntegralClosedSubspace.range_pointsMap_top D.site D.base D.base_mem hX.1 hint).symm

include hj hX hU in
/-- On a nonempty open of an integral space there is an integral closed subspace whose closure is
the whole space. -/
theorem exists_closureImage_eq_top_of_isOpenImmersion
    (hint : IsIntegralSpace D.site D.base D.base_mem X) (u₀ : points D.site D.base D.base_mem U) :
    ∃ W : IntegralClosedSubspace D.site D.base D.base_mem U,
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
          (D.isDecentSpace_of_isGood sX hX) j W =
        IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint := by
  set T := IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint
  have hmem : u₀ ∈ T.preimagePointSet D.site D.base D.base_mem j := by
    show pointsMap D.site D.base D.base_mem U j u₀ ∈
      subspacePointSet D.site D.base D.base_mem X T.subspace
    rw [subspacePointSet, IntegralClosedSubspace.range_pointsMap_top]
    exact Set.mem_univ _
  obtain ⟨C, hC, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({⟨u₀, hmem⟩} : Set (T.preimagePointSet D.site D.base D.base_mem j)) isIrreducible_singleton
  exact ⟨_, (T.exists_preimageComponent_eq_iff_closureImage_eq D sX hX sU hU hj _).1 ⟨⟨C, hC⟩, rfl⟩⟩

include hj hjB hj'B in
/-- **The top power over an integral base, from a nonempty open.** -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_top_of_isOpenImmersion
    (hint : IsIntegralSpace D.site D.base D.base_mem X) (u₀ : points D.site D.base D.base_mem U)
    (k : ℤ) (hk : deltaDimension D sX (IntegralClosedSubspace.top D.site D.base D.base_mem hX.1
      hint) = k)
    (htop : ∀ γ : CycleGroup D sU k,
      chowClassCanonical.{u + 1} D sU hU k
          (properCyclePushforward D sPU hPU sU hU hπUB
            (isProper_of_isPullback D.site D.base D.base_mem hPU.1 hP.1 hU.1 hX.1 sq hp).2.1.2 k
            (firstChernCapPowCycleMap D sPU hPU
              ((modulePullback D.site D.base D.base_mem
                (ObjectProperty.homMk j' :
                  (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨P, hP.1⟩)).obj L)
              (modulePullbackInvertible
                (ObjectProperty.homMk j' :
                  (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨P, hP.1⟩) L hL) n k
              (flatPullbackMap D sPU hPU sU hU πU hπUB n
                (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB
                  hπB sq.flip n hflat hrel).2.1
                (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB
                  hπB sq.flip n hflat hrel).2.2 k (k + n) rfl γ))) =
        chowClassCanonical.{u + 1} D sU hU k γ) :
    properCyclePushforward D sP hP sX hX hπB hp.2.1.2 k
        (firstChernCapPowCycleMap D sP hP L hL n k
          (flatPullbackMap D sP hP sX hX π hπB n hflat hrel k (k + n) rfl
            (integralCycle D sX k (IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint)
              hk))) =
      integralCycle D sX k (IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint) hk := by
  set T := IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint
  have hjf := isFlat_and_hasRelativeDimension_zero_of_isOpenImmersion' D sX hX hj
  have hj'f := isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sP hP sU hU sX hX hj'B hjB
    sq 0 hjf.1 hjf.2
  have hπUf := isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB hπB
    sq.flip n hflat hrel
  set ρ := flatPullbackMap D sU hU sX hX j hjB 0 hjf.1 hjf.2 k k (by simp)
  set z := properCyclePushforward D sP hP sX hX hπB hp.2.1.2 k
    (firstChernCapPowCycleMap D sP hP L hL n k
      (flatPullbackMap D sP hP sX hX π hπB n hflat hrel k (k + n) rfl (integralCycle D sX k T hk)))
  have hz : z = (z.1 T) • integralCycle D sX k T hk :=
    properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_integralCycle D sX hX sP hP π
      hπB hp.2.1.2 n hflat hrel L hL k T hk
  have hbc := flatPullback_properPushforward_unconditional D sPU hPU sP hP sU hU sX hX hj'B hπUB hπB
    hjB 0 hjf.1 hjf.2 sq hp k k (by simp)
      (firstChernCapPowCycleMap D sP hP L hL n k
        (flatPullbackMap D sP hP sX hX π hπB n hflat hrel k (k + n) rfl
          (integralCycle D sX k T hk)))
  have hcap := chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap_modulePullback
      D sPU hPU sP hP j' hj'B 0
    hj'f.2.1 hj'f.2.2 L hL n k k (by simp) (by simp)
    (flatPullbackMap D sP hP sX hX π hπB n hflat hrel k (k + n) rfl (integralCycle D sX k T hk))
  have hpull : flatPullbackMap D sPU hPU sP hP j' hj'B 0 hj'f.2.1 hj'f.2.2 (k + n) (k + n) (by simp)
      (flatPullbackMap D sP hP sX hX π hπB n hflat hrel k (k + n) rfl (integralCycle D sX k T hk)) =
      flatPullbackMap D sPU hPU sU hU πU hπUB n hπUf.2.1 hπUf.2.2 k (k + n) rfl
        (ρ (integralCycle D sX k T hk)) := by
    refine Subtype.ext ?_
    have h1 := congrArg (fun φ => (φ (integralCycle D sX k T hk)).1)
      (flatPullbackMap_comp D sPU hPU sP hP sX hX j' π hj'B hπB 0 n hj'f.2.1 hj'f.2.2 hflat hrel k
        (k + n) (by push_cast; ring))
    have h2 := congrArg (fun φ => (φ (integralCycle D sX k T hk)).1)
      (flatPullbackMap_comp D sPU hPU sU hU sX hX πU j hπUB hjB n 0 hπUf.2.1 hπUf.2.2 hjf.1 hjf.2 k
        (k + n) (by push_cast; ring))
    simp only [AddMonoidHom.comp_apply] at h1 h2
    refine (Eq.trans ?_ h1.symm).trans ((flatPullbackMap_coe_congr D sPU hPU sX hX sq.w _ _
      (by lia) _ _ _ _ k (k + n) k (k + n) _ _ _ _ rfl).trans (Eq.trans h2 ?_))
    · exact coe_flatPullbackMap_congr D sP hP sPU hPU j' hj'B 0 hj'f.2.1 hj'f.2.2 (by simp) rfl _ _
        _ _ rfl
    · exact coe_flatPullbackMap_congr D sU hU sPU hPU πU hπUB n hπUf.2.1 hπUf.2.2 (by simp) rfl _ _
        _ _ rfl
  have hclass : chowClassCanonical.{u + 1} D sU hU k (ρ z) =
      chowClassCanonical.{u + 1} D sU hU k (ρ (integralCycle D sX k T hk)) := by
    rw [hbc, ← chowGroupCanonicalProperPushforward_chowClassCanonical.{u + 1} D sPU hPU sU hU hπUB
      (isProper_of_isPullback D.site D.base D.base_mem hPU.1 hP.1 hU.1 hX.1 sq hp), hcap,
      chowGroupCanonicalProperPushforward_chowClassCanonical, hpull]
    exact htop _
  have heq := eq_of_chowClassCanonical_eq_of_forall_deltaDimension_le D sU hU k
    (fun W => (deltaDimension_le_of_isOpenImmersion_of_isIntegralSpace D sX hX sU hU hj hjB hint
      W).trans hk.le) hclass
  obtain ⟨W, hW⟩ := exists_closureImage_eq_top_of_isOpenImmersion D sX hX sU hU hj hint u₀
  have hρT : (ρ (integralCycle D sX k T hk)).1 W = 1 := by
    rw [flatPullbackMap_eq_cycleGroupRestrict D sX hX sU hU hj hjB k k (by simp),
      cycleGroupRestrict_apply, hW, integralCycle_coe, integralCycleCoeff_self]
  have hd : z.1 T = 1 := by
    have h := congrArg (fun c : CycleGroup D sU k => c.1 W) heq
    rw [hz, map_zsmul] at h
    change z.1 T * (ρ (integralCycle D sX k T hk)).1 W = _ at h
    rwa [hρT, mul_one] at h
  rw [hz, hd, one_smul]

end Open

end AlgebraicGeometry.Space

end
