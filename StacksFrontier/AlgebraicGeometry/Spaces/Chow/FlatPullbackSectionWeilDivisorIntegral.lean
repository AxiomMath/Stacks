module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionWeilDivisorCoefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionChartOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.SectionWeilDivisorModuleIso

/-!
# The right-hand side of Stacks 0EQQ on an integral source

In Situation 0EDT let `X/B` and `Y/B` be good, `Y` integral of δ-dimension `n`, `f : X ⟶ Y`
flat of relative dimension `r`, `ℒ` invertible on `Y` and `s` a nonzero meromorphic section of
`ℒ`. The right-hand side of Stacks 0EQQ is the cycle
`∑ m_{X_i, X} (X_i → X)_* div_{f^*ℒ|_{X_i}}(s_i)`
(`AlgebraicGeometry.Space.componentDivisorSum`). When `X` itself is integral, of δ-dimension
`n + r`, this file shows that it is the divisor `div_{f^*ℒ}(f^*s)` of Stacks 0EQE of the pulled
back section on `X` itself, with `f^*s` the pullback of Stacks 0ENC.

## Main results

* `AlgebraicGeometry.Space.componentDivisorSum_eq_sectionWeilDivisor_of_isIntegralSpace`.

## Implementation notes

The identity is checked coefficientwise. At a prime divisor `Z` of `X` both coefficients are the
order of vanishing, in the stalk `𝒪_{U, u}` of an affine chart over the generic point of `Z`, of
the reading `φ(s / e)` of `s` against a free generator `e` of `ℒ` on an affine chart `V` of `Y`
under `U`: for the right-hand side of Stacks 0EQQ this is
`componentDivisorSum_apply_eq_ordTotalFracInt`, and for `div_{f^*ℒ}(f^*s)` it is
`orderOfVanishingSection_pullbackMeromorphicSection_eq_ordTotalFracInt_map`. At an integral closed
subspace which is not a prime divisor both coefficients vanish: the one of `div_{f^*ℒ}(f^*s)` by
definition, the other because a nonzero coefficient of an `(n + r - 1)`-cycle sits on a subspace of
δ-dimension `n + r - 1`, which on the integral `X` of δ-dimension `n + r` is a prime divisor
(Stacks 0EPZ).

## References

* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory

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
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (hL : IsInvertibleSheaf D sY hY L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L) (hs : s ≠ 0)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)

/-- `f` as a morphism of algebraic spaces. -/
abbrev flatPullbackSpaceHom :
    (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩ :=
  ObjectProperty.homMk f

include hbase hr hn in
/-- **The right-hand side of Stacks 0EQQ on an integral source is `div_{f^*ℒ}(f^*s)`.** If `X` is
integral of δ-dimension `n + r`, then

  `∑ m_{X_i, X} (X_i → X)_* div_{f^*ℒ|_{X_i}}(s_i) = div_{f^*ℒ}(f^*s)` in `Z_{n+r-1}(X)`. -/
theorem componentDivisorSum_eq_sectionWeilDivisor_of_isIntegralSpace
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((n + r : ℤ) : EInt)) :
    componentDivisorSum D sX hX sY hY f r hflat hintY L hL s hs =
      sectionWeilDivisor D sX hX hintX
        ((modulePullback D.site D.base D.base_mem (flatPullbackSpaceHom D sX hX sY hY f)).obj L)
        (isInvertibleSheaf_modulePullback D sY hY sX hX (flatPullbackSpaceHom D sX hX sY hY f) hL)
        hnX
        (pullbackMeromorphicSection D.site D.base D.base_mem
          (flatPullbackSpaceHom D sX hX sY hY f) L
          (pullbacksMeromorphicSections_of_flat D.site D.base D.base_mem f hflat) s)
        (pullbackMeromorphicSection_ne_zero_of_isFlat D sY hY hintY sX hX hintX
          (flatPullbackSpaceHom D sX hX sY hY f) hflat hL s hs) := by
  have hNX := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  let := (genericFractionEmbedding D.site D.base D.base_mem hX.1 hintX.2.1 hintX hNX).nontrivial
  let :=
    (genericFractionEmbedding D.site D.base D.base_mem hX.1 hintX.2.1 hintX hNX).isNoetherianRing
  let := (genericFractionEmbedding D.site D.base D.base_mem hX.1 hintX.2.1 hintX hNX).krullDimLE
  obtain ⟨dX, hdX⟩ := exists_dimensionFunction_deltaValue_of_isGood D sX hX
  have hinv := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  refine Subtype.ext (funext fun Z => ?_)
  show _ = divisorCycleCoefficients D sX hX hintX.2.1 _ _ _ Z
  have htfae := fun Z => (isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hintX dX hdX hnX Z).out 2 3
  by_cases hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1
  · rw [divisorCycleCoefficients_of_codimension_eq_one D sX hX hintX.2.1 _ _ _ hcod]
    have hZd : deltaDimension D sX Z = n + r - 1 := (htfae Z).mp hcod
    set P := Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod with hP
    have hPgen : P.genericPoint D.site D.base D.base_mem X =
        Z.ambientGenericPoint D.site D.base D.base_mem := by
      rw [PrimeDivisor.genericPoint_eq_ambientGenericPoint D hX.1 P,
        IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor]
    obtain ⟨d, u, hU, hV, hu, e, hecompat, hebij⟩ :=
      exists_affine_chartDiagram_generator_through D.site D.base D.base_mem
        (flatPullbackSpaceHom D sX hX sY hY f) L hL (P.genericPoint D.site D.base D.base_mem X)
    have : IsLocallyNoetherian (chartScheme d.U) :=
      (exists_atlas_iff_forall_etale D.site D.base D.base_mem X
        (fun W : Scheme.{u} => IsLocallyNoetherian W) hX.1).mp hNX d.U.obj.left d.U.obj.hom
        d.U.property
    have : Ring.KrullDimLE 1 ((chartScheme d.U).presheaf.stalk u) :=
      P.krullDimLE_chartStalk D.site D.base D.base_mem hX.1 hintX.2.1 d.U u hu
    have hdimA : ringKrullDim ((chartScheme d.U).presheaf.stalk u) = 1 :=
      P.ringKrullDim_chartStalk D.site D.base D.base_mem hX.1 hintX.2.1 d.U u hu
    rw [componentDivisorSum_apply_eq_ordTotalFracInt D sX hX sY hY f hbase r hflat hr hintY hn L hL
      s hs Z hZd d hU hV e hecompat hebij u (hu.trans hPgen) hdimA]
    have hreg : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L s :=
      (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hY.1 hintY
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) L
        hinv s).mpr hs
    obtain ⟨hc, hord⟩ := orderOfVanishingSection_pullbackMeromorphicSection_eq_ordTotalFracInt_map
      D.site D.base D.base_mem hintX.2.1 hintX hNX (flatPullbackSpaceHom D sX hX sY hY f)
      (pullbacksMeromorphicSections_of_flat D.site D.base D.base_mem f hflat)
      (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isGood D sY hY hintY)
      (hasLocallyFiniteIrreducibleComponents_of_isGood D sY hY) P L
      hinv s hreg d hU hV e hecompat
      hebij u hu (nonZeroDivisors_le_comap_stalkMap_of_isFlat D f hflat d u)
    exact (hord.trans (Ring.ordTotalFracInt_congr _ _ _ rfl)).symm
  · rw [divisorCycleCoefficients_of_codimension_ne_one D sX hX hintX.2.1 _ _ _ hcod]
    by_contra hne
    exact hcod ((htfae Z).mpr
      (((componentDivisorSum D sX hX sY hY f r hflat hintY L hL s hs).2).2 Z hne))

end AlgebraicGeometry.Space

end
