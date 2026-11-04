module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapCanonical

/-!
# Stacks 0ER6 at an integral closed subspace contained in the divisor

In Situation 0EDT let `f : X' ⟶ X` be flat of relative dimension `r` between good algebraic
spaces over `B`, let `(ℒ, s, i : E → X)` be as in Definition 0ER1 and let `W ⊆ X` be an integral
closed subspace of δ-dimension `k + 1` contained in `E`.  The source's second case of the proof
of Stacks 0ER6: `f^{-1}(W) ⊆ E'` and the identity at `[W]` is Stacks 0EQR.  Here, on `X'`, the
defect at `W` of the cap products of the two Gysin rules (`sectionGysinChernRule`,
`gysinPullbackChernRule`) is rationally equivalent to zero inside `f^{-1}(|W|)`.

The Gysin rules differ from the canonical cap products of Stacks 0EQJ by principal divisors: on
`W` (and on each subspace of `X'` occurring in `f^*[W]`, all of which lie in `E'`) both are Weil
divisors of regular meromorphic sections of the restricted invertible module, which differ by a
principal divisor (Stacks 0EPT).  So the defect is the defect at the canonical rules, which is
Stacks 0EQR at one integral closed subspace
(`AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect`),
plus the flat pullback of a principal divisor on `W` (Stacks 0EQA, read inside `f^{-1}(|W|)`),
minus a difference of cap products by rules differing by principal divisors inside `f^{-1}(|W|)`.

## Main results

* `isRationallyEquivalentToZeroWithinCanonical_flatPullbackMap_pushforward_of_principal`:
  `f^*(i_{V,*} div(φ))` is rationally equivalent to zero inside `f^{-1}(|V|)`.
* `flatChernDefect_eq_add_sub`: how the defect changes with the rules.
* `isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect_gysin_of_le`:
  the case `W ⊆ D` of Stacks 0ER6.

## References

* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Principal

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- The flat pullback of the pushforward of a principal divisor on an integral closed subspace
`V ⊆ Y` is rationally equivalent to zero within `f^{-1}(|V|)`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_flatPullbackMap_pushforward_of_principal
    (m n : ℤ) (hmn : m + (r : ℤ) = n) (V : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hV : deltaDimension D sY V = m + 1) (d : CycleGroup D (V.subspace.ι ≫ sY) m)
    (hd : IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ sY)
      (isGood_integralClosedSubspace D sY hY V) V.isIntegralSpace m d) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sX hX n
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
        (integralClosedSubspacePushforward D sY hY V m d))
      (pointsMap D.site D.base D.base_mem X f ⁻¹'
        subspacePointSet D.site D.base D.base_mem Y V.subspace) := by
  refine isRationallyEquivalentToZeroWithinCanonical_flatPullbackMap_pushforward D sX hX sY hY f
    hbase r hflat hr m n hmn V d ?_
  have hk : deltaDimensionClosed D (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
      Set.univ isClosed_univ = ((m + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sY hY V, hV]
  obtain ⟨g, hg⟩ := hd.exists_eq_rationalFunctionPrincipalDivisorCycle D hk
  have hV'good := isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V
  have hpr := isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V
  exact isRationallyEquivalentToZeroCanonical_flatPullbackMap_of_eq_finsum_components D
    ((V.subspace.preimage f).ι ≫ sX) hV'good (V.subspace.ι ≫ sY)
    (isGood_integralClosedSubspace D sY hY V) (V.subspace.fromPreimage f)
    (fromPreimage_comp_ι_comp D sX sY f hbase V) r hpr.1 hpr.2 V.isIntegralSpace hk g
    (fun W => spaceMultiplicity D (V.subspace.preimage f).toFunctor hV'good.1 W.1)
    (fun W => W.deltaDimensionClosed_univ_of_isFlat D ((V.subspace.preimage f).ι ≫ sX) hV'good
      (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
      (V.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase V) r hpr.2 hpr.1
      V.isIntegralSpace hk)
    (fun W => W.flatPullbackRationalFunction D ((V.subspace.preimage f).ι ≫ sX) hV'good
      (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
      (V.subspace.fromPreimage f) hpr.1 V.isIntegralSpace g) _
    (flatPullbackMap_rationalFunctionPrincipalDivisorCycle_eq_finsum_components D
      ((V.subspace.preimage f).ι ≫ sX) hV'good (V.subspace.ι ≫ sY)
      (isGood_integralClosedSubspace D sY hY V) (V.subspace.fromPreimage f)
      (fromPreimage_comp_ι_comp D sX sY f hbase V) r hpr.2 hpr.1 V.isIntegralSpace hk g)
    m n hmn rfl d hg

variable (k : ℤ) (chernY chernY' : FirstChernComponentCycleRule D sY k)
    (chernX chernX' : FirstChernComponentCycleRule D sX (k + (r : ℤ)))

/-- The defect at `W` changes, when both component rules change, by the flat pullback of the
change on `W` minus the change of the cap product on `f^*[W]`. -/
theorem flatChernDefect_eq_add_sub (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hW : deltaDimension D sY W = k + 1) :
    flatChernDefect D sX hX sY hY f hbase r hflat hr k chernY chernX W hW =
      flatChernDefect D sX hX sY hY f hbase r hflat hr k chernY' chernX' W hW +
        flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
          (integralClosedSubspacePushforward D sY hY W k (chernY W hW - chernY' W hW)) -
        (firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX
            (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
              (integralCycle D sY (k + 1) W hW)) -
          firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX'
            (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
              (integralCycle D sY (k + 1) W hW))) := by
  simp only [flatChernDefect, firstChernComponentCycle_of_deltaDimension_eq D sY hY k _ hW,
    map_sub]
  abel

end Principal

section Restricted

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (hL : IsInvertibleSheaf D p hp L)
    (k : ℤ)

/-- The component cycle `c₁(ℒ|_W) ∩ [W]` of Stacks 0ER1(1)(b) differs from the one of the cap
product at the canonical choices by a principal divisor. -/
theorem isPrincipalDivisorCycleOfGood_restrictedDivisorCycle_sub_canonicalFirstChernRule
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D p W = k + 1) :
    IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
      W.isIntegralSpace k
      (restrictedDivisorCycle D p hp L k hL W hW - canonicalFirstChernRule D p hp L hL k W hW) :=
  have hWg := isGood_integralClosedSubspace D p hp W
  have hLW := isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W
  isPrincipalDivisorCycleOfGood_canonicalDivisorCycleAt_sub D _ hWg W.isIntegralSpace _ hLW _ _
    (isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem hWg.1
      W.isIntegralSpace (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hWg) _ hLW)
    (isRegularMeromorphicSection_componentMeromorphicSection p hp
      (subspaceDivisorSetupOfIsGood D p hp) L hL W) _

end Restricted

section Contained

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hfbase : f.hom ≫ p = p') (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f.hom)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)

/-- **Stacks 0ER6, the case `W ⊆ D`.**  For an integral closed subspace `W ⊆ E` of δ-dimension
`k + 1`, every integer multiple of the defect at `W` of the two Gysin rules is rationally
equivalent to zero, at the canonical embeddings, inside `f^{-1}(|W|)`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect_gysin_of_le
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D p W = k + 1)
    (hWE : W.subspace ≤ (vanishingLocus D p hp L s).1) (a : ℤ) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D p' hp' (k + (r : ℤ))
      (a • flatChernDefect D p' hp' p hp f.hom hfbase r hflat hr k
        (sectionGysinChernRule D p hp L s hL k) (gysinPullbackChernRule D p hp p' hp' f r L s hL k)
        W hW)
      (pointsMap D.site D.base D.base_mem X' f.hom ⁻¹'
        subspacePointSet D.site D.base D.base_mem X W.subspace) := by
  classical
  have hL' := isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL
  set c' := canonicalFirstChernRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
    (modulePullbackInvertible f L (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL))
    (k + (r : ℤ))
  rw [flatChernDefect_eq_add_sub D p' hp' p hp f.hom hfbase r hflat hr k _
    (canonicalFirstChernRule D p hp L hL k) _ c' W hW,
    smul_sub, smul_add]
  refine IsRationallyEquivalentToZeroWithinCanonical.sub
    (IsRationallyEquivalentToZeroWithinCanonical.add ?_ ?_) ?_
  · exact isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect D p' hp' p hp f.hom
      hfbase r hflat hr L hL k W hW a
  · rw [← map_zsmul, ← map_zsmul]
    refine isRationallyEquivalentToZeroWithinCanonical_flatPullbackMap_pushforward_of_principal D
      p' hp' p hp f.hom hfbase r hflat hr k (k + (r : ℤ)) rfl W hW _
      (isPrincipalDivisorCycleOfGood_zsmul D _ _ _ k ?_ a)
    rw [sectionGysinChernRule, restrictedSectionChernRule_of_le D p hp L s hL k _ hW hWE]
    exact isPrincipalDivisorCycleOfGood_restrictedDivisorCycle_sub_canonicalFirstChernRule D p hp
      L hL k W hW
  · rw [smul_sub, ← map_zsmul (firstChernCapCycleMap D p' hp' (k + (r : ℤ))
        (gysinPullbackChernRule D p hp p' hp' f r L s hL k)),
      ← map_zsmul (firstChernCapCycleMap D p' hp' (k + (r : ℤ)) c')]
    refine isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_sub D p' hp'
      (k + (r : ℤ)) _ _ _ _ fun T hT hβ _ => ?_
    have hμ : flatPullbackMult D p' hp' p hp f.hom hfbase r hflat hr W T ≠ 0 := by
      intro h0
      apply hβ
      rw [AddSubgroup.coe_zsmul, Pi.smul_apply, flatPullbackMap_integralCycle, h0, smul_zero]
    have hsub := subspacePointSet_subset_of_flatPullbackMult_ne_zero D p' hp' p hp f.hom hfbase r
      hflat hr W T hμ
    refine ⟨?_, hsub⟩
    have hTE : T.subspace ≤ (pullbackSectionVanishingLocus D p hp p' hp' f L s).1 := by
      refine le_of_subspacePointSet_subset_of_integral D hp'.1 _
        (pullbackSectionVanishingLocus D p hp p' hp' f L s).2 T ?_
      rw [pullbackVanishingLocus_eq_preimage D p hp p' hp' f L s hL, subspacePointSet_preimage]
      exact hsub.trans (Set.preimage_mono (subspacePointSet_mono_of_le D hWE))
    rw [gysinPullbackChernRule, sectionGysinChernRule,
      restrictedSectionChernRule_of_le D p' hp' _ _ hL' (k + (r : ℤ)) _ hT hTE]
    exact isPrincipalDivisorCycleOfGood_restrictedDivisorCycle_sub_canonicalFirstChernRule D p'
      hp' _ hL' (k + (r : ℤ)) T hT

end Contained

end AlgebraicGeometry.Space

end
