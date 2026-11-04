module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionWeilDivisor

/-!
# Stacks 0EQR: flat pullback commutes with the cap product with a first Chern class

In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be flat of relative dimension `r`,
let `ℒ` be an invertible `𝒪_Y`-module and let `α` be a `(k+1)`-cycle on `Y`.  **Stacks 0EQR** is

  `f^*(c₁(ℒ) ∩ α) = c₁(f^*ℒ) ∩ f^*α`   in `CH_{k+r}(X)`.

All the objects are the constructed ones: the Chow groups of Stacks 0EQ6 at the canonical
embeddings of Stacks 0ENK (`chowGroupCanonical`), the cap product of Stacks 0EQJ
(`canonicalFirstChernCapCanonical`, the component cycle at `W` being `div_{ℒ|_W}(s_W)` of Stacks
0EQE for the section `s_W` of `ℒ|_W` that Stacks 0EPQ provides), the flat pullback of cycles of
Stacks 0EP8 (`flatPullbackMap`), the flat pullback on Chow groups of Stacks 0EQB
(`flatPullbackChowMapCanonical`) and the inverse image `f^*ℒ` of Stacks 03LU (`modulePullback`).

## Proof

As in the source.  For an integral closed subspace `W ⊆ Y` of δ-dimension `k + 1` let
`h : W' = f^{-1}(W) ⟶ W` be the projection, flat of relative dimension `r`.  Stacks 0EQQ for `h`
(`flatPullbackMap_sectionWeilDivisor_eq_componentDivisorSum`) gives
`h^* div_{ℒ|_W}(s_W) = ∑ n_i div(s_i)` over the components `W'_i` of `W'` of δ-dimension
`k + r + 1`; pushing it to `X` (Stacks 0EPD at the inverse image) the left side becomes
`f^*(c₁(ℒ) ∩ [W])` and the right side differs from `c₁(f^*ℒ) ∩ f^*[W]` component by component by
principal divisors (Stacks 0EPT after transporting `s_i` to the image of `W'_i` in `X`).  The
general cycle follows by Remark 0EQ8, at the canonical embeddings.  The three steps are
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapTransport`,
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapPreimage` and
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapAssembly`.

## Main results

* `AlgebraicGeometry.Space.flatPullbackChowMapCanonical_canonicalFirstChernCapCanonical`:
  **Stacks 0EQR**.
* `AlgebraicGeometry.Space.chowClassCanonical_flatPullbackMap_firstChernCapCycleMap`: the same,
  read at the cycle representing `c₁(ℒ) ∩ α`.

## References

* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
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
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (k : ℤ) (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hW : deltaDimension D sY W = k + 1)

/-- The section of `ℒ|_W` chosen by the cap product of Stacks 0EQJ is nonzero. -/
theorem componentMeromorphicSection_ne_zero_of_isGood :
    componentMeromorphicSection sY hY (subspaceDivisorSetupOfIsGood D sY hY) L hL W ≠ 0 :=
  (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem W.isClosedSubspace.1
    W.isIntegralSpace
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
      (isGood_integralClosedSubspace D sY hY W))
    _ (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL W) _).mp
    (isRegularMeromorphicSection_componentMeromorphicSection sY hY
      (subspaceDivisorSetupOfIsGood D sY hY) L hL W)

include hW in
/-- The δ-dimension of `W`, read on `W`. -/
theorem deltaDimensionClosed_integralClosedSubspace_of_eq :
    deltaDimensionClosed D (W.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
  rw [deltaDimensionClosed_univ_integralClosedSubspace D sY hY W, hW]

/-- **The per-subspace step of Stacks 0EQR.**  For an integral closed subspace `W ⊆ Y` of
δ-dimension `k + 1` and `a : ℤ`, the cycle `a · (f^*(c₁(ℒ) ∩ [W]) - c₁(f^*ℒ) ∩ f^*[W])` is
rationally equivalent to zero, at the canonical embeddings, inside `f^{-1}(|W|)`.  The expansion it
needs is Stacks 0EQQ for the projection `h : f^{-1}(W) ⟶ W`,
`flatPullbackMap_sectionWeilDivisor_eq_componentDivisorSum`, applied to the section of `ℒ|_W`
chosen by the cap product. -/
theorem isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect
    (a : ℤ) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sX hX (k + (r : ℤ))
      (a • flatChernDefect D sX hX sY hY f hbase r hflat hr k
        (canonicalFirstChernRule D sY hY L hL k)
        (canonicalFirstChernRule D sX hX
          ((modulePullback D.site D.base D.base_mem
            (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨Y, hY.1⟩)).obj L)
          (modulePullbackInvertible
            (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨Y, hY.1⟩) L hL) (k + (r : ℤ))) W hW)
      (pointsMap D.site D.base D.base_mem X f ⁻¹'
        subspacePointSet D.site D.base D.base_mem Y W.subspace) := by
  classical
  have hLW := isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL W
  have hP := isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W
  have hW' := isGood_integralClosedSubspace D sY hY W
  have hfl := isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr W
  have hs := componentMeromorphicSection_ne_zero_of_isGood D sY hY L hL W
  refine isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect_of_finsum D sX hX sY hY
    f hbase r hflat hr W L hL k hW
    (J := topDimensionalComponents D ((W.subspace.preimage f).ι ≫ sX) (k + 1 + r))
    (fun j => j.1) Subtype.val_injective
    (fun j => spaceMultiplicity D (W.subspace.preimage f).toFunctor hP.1 j.1)
    (fun j => ?_) (fun T hT => ?_)
    (locallyFinite_topDimensionalComponents D ((W.subspace.preimage f).ι ≫ sX) hP _)
    (fun j => by rw [j.2.2]; ring)
    (fun j => componentMorphism D (W.subspace.ι ≫ sY) hW' (W.subspace.fromPreimage f) j.1)
    (fun j => by
      change (j.1.subspace.ι ≫ W.subspace.fromPreimage f) ≫ W.subspace.ι = _
      rw [Category.assoc, Subfunctor.fromPreimage_ι])
    (fun j => componentSection D ((W.subspace.preimage f).ι ≫ sX) hP (W.subspace.ι ≫ sY) hW'
      (W.subspace.fromPreimage f) hfl.1 W.isIntegralSpace
      (integralClosedSubspaceRestrict D sY hY L W)
      (componentMeromorphicSection sY hY (subspaceDivisorSetupOfIsGood D sY hY) L hL W) j.1 j.2.1)
    (fun j => (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem
      j.1.isClosedSubspace.1 j.1.isIntegralSpace
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
        (isGood_integralClosedSubspace D ((W.subspace.preimage f).ι ≫ sX) hP j.1))
      _ (modulePullbackInvertible
        (componentMorphism D (W.subspace.ι ≫ sY) hW' (W.subspace.fromPreimage f) j.1)
        (integralClosedSubspaceRestrict D sY hY L W) hLW) _).mpr
      (componentSection_ne_zero D ((W.subspace.preimage f).ι ≫ sX) hP (W.subspace.ι ≫ sY) hW'
        (W.subspace.fromPreimage f) hfl.1 W.isIntegralSpace
        (integralClosedSubspaceRestrict D sY hY L W) hLW.toAlgebraicGeometry
        (componentMeromorphicSection sY hY (subspaceDivisorSetupOfIsGood D sY hY) L hL W) hs j.1
        j.2.1))
    (fun Z => ?_) a
  · -- the multiplicities
    have hV : deltaDimension D sX (preimageComponentImage sX hX sY hY f W j.1) =
        deltaDimension D sY W + (r : ℤ) := by
      rw [deltaDimension_preimageComponentImage D sX hX sY hY f W j.1, j.2.2, hW]
    exact flatPullbackMult_preimageComponentImage_eq_geometricLength D sX hX sY hY f hbase r
      hflat hr W j.1 hV
  · -- every subspace occurring in `f^*[W]` is the image of a top-dimensional component
    by_cases hex : ∃ V, preimageComponentImage sX hX sY hY f W V = T
    · obtain ⟨V, rfl⟩ := hex
      have hd := deltaDimension_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W
        _ hT
      refine ⟨⟨V, mem_irreducibleComponents_of_deltaDimension_preimageComponentImage D sX hX sY hY
        f hbase r hflat hr W V hd, ?_⟩, rfl⟩
      rw [← deltaDimension_preimageComponentImage D sX hX sY hY f W V, hd, hW]
    · exact absurd (flatPullbackMult_eq_zero_of_forall_ne_preimageComponentImage D sX hX sY hY f
        hbase r hflat hr W T fun V hV => hex ⟨V, hV⟩) hT
  · -- the expansion of Stacks 0EQQ for `h`
    have h1 := congrArg (fun c => c.1 Z)
      (flatPullbackMap_sectionWeilDivisor_eq_componentDivisorSum D
        ((W.subspace.preimage f).ι ≫ sX) hP (W.subspace.ι ≫ sY) hW'
        (W.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase W) r hfl.1 hfl.2
        W.isIntegralSpace (deltaDimensionClosed_integralClosedSubspace_of_eq D sY hY k W hW)
        (integralClosedSubspaceRestrict D sY hY L W) hLW.toAlgebraicGeometry
        (componentMeromorphicSection sY hY (subspaceDivisorSetupOfIsGood D sY hY) L hL W) hs)
    simp only [flatPullbackMap_apply] at h1 ⊢
    refine h1.trans ?_
    unfold componentDivisorSum
    rw [cycleFamilySum_apply]
    refine finsum_congr fun j => ?_
    rw [map_zsmul, AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul]
    rfl

omit hW in
/-- **Stacks 0EQR, read at a representative of `c₁(ℒ) ∩ α`.**  For `f : X ⟶ Y` flat of relative
dimension `r` between good spaces over `B`, `ℒ` invertible on `Y` and `α ∈ Z_{k+1}(Y)`, the
classes in `CH_{k+r}(X)` of `f^*(c₁(ℒ) ∩ α)` and of `c₁(f^*ℒ) ∩ f^*α` agree, where
`c₁(ℒ) ∩ α` is represented by the cycle `∑_W α_W (i_W)_* div_{ℒ|_W}(s_W)` of Stacks 0EQJ.

The proof is the source's: the difference is the locally finite sum over the subspaces `W`
occurring in `α` of `α_W` times the defect at `W`, each rationally equivalent to zero inside
`f^{-1}(W)` (Stacks 0EQ8); the defect at `W` is computed from Stacks 0EQQ for the projection
`h : f^{-1}(W) ⟶ W` (`flatPullbackMap_sectionWeilDivisor_eq_componentDivisorSum`), Stacks 0EPD at
the inverse image, and Stacks 0EPT on each component of `f^{-1}(W)`. -/
theorem chowClassCanonical_flatPullbackMap_firstChernCapCycleMap (α : CycleGroup D sY (k + 1)) :
    chowClassCanonical.{u + 1} D sX hX (k + (r : ℤ))
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
          (firstChernCapCycleMap D sY hY k (canonicalFirstChernRule D sY hY L hL k) α)) =
      canonicalFirstChernCapCanonical.{u + 1} D sX hX
        ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨Y, hY.1⟩)).obj L)
        (modulePullbackInvertible
          (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨Y, hY.1⟩) L hL) (k + (r : ℤ))
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
          α) := by
  rw [canonicalFirstChernCapCanonical, AddMonoidHom.comp_apply,
    chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  exact isRationallyEquivalentToZeroCanonical_flatPullbackMap_firstChernCapCycleMap_sub D sX hX sY
    hY f hbase r hflat hr k _ _ (fun W hW a =>
      isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect D sX
        hX sY hY f hbase r hflat hr L hL k W hW a) α

omit hW in
/-- **Stacks 0EQR.**  In Situation 0EDT let `X, Y/B` be good, let `f : X ⟶ Y` be flat of relative
dimension `r`, let `ℒ` be an invertible `𝒪_Y`-module and let `α` be a `(k+1)`-cycle on `Y`.  Then

  `f^*(c₁(ℒ) ∩ α) = c₁(f^*ℒ) ∩ f^*α`

in `CH_{k+r}(X)`.  Here `c₁(ℒ) ∩ - : Z_{k+1}(Y) → CH_k(Y)` is the cap product of Stacks 0EQJ
(`canonicalFirstChernCapCanonical`) into the Chow group `CH_k(Y)` of Stacks 0EQ6 at the canonical
embeddings of Stacks 0ENK, `f^* : CH_k(Y) → CH_{k+r}(X)` is the flat pullback on Chow groups of
Stacks 0EQB (`flatPullbackChowMapCanonical`), `f^*α` is the flat pullback of cycles of Stacks 0EP8
(`flatPullbackMap`) and `f^*ℒ` is the inverse image of Stacks 03LU (`modulePullback`).  The
source's `k`-cycle and `CH_{k+r-1}` are this statement's `(k+1)`-cycle and `CH_{k+r}`. -/
@[stacks 0EQR]
theorem flatPullbackChowMapCanonical_canonicalFirstChernCapCanonical
    (α : CycleGroup D sY (k + 1)) :
    flatPullbackChowMapCanonical.{u + 1} D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
        (canonicalFirstChernCapCanonical.{u + 1} D sY hY L hL k α) =
      canonicalFirstChernCapCanonical.{u + 1} D sX hX
        ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨Y, hY.1⟩)).obj L)
        (modulePullbackInvertible
          (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨Y, hY.1⟩) L hL) (k + (r : ℤ))
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
          α) := by
  rw [canonicalFirstChernCapCanonical, AddMonoidHom.comp_apply,
    flatPullbackChowMapCanonical_chowClassCanonical]
  exact chowClassCanonical_flatPullbackMap_firstChernCapCycleMap D sX hX sY hY f hbase r hflat hr
    L hL k α

end AlgebraicGeometry.Space

end
