module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackOfGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardNonContained

/-!
# Stacks 0ER6 at an integral closed subspace not contained in the divisor

In Situation 0EDT let `f : X' ⟶ X` be flat of relative dimension `r` between good algebraic
spaces over `B`, let `(ℒ, s, i : E → X)` be as in Definition 0ER1 and let `W ⊆ X` be an integral
closed subspace of δ-dimension `k + 1` with `W ⊄ E`.  The source's first case of the proof of
Stacks 0ER6: `(i')^* f^* [W] = g^* i^* [W]` holds as cycles.  Read on `X'` through the
pushforwards along `i'` and `i`, this is the vanishing of the defect at `W`
(`AlgebraicGeometry.Space.flatChernDefect_gysinChernRule_eq_zero_of_not_le`).

## The proof

Off `E` the Gysin rule at `W` is the Weil divisor `div_{ℒ|_W}(s|_W)` of the restricted global
section, and the Gysin rule of `(f^*ℒ, f^*s)` at a subspace `V' ⊄ E'` is `div((f^*s)|_{V'})`
(`AlgebraicGeometry.Space.restrictedSectionChernRule`).  Stacks 0EQQ for the flat projection
`h : f^{-1}(W) ⟶ W` expands `h^* div_{ℒ|_W}(s|_W)` as `∑ m_V div(s_V)` over the components `V` of
`f^{-1}(W)` (`AlgebraicGeometry.Space.flatPullbackMap_gysinChernRule_apply_of_not_le`), with
`s_V` the pullback of `s|_W` along `V ⟶ W`.  The image `V'` of a component occurring in `f^*[W]`
is not contained in `E'` (its generic point lies over that of `W`), and the divisor of `s_V`,
transported to `V'`, is `div((f^*s)|_{V'})`
(`AlgebraicGeometry.Space.pushforwardCycleTransport_canonicalDivisorCycleAt_componentSection`):
both are the divisors of inverse images of `s` along the two factorizations
`V ⟶ W ⟶ X` and `V ≅ V' ⟶ X' ⟶ X` of one morphism
(`Space.canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_square`).
The multiplicities `m_V` are those of `f^*[W]`.  So the two sides agree term by term
(`AlgebraicGeometry.Space.flatChernDefect_eq_zero_of_finsum`).

## References

* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Exact

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)

/-- **The defect at `W` vanishes as soon as the expansion of `h^*(c₁ ∩ [W])` along the
components of `f^{-1}(W)` transports, term by term, to the component cycles of the rule on `X`.**
This is the exact form of
`Space.isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect_of_finsum`:
there each term is matched up to a principal divisor, here on the nose. -/
theorem flatChernDefect_eq_zero_of_finsum (k : ℤ) (chernY : FirstChernComponentCycleRule D sY k)
    (chernX : FirstChernComponentCycleRule D sX (k + (r : ℤ)))
    (hW : deltaDimension D sY W = k + 1) {J : Type (u + 1)}
    (V : J → IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hVinj : Function.Injective V) (n : J → ℤ)
    (hn : ∀ j, flatPullbackMult D sX hX sY hY f hbase r hflat hr W
      (preimageComponentImage sX hX sY hY f W (V j)) = n j)
    (hcover : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem X,
      flatPullbackMult D sX hX sY hY f hbase r hflat hr W T ≠ 0 →
        ∃ j, preimageComponentImage sX hX sY hY f W (V j) = T)
    (hVfin : LocallyFinite fun j =>
      subspacePointSet D.site D.base D.base_mem (W.subspace.preimage f).toFunctor (V j).subspace)
    (hVdim : ∀ j, deltaDimension D ((W.subspace.preimage f).ι ≫ sX) (V j) = k + (r : ℤ) + 1)
    (d : ∀ j, CycleGroup D ((V j).subspace.ι ≫ (W.subspace.preimage f).ι ≫ sX) (k + (r : ℤ)))
    (hsum : ∀ Z, (flatPullbackMap D ((W.subspace.preimage f).ι ≫ sX)
        (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W)
        (W.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W)
        (W.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase W) r
        (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr W).1
        (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr W).2
        k (k + (r : ℤ)) rfl (chernY W hW)).1 Z =
      ∑ᶠ j, n j *
        (integralClosedSubspacePushforward D ((W.subspace.preimage f).ι ≫ sX)
          (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) (V j) (k + (r : ℤ))
          (d j)).1 Z)
    (hd : ∀ j, n j ≠ 0 →
      IntegralClosedSubspace.pushforwardCycleTransport D sX hX
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).1
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).2 (V j)
          (k + (r : ℤ)) (d j) =
        chernX (preimageComponentImage sX hX sY hY f W (V j))
          ((deltaDimension_preimageComponentImage D sX hX sY hY f W (V j)).trans (hVdim j))) :
    flatChernDefect D sX hX sY hY f hbase r hflat hr k chernY chernX W hW = 0 := by
  classical
  have hP := isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W
  have hdec := D.isDecentSpace_of_isGood sX hX
  let V' : J → IntegralClosedSubspace D.site D.base D.base_mem X := fun j =>
    preimageComponentImage sX hX sY hY f W (V j)
  have hdim : ∀ j, deltaDimension D sX (V' j) = k + (r : ℤ) + 1 := fun j =>
    (deltaDimension_preimageComponentImage D sX hX sY hY f W (V j)).trans (hVdim j)
  have hfin : LocallyFinite fun j => subspacePointSet D.site D.base D.base_mem X (V' j).subspace :=
    locallyFinite_subspacePointSet_pushforward D.site D.base D.base_mem hX.1 hP.1 hdec hP.2 V hVfin
  refine Subtype.ext (funext fun T => ?_)
  have hA : (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
      (firstChernComponentCycle D sY hY k chernY W)).1 T =
      ∑ᶠ j, n j *
        (integralClosedSubspacePushforward D sX hX (V' j) (k + (r : ℤ))
          (IntegralClosedSubspace.pushforwardCycleTransport D sX hX hP.1 hP.2 (V j) (k + (r : ℤ))
            (d j))).1 T := by
    rw [firstChernComponentCycle_of_deltaDimension_eq D sY hY k _ hW,
      flatPullbackMap_integralClosedSubspacePushforward_eq_closedPushforward D sX hX sY hY f hbase r
        hflat hr W k (k + (r : ℤ)) rfl]
    change cycleClosedPushforward D hX.1 hP.1 hdec hP.2 _ T = _
    rw [cycleClosedPushforward_apply_of_eq_finsum D hX.1 hP.1 hdec hP.2 n
      (fun j => (integralClosedSubspacePushforward D _
        (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) (V j) (k + (r : ℤ))
          (d j)).1) _ hsum T]
    exact finsum_congr fun j => by
      rw [integralClosedSubspacePushforward_preimageComponentImage_coe]
  have hB : (firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
        (integralCycle D sY (k + 1) W hW))).1 T =
      ∑ᶠ j, n j * (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX (V' j)).1 T := by
    rw [firstChernCapCycleMap_apply]
    rw [finsum_congr fun T' => by
      rw [flatPullbackMap_integralCycle D sX hX sY hY f hbase r hflat hr (k + 1)
        (k + (r : ℤ) + 1) (by ring) W hW T']]
    have hinj : Function.Injective V' := fun j j' hjj' => hVinj
      (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1 hP.1 hdec hP.2
        hjj')
    rw [← finsum_mem_univ, ← finsum_mem_inter_support_eq' _ (Set.range V') Set.univ ?_,
      finsum_mem_range hinj]
    · exact finsum_congr fun j => by rw [hn j]
    · intro T' hT'
      simp only [Set.mem_univ, iff_true]
      obtain ⟨j, hj⟩ := hcover T' (left_ne_zero_of_mul hT')
      exact ⟨j, hj⟩
  have hξ : T.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X T.subspace :=
    ⟨T.genericPoint D.site D.base D.base_mem, rfl⟩
  have hfx : (Function.support fun j => n j *
      (integralClosedSubspacePushforward D sX hX (V' j) (k + (r : ℤ))
        (IntegralClosedSubspace.pushforwardCycleTransport D sX hX hP.1 hP.2 (V j) (k + (r : ℤ))
          (d j))).1 T).Finite :=
    (hfin.point_finite (T.ambientGenericPoint D.site D.base D.base_mem)).subset fun j hj =>
      subspacePointSet_subset_of_pushforward_ne_zero D sX hX (V' j) (k + (r : ℤ)) _ T
        (right_ne_zero_of_mul hj) hξ
  have hfy : (Function.support fun j => n j *
      (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX (V' j)).1 T).Finite :=
    (hfin.point_finite (T.ambientGenericPoint D.site D.base D.base_mem)).subset fun j hj =>
      subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX (k + (r : ℤ)) _ (V' j) T
        (right_ne_zero_of_mul hj) hξ
  change (flatChernDefect D sX hX sY hY f hbase r hflat hr k chernY chernX W hW).1 T = 0
  rw [flatChernDefect, AddSubgroup.coe_sub, Pi.sub_apply, hA, hB, ← finsum_sub_distrib hfx hfy]
  refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
  by_cases hj : n j = 0
  · rw [hj, zero_mul, zero_mul, sub_zero]
  · rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX (k + (r : ℤ)) _ (hdim j), hd j hj,
      sub_self]

end Exact

section Regular

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)

/-- Regularity of the meromorphic section of a global section is transported along an isomorphism
of modules carrying one global section to the other. -/
private theorem isRegularMeromorphicSection_globalSectionMeromorphic_of_sectionsMap_eq
    {M N : Modules.{u, u} D.site D.base D.base_mem Y hY} (e : M ≅ N) (σ : M.sections)
    (τ : N.sections) (hστ : SheafOfModules.sectionsMap e.hom σ = τ)
    (h : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY _
      (globalSectionMeromorphic D.site D.base D.base_mem hY _ σ)) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY _
      (globalSectionMeromorphic D.site D.base D.base_mem hY _ τ) := by
  have h' := isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem Y hY e _ h
  have key := sectionsMap_meromorphicSectionSheafMap_globalSectionMeromorphic D.site D.base
    D.base_mem hY e.hom σ
  rw [meromorphicSectionSheafMapIso_hom] at h'
  rw [hστ] at key
  exact key ▸ h'

/-- Regularity of the meromorphic section of an iterated pullback of a global section passes to
the pullback along the composite. -/
theorem isRegularMeromorphicSection_globalSectionMeromorphic_modulePullbackSections_comp
    {Z Z' : AlgebraicSpaces D.site D.base D.base_mem} (a : (⟨Y, hY⟩ : AlgebraicSpaces _ _ _) ⟶ Z)
    (b : Z ⟶ Z') (L : Modules.{u, u} D.site D.base D.base_mem Z'.1 Z'.2) (σ : L.sections)
    (h : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY _
      (globalSectionMeromorphic D.site D.base D.base_mem hY _
        (modulePullbackSections D.site D.base D.base_mem a _
          (modulePullbackSections D.site D.base D.base_mem b L σ)))) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY _
      (globalSectionMeromorphic D.site D.base D.base_mem hY _
        (modulePullbackSections D.site D.base D.base_mem (a ≫ b) L σ)) :=
  isRegularMeromorphicSection_globalSectionMeromorphic_of_sectionsMap_eq D hY
    ((modulePullbackCompIso D.site D.base D.base_mem a b).app L) _ _
    (by rw [Iso.app_hom, sectionsMap_modulePullbackCompIso_modulePullbackSections]) h

/-- Regularity of the meromorphic section of the pullback of a global section along a composite
passes to the iterated pullback. -/
theorem isRegularMeromorphicSection_globalSectionMeromorphic_modulePullbackSections_of_comp
    {Z Z' : AlgebraicSpaces D.site D.base D.base_mem} (a : (⟨Y, hY⟩ : AlgebraicSpaces _ _ _) ⟶ Z)
    (b : Z ⟶ Z') (L : Modules.{u, u} D.site D.base D.base_mem Z'.1 Z'.2) (σ : L.sections)
    (h : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY _
      (globalSectionMeromorphic D.site D.base D.base_mem hY _
        (modulePullbackSections D.site D.base D.base_mem (a ≫ b) L σ))) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY _
      (globalSectionMeromorphic D.site D.base D.base_mem hY _
        (modulePullbackSections D.site D.base D.base_mem a _
          (modulePullbackSections D.site D.base D.base_mem b L σ))) :=
  isRegularMeromorphicSection_globalSectionMeromorphic_of_sectionsMap_eq D hY
    ((modulePullbackCompIso D.site D.base D.base_mem a b).app L).symm _ _
    (by rw [Iso.symm_hom, Iso.app_inv,
      sectionsMap_modulePullbackCompIso_inv_modulePullbackSections]) h

end Regular

section Square

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sY : Y ⟶ D.space}
    (hY : D.IsGood sY) (hint : IsIntegralSpace D.site D.base D.base_mem Y)

/-- **The Weil divisor of a global section pulled back along two factorizations of one
morphism.**  For `a ≫ b = (a' ≫ b') ≫ c`, the divisors on `Y` of `a^*(b^*σ)` and of
`a'^*(b'^*(c^*σ))` agree: both are the divisor of the pullback of `σ` along the common composite
(Stacks 03LU). -/
theorem canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_square
    {B B' C C' : AlgebraicSpaces D.site D.base D.base_mem}
    (a : (⟨Y, hY.1⟩ : AlgebraicSpaces _ _ _) ⟶ B) (b : B ⟶ C)
    (a' : (⟨Y, hY.1⟩ : AlgebraicSpaces _ _ _) ⟶ B') (b' : B' ⟶ C') (c : C' ⟶ C)
    (w : a ≫ b = (a' ≫ b') ≫ c) (L : Modules.{u, u} D.site D.base D.base_mem C.1 C.2)
    (hL : IsInvertibleModule (B := D.site) C L) (σ : L.sections)
    (h1 : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
        (modulePullbackSections D.site D.base D.base_mem a _
          (modulePullbackSections D.site D.base D.base_mem b L σ))))
    (h5 : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
        (modulePullbackSections D.site D.base D.base_mem a' _
          (modulePullbackSections D.site D.base D.base_mem b' _
            (modulePullbackSections D.site D.base D.base_mem c L σ)))))
    {k : ℤ} (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    canonicalDivisorCycleAt D sY hY hint _
        (modulePullbackInvertible a _ (modulePullbackInvertible b L hL))
        (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
          (modulePullbackSections D.site D.base D.base_mem a _
            (modulePullbackSections D.site D.base D.base_mem b L σ))) h1 hk =
      canonicalDivisorCycleAt D sY hY hint _
        (modulePullbackInvertible a' _ (modulePullbackInvertible b' _
          (modulePullbackInvertible c L hL)))
        (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
          (modulePullbackSections D.site D.base D.base_mem a' _
            (modulePullbackSections D.site D.base D.base_mem b' _
              (modulePullbackSections D.site D.base D.base_mem c L σ)))) h5 hk := by
  have h2 := isRegularMeromorphicSection_globalSectionMeromorphic_modulePullbackSections_comp D
    hY.1 a b L σ h1
  have h4 := isRegularMeromorphicSection_globalSectionMeromorphic_modulePullbackSections_comp D
    hY.1 a' b' _ (modulePullbackSections D.site D.base D.base_mem c L σ) h5
  have h3 := isRegularMeromorphicSection_globalSectionMeromorphic_modulePullbackSections_comp D
    hY.1 (a' ≫ b') c L σ h4
  refine (canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_comp D hY hint
    a b L σ _ (modulePullbackInvertible (a ≫ b) L hL) h1 h2 hk).trans ?_
  refine (canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_congr D hY hint
    w L σ _ (modulePullbackInvertible ((a' ≫ b') ≫ c) L hL) h2 h3 hk).trans ?_
  refine (canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_comp D hY hint
    (a' ≫ b') c L σ (modulePullbackInvertible (a' ≫ b') _ (modulePullbackInvertible c L hL)) _
    h4 h3 hk).symm.trans ?_
  exact (canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_comp D hY hint
    a' b' _ (modulePullbackSections D.site D.base D.base_mem c L σ) _ _ h5 h4 hk).symm

end Square

section Component

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hfbase : f.hom ≫ p = p') (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f.hom)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f.hom).toFunctor)

/-- The two routes `V ⟶ X` around the square of Remark 0ER3 at a component `V` of `f^{-1}(W)`:
through `W` and through the image `V'` of `V` in `X'`. -/
theorem componentMorphism_comp_closedSubspaceInclusion :
    componentMorphism D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
        (W.subspace.fromPreimage f.hom) V ≫
      closedSubspaceInclusion D.site D.base D.base_mem ⟨X, hp.1⟩
        ⟨W.subspace, W.isClosedSubspace⟩ =
    ((algebraicSpacesIsoOfIso D.site D.base D.base_mem V.isClosedSubspace.1
        (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1
        (preimageComponentIso p' hp' p hp f.hom W V)).hom ≫
      closedSubspaceInclusion D.site D.base D.base_mem ⟨X', hp'.1⟩
        ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace,
          (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace⟩) ≫ f := by
  refine ObjectProperty.hom_ext _ ?_
  change (V.subspace.ι ≫ W.subspace.fromPreimage f.hom) ≫ W.subspace.ι =
    ((preimageComponentIso p' hp' p hp f.hom W V).hom ≫
      (preimageComponentImage p' hp' p hp f.hom W V).subspace.ι) ≫ f.hom
  rw [IntegralClosedSubspace.pushforwardIso_hom_comp_ι, Category.assoc, Category.assoc,
    Subfunctor.fromPreimage_ι]

include hfbase hflat in
/-- **The divisor on a component of `f^{-1}(W)`, read through `V ≅ V'`.**  The Weil divisor on a
component `V` of `f^{-1}(W)` of the pullback along `V ⟶ W` of `s|_W` is the divisor of the
pullback along `V ≅ V'` of `(f^*s)|_{V'}`: both are inverse images of `s` along `V ⟶ X`. -/
theorem canonicalDivisorCycleAt_componentSection_eq_pullback
    (hVc : subspacePointSet D.site D.base D.base_mem (W.subspace.preimage f.hom).toFunctor
        V.subspace ∈ irreducibleComponents
          (points D.site D.base D.base_mem (W.subspace.preimage f.hom).toFunctor))
    (hreg : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      V.isClosedSubspace.1
      (componentModule D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
        (W.subspace.fromPreimage f.hom)
        (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩) V)
      (componentSection D ((W.subspace.preimage f.hom).ι ≫ p')
        (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) (W.subspace.ι ≫ p)
        (isGood_integralClosedSubspace D p hp W) (W.subspace.fromPreimage f.hom)
        (isFlat_and_hasRelativeDimension_fromPreimage D p' hp' p hp f.hom hfbase r hflat hr W).1
        W.isIntegralSpace (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
        (globalSectionMeromorphic D.site D.base D.base_mem W.isClosedSubspace.1
          (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
          (closedSubspaceRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩)) V hVc))
    (hNm : IsInvertibleModule (B := D.site)
      ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace.toFunctor,
        (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1⟩
      (closedSubspaceRestrictSheaf D p' hp' (pullbackSheaf D p hp p' hp' f L)
        ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace,
          (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace⟩))
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem
      (preimageComponentImage p' hp' p hp f.hom W V).subspace.toFunctor
      (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem
        (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1 _
        (closedSubspaceRestrictSection D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)
          ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace,
            (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace⟩)))
    (hdeg : deltaDimensionClosed D (V.subspace.ι ≫ (W.subspace.preimage f.hom).ι ≫ p')
      (isGood_integralClosedSubspace D _
        (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) V)
      Set.univ isClosed_univ = ((k + (r : ℤ) + 1 : ℤ) : EInt)) :
    canonicalDivisorCycleAt D (V.subspace.ι ≫ (W.subspace.preimage f.hom).ι ≫ p')
        (isGood_integralClosedSubspace D _
          (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) V)
        V.isIntegralSpace
        (componentModule D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
          (W.subspace.fromPreimage f.hom)
          (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩) V)
        (modulePullbackInvertible
          (componentMorphism D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
            (W.subspace.fromPreimage f.hom) V) _
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
            (isInvertible_closedSubspaceRestrictSheaf D p hp L
              ⟨W.subspace, W.isClosedSubspace⟩ hL)))
        _ hreg hdeg =
      canonicalDivisorCycleAt D (V.subspace.ι ≫ (W.subspace.preimage f.hom).ι ≫ p')
        (isGood_integralClosedSubspace D _
          (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) V)
        V.isIntegralSpace
        ((modulePullback D.site D.base D.base_mem
          (algebraicSpacesIsoOfIso D.site D.base D.base_mem V.isClosedSubspace.1
            (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1
            (preimageComponentIso p' hp' p hp f.hom W V)).hom).obj
          (closedSubspaceRestrictSheaf D p' hp' (pullbackSheaf D p hp p' hp' f L)
            ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace,
              (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace⟩))
        (isInvertibleModule_modulePullback_algebraicSpacesIsoOfIso D.site D.base D.base_mem
          V.isClosedSubspace.1 (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1
          (preimageComponentIso p' hp' p hp f.hom W V) _ hNm)
        (pullbackMeromorphicSection D.site D.base D.base_mem
          (algebraicSpacesIsoOfIso D.site D.base D.base_mem V.isClosedSubspace.1
            (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1
            (preimageComponentIso p' hp' p hp f.hom W V)).hom _
          (pullbacksMeromorphicSections_algebraicSpacesIsoOfIso D.site D.base D.base_mem
            V.isClosedSubspace.1 (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1
            (preimageComponentIso p' hp' p hp f.hom W V)) _)
        (isRegularMeromorphicSection_pullbackMeromorphicSection_algebraicSpacesIsoOfIso
          D.site D.base D.base_mem V.isClosedSubspace.1
          (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1
          (preimageComponentIso p' hp' p hp f.hom W V) _ hNm _ hτ) hdeg := by
  have hb1 := pullbackMeromorphicSection_globalSectionMeromorphic D.site D.base D.base_mem
    (componentMorphism D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
      (W.subspace.fromPreimage f.hom) V)
    (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
    (pullbacksMeromorphicSections_componentMorphism D ((W.subspace.preimage f.hom).ι ≫ p')
      (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W)
      (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W) (W.subspace.fromPreimage f.hom)
      (isFlat_and_hasRelativeDimension_fromPreimage D p' hp' p hp f.hom hfbase r hflat hr W).1
      W.isIntegralSpace V hVc)
    (closedSubspaceRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩)
  have hb6 := pullbackMeromorphicSection_globalSectionMeromorphic D.site D.base D.base_mem
    (algebraicSpacesIsoOfIso D.site D.base D.base_mem V.isClosedSubspace.1
      (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1
      (preimageComponentIso p' hp' p hp f.hom W V)).hom
    (closedSubspaceRestrictSheaf D p' hp' (pullbackSheaf D p hp p' hp' f L)
      ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace,
        (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace⟩)
    (pullbacksMeromorphicSections_algebraicSpacesIsoOfIso D.site D.base D.base_mem
      V.isClosedSubspace.1 (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1
      (preimageComponentIso p' hp' p hp f.hom W V))
    (closedSubspaceRestrictSection D p' hp' (pullbackSheaf D p hp p' hp' f L)
      (pullbackGlobalSection D p hp p' hp' f L s)
      ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace,
        (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace⟩)
  have h6 := isRegularMeromorphicSection_pullbackMeromorphicSection_algebraicSpacesIsoOfIso
    D.site D.base D.base_mem V.isClosedSubspace.1
    (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1
    (preimageComponentIso p' hp' p hp f.hom W V) _ hNm _ hτ
  have h1 : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      V.isClosedSubspace.1 _ (globalSectionMeromorphic D.site D.base D.base_mem
        V.isClosedSubspace.1 _
        (modulePullbackSections D.site D.base D.base_mem
          (componentMorphism D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
            (W.subspace.fromPreimage f.hom) V) _
          (closedSubspaceRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩))) := by
    rw [← hb1]
    exact hreg
  have h5 : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      V.isClosedSubspace.1 _ (globalSectionMeromorphic D.site D.base D.base_mem
        V.isClosedSubspace.1 _
        (modulePullbackSections D.site D.base D.base_mem
          (algebraicSpacesIsoOfIso D.site D.base D.base_mem V.isClosedSubspace.1
            (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1
            (preimageComponentIso p' hp' p hp f.hom W V)).hom _
          (closedSubspaceRestrictSection D p' hp' (pullbackSheaf D p hp p' hp' f L)
            (pullbackGlobalSection D p hp p' hp' f L s)
            ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace,
              (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace⟩))) := by
    rw [← hb6]
    exact h6
  refine (canonicalDivisorCycleAt_congr_section D _ V.isIntegralSpace _ _ hreg h1 hdeg hb1).trans ?_
  refine (canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_square
      D _ V.isIntegralSpace _ _ _ _ f
      (componentMorphism_comp_closedSubspaceInclusion D p hp p' hp' f W V) L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) s h1 h5 hdeg).trans ?_
  exact canonicalDivisorCycleAt_congr_section D _ V.isIntegralSpace _ _ h5 h6 hdeg hb6.symm

include hfbase hflat in
/-- **The divisor on a component of `f^{-1}(W)`, transported to `X'`.**  For `W ⊄ E`, a component
`V` of `f^{-1}(W)` whose image `V'` in `X'` is not contained in `E'`, the Weil divisor on `V` of
the pullback along `V ⟶ W` of `s|_W`, transported to `V'`, is the divisor of `(f^*s)|_{V'}`,
which is the value of the Gysin rule of `(f^*ℒ, f^*s)` at `V'`. -/
theorem pushforwardCycleTransport_canonicalDivisorCycleAt_componentSection
    (_hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1)
    (hVc : subspacePointSet D.site D.base D.base_mem (W.subspace.preimage f.hom).toFunctor
        V.subspace ∈ irreducibleComponents
          (points D.site D.base D.base_mem (W.subspace.preimage f.hom).toFunctor))
    (hVdim : deltaDimension D ((W.subspace.preimage f.hom).ι ≫ p') V = k + (r : ℤ) + 1)
    (hV'E : ¬ (preimageComponentImage p' hp' p hp f.hom W V).subspace ≤
      (pullbackSectionVanishingLocus D p hp p' hp' f L s).1)
    (hreg : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      V.isClosedSubspace.1
      (componentModule D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
        (W.subspace.fromPreimage f.hom)
        (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩) V)
      (componentSection D ((W.subspace.preimage f.hom).ι ≫ p')
        (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) (W.subspace.ι ≫ p)
        (isGood_integralClosedSubspace D p hp W) (W.subspace.fromPreimage f.hom)
        (isFlat_and_hasRelativeDimension_fromPreimage D p' hp' p hp f.hom hfbase r hflat hr W).1
        W.isIntegralSpace (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
        (globalSectionMeromorphic D.site D.base D.base_mem W.isClosedSubspace.1
          (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
          (closedSubspaceRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩)) V hVc))
    (hdeg : deltaDimensionClosed D (V.subspace.ι ≫ (W.subspace.preimage f.hom).ι ≫ p')
      (isGood_integralClosedSubspace D _
        (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) V)
      Set.univ isClosed_univ = ((k + (r : ℤ) + 1 : ℤ) : EInt)) :
    IntegralClosedSubspace.pushforwardCycleTransport D p' hp'
        (isClosedSubspace_preimage_integralClosedSubspace D p' hp' p hp f.hom W).1
        (isClosedSubspace_preimage_integralClosedSubspace D p' hp' p hp f.hom W).2 V
        (k + (r : ℤ))
        (canonicalDivisorCycleAt D (V.subspace.ι ≫ (W.subspace.preimage f.hom).ι ≫ p')
          (isGood_integralClosedSubspace D _
            (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) V)
          V.isIntegralSpace
          (componentModule D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
            (W.subspace.fromPreimage f.hom)
            (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩) V)
          (modulePullbackInvertible
            (componentMorphism D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
              (W.subspace.fromPreimage f.hom) V) _
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
              (isInvertible_closedSubspaceRestrictSheaf D p hp L
                ⟨W.subspace, W.isClosedSubspace⟩ hL)))
          _ hreg hdeg) =
      gysinPullbackChernRule D p hp p' hp' f r L s hL k
        (preimageComponentImage p' hp' p hp f.hom W V)
        ((deltaDimension_preimageComponentImage D p' hp' p hp f.hom W V).trans hVdim) := by
  have hL' := isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL
  have hV'g := isGood_integralClosedSubspace D p' hp' (preimageComponentImage p' hp' p hp f.hom W V)
  have hNm : IsInvertibleModule (B := D.site)
      ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace.toFunctor,
        (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace.1⟩
      (closedSubspaceRestrictSheaf D p' hp' (pullbackSheaf D p hp p' hp' f L)
        ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace,
          (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace⟩) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (isInvertible_closedSubspaceRestrictSheaf D p' hp' _
        ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace,
          (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace⟩ hL')
  have hτ := isRegularMeromorphicSection_of_ne_zero_of_isGood D
    ((preimageComponentImage p' hp' p hp f.hom W V).subspace.ι ≫ p') hV'g
    (preimageComponentImage p' hp' p hp f.hom W V).isIntegralSpace _ hNm
    (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D _ hV'g _
      (isInvertible_closedSubspaceRestrictSheaf D p' hp' _
        ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace,
          (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace⟩ hL')
      (closedSubspaceRestrictSection_ne_zero D p' hp' _ (pullbackGlobalSection D p hp p' hp' f L s)
        hL' ⟨(preimageComponentImage p' hp' p hp f.hom W V).subspace,
          (preimageComponentImage p' hp' p hp f.hom W V).isClosedSubspace⟩ hV'E))
  have hcomp : (preimageComponentIso p' hp' p hp f.hom W V).hom ≫
      ((preimageComponentImage p' hp' p hp f.hom W V).subspace.ι ≫ p') =
        V.subspace.ι ≫ (W.subspace.preimage f.hom).ι ≫ p' := by
    rw [← Category.assoc, IntegralClosedSubspace.pushforwardIso_hom_comp_ι, Category.assoc]
  have hdeg' : deltaDimensionClosed D
      ((preimageComponentImage p' hp' p hp f.hom W V).subspace.ι ≫ p') hV'g Set.univ
      isClosed_univ = ((k + (r : ℤ) + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D p' hp' _,
      (deltaDimension_preimageComponentImage D p' hp' p hp f.hom W V).trans hVdim]
  rw [canonicalDivisorCycleAt_componentSection_eq_pullback D p hp p' hp' f hfbase r hflat hr L s
    hL k W V hVc hreg hNm hτ hdeg, gysinPullbackChernRule, sectionGysinChernRule,
    restrictedSectionChernRule, dif_neg hV'E]
  exact canonicalDivisorCycleAt_pushforwardOfIso D _ _ _ hV'g V.isIntegralSpace
    (preimageComponentImage p' hp' p hp f.hom W V).isIntegralSpace
    (preimageComponentIso p' hp' p hp f.hom W V) _ hNm _ hτ hcomp hdeg hdeg'

end Component

section NonContained

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hfbase : f.hom ≫ p = p') (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f.hom)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)

include hfbase hr hL in
/-- An integral closed subspace of `X'` occurring in `f^*[W]` for `W ⊄ E` is not contained in
`E' = f^{-1}(E)`: its generic point lies over the generic point of `W`. -/
theorem not_le_pullbackVanishingLocus_of_flatPullbackMult_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X')
    (hT : flatPullbackMult D p' hp' p hp f.hom hfbase r hflat hr W T ≠ 0) :
    ¬ T.subspace ≤ (pullbackSectionVanishingLocus D p hp p' hp' f L s).1 := by
  intro hle
  have hgen := pointsMap_ambientGenericPoint_eq_of_flatPullbackMult_ne_zero D p' hp' p hp f.hom
    hfbase r hr hflat W T hT
  have hmem : T.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X'
        (pullbackSectionVanishingLocus D p hp p' hp' f L s).1 :=
    subspacePointSet_mono_of_le D hle ⟨T.genericPoint D.site D.base D.base_mem, rfl⟩
  rw [pullbackVanishingLocus_eq_preimage D p hp p' hp' f L s hL, subspacePointSet_preimage,
    Set.mem_preimage, hgen] at hmem
  exact notMem_subspacePointSet_ambientGenericPoint_of_not_le D hp.1 _
    (vanishingLocus D p hp L s).2 W hWE hmem

include hfbase hr hL in
/-- For `W ⊄ E` the pulled-back section `s_V = (V ⟶ W)^*(s|_W)` of Stacks 0EQQ is regular. -/
theorem isRegularMeromorphicSection_gysinComponentSection
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1)
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f.hom).toFunctor)
    (hVc : subspacePointSet D.site D.base D.base_mem (W.subspace.preimage f.hom).toFunctor
        V.subspace ∈ irreducibleComponents
          (points D.site D.base D.base_mem (W.subspace.preimage f.hom).toFunctor)) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      V.isClosedSubspace.1
      (componentModule D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
        (W.subspace.fromPreimage f.hom)
        (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩) V)
      (componentSection D ((W.subspace.preimage f.hom).ι ≫ p')
        (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) (W.subspace.ι ≫ p)
        (isGood_integralClosedSubspace D p hp W) (W.subspace.fromPreimage f.hom)
        (isFlat_and_hasRelativeDimension_fromPreimage D p' hp' p hp f.hom hfbase r hflat hr W).1
        W.isIntegralSpace (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
        (globalSectionMeromorphic D.site D.base D.base_mem W.isClosedSubspace.1
          (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
          (closedSubspaceRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩)) V hVc) := by
  have hM := isInvertible_closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩ hL
  refine (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem V.isClosedSubspace.1
    V.isIntegralSpace (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
      (isGood_integralClosedSubspace D _
        (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) V)) _
    (modulePullbackInvertible
      (componentMorphism D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
        (W.subspace.fromPreimage f.hom) V) _
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM)) _).mpr ?_
  exact componentSection_ne_zero D _
    (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W)
    _ (isGood_integralClosedSubspace D p hp W) _ _ W.isIntegralSpace _ hM _
    (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D _
      (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩) _ hM
      (closedSubspaceRestrictSection_ne_zero D p hp L s hL ⟨W.subspace, W.isClosedSubspace⟩ hWE))
    V hVc

include hL in
/-- **Stacks 0EQQ for `h : f^{-1}(W) ⟶ W` at the Gysin rule**, coefficientwise: for `W ⊄ E` the
flat pullback along `h` of `i^*[W] = div_{ℒ|_W}(s|_W)` is the weighted sum over the components
`V` of `f^{-1}(W)` of the divisors of `s_V`. -/
theorem flatPullbackMap_gysinChernRule_apply_of_not_le
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f.hom).toFunctor) :
    (flatPullbackMap D ((W.subspace.preimage f.hom).ι ≫ p')
        (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W)
        (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
        (W.subspace.fromPreimage f.hom) (fromPreimage_comp_ι_comp D p' p f.hom hfbase W) r
        (isFlat_and_hasRelativeDimension_fromPreimage D p' hp' p hp f.hom hfbase r hflat hr W).1
        (isFlat_and_hasRelativeDimension_fromPreimage D p' hp' p hp f.hom hfbase r hflat hr W).2
        k (k + (r : ℤ)) rfl (sectionGysinChernRule D p hp L s hL k W hW)).1 Z =
      ∑ᶠ j : topDimensionalComponents D ((W.subspace.preimage f.hom).ι ≫ p') (k + 1 + r),
        spaceMultiplicity D (W.subspace.preimage f.hom).toFunctor
            (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W).1 j.1 *
          (integralClosedSubspacePushforward D ((W.subspace.preimage f.hom).ι ≫ p')
            (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) j.1 (k + (r : ℤ))
            (canonicalDivisorCycleAt D (j.1.subspace.ι ≫ (W.subspace.preimage f.hom).ι ≫ p')
              (isGood_integralClosedSubspace D _
                (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) j.1)
              j.1.isIntegralSpace
              (componentModule D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
                (W.subspace.fromPreimage f.hom)
                (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩) j.1)
              (modulePullbackInvertible
                (componentMorphism D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
                  (W.subspace.fromPreimage f.hom) j.1) _
                (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
                  (isInvertible_closedSubspaceRestrictSheaf D p hp L
                    ⟨W.subspace, W.isClosedSubspace⟩ hL)))
              _ (isRegularMeromorphicSection_gysinComponentSection D p hp p' hp' f hfbase r hflat hr
                L s hL W hWE j.1 j.2.1)
              (deltaDimensionClosed_preimageComponent D p' hp' p hp f.hom W j.1
                (by rw [j.2.2]; ring)))).1 Z := by
  have hM := isInvertible_closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩ hL
  have hn : deltaDimensionClosed D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D p hp W, hW]
  have h1 := congrArg (fun c => c.1 Z)
    (flatPullbackMap_sectionWeilDivisor_eq_componentDivisorSum D
      ((W.subspace.preimage f.hom).ι ≫ p')
      (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W)
      (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
      (W.subspace.fromPreimage f.hom) (fromPreimage_comp_ι_comp D p' p f.hom hfbase W) r
      (isFlat_and_hasRelativeDimension_fromPreimage D p' hp' p hp f.hom hfbase r hflat hr W).1
      (isFlat_and_hasRelativeDimension_fromPreimage D p' hp' p hp f.hom hfbase r hflat hr W).2
      W.isIntegralSpace hn (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
      hM (globalSectionMeromorphic D.site D.base D.base_mem W.isClosedSubspace.1
        (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
        (closedSubspaceRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩))
      (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D _
        (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩) _ hM
        (closedSubspaceRestrictSection_ne_zero D p hp L s hL ⟨W.subspace, W.isClosedSubspace⟩
          hWE)))
  simp only [flatPullbackMap_apply] at h1 ⊢
  rw [sectionGysinChernRule, restrictedSectionChernRule_of_not_le_coe D p hp L s hL k _ hW hWE]
  refine h1.trans ?_
  unfold componentDivisorSum
  rw [cycleFamilySum_apply]
  refine finsum_congr fun j => ?_
  rw [map_zsmul, AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul]
  rfl

include hL in
/-- The term of the expansion at one component `V` of `f^{-1}(W)` occurring in `f^*[W]`. -/
theorem pushforwardCycleTransport_gysinComponentDivisor
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1)
    (j : topDimensionalComponents D ((W.subspace.preimage f.hom).ι ≫ p') (k + 1 + r))
    (hj : flatPullbackMult D p' hp' p hp f.hom hfbase r hflat hr W
      (preimageComponentImage p' hp' p hp f.hom W j.1) ≠ 0)
    (hVdim : deltaDimension D ((W.subspace.preimage f.hom).ι ≫ p') j.1 = k + (r : ℤ) + 1) :
    IntegralClosedSubspace.pushforwardCycleTransport D p' hp'
        (isClosedSubspace_preimage_integralClosedSubspace D p' hp' p hp f.hom W).1
        (isClosedSubspace_preimage_integralClosedSubspace D p' hp' p hp f.hom W).2 j.1
        (k + (r : ℤ))
        (canonicalDivisorCycleAt D (j.1.subspace.ι ≫ (W.subspace.preimage f.hom).ι ≫ p')
          (isGood_integralClosedSubspace D _
            (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) j.1)
          j.1.isIntegralSpace
          (componentModule D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
            (W.subspace.fromPreimage f.hom)
            (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩) j.1)
          (modulePullbackInvertible
            (componentMorphism D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
              (W.subspace.fromPreimage f.hom) j.1) _
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
              (isInvertible_closedSubspaceRestrictSheaf D p hp L
                ⟨W.subspace, W.isClosedSubspace⟩ hL)))
          _ (isRegularMeromorphicSection_gysinComponentSection D p hp p' hp' f hfbase r hflat hr
            L s hL W hWE j.1 j.2.1)
          (deltaDimensionClosed_preimageComponent D p' hp' p hp f.hom W j.1 hVdim)) =
      gysinPullbackChernRule D p hp p' hp' f r L s hL k
        (preimageComponentImage p' hp' p hp f.hom W j.1)
        ((deltaDimension_preimageComponentImage D p' hp' p hp f.hom W j.1).trans hVdim) :=
  pushforwardCycleTransport_canonicalDivisorCycleAt_componentSection D p hp p' hp' f
    hfbase r hflat hr L s hL k W j.1 hWE j.2.1 hVdim
    (not_le_pullbackVanishingLocus_of_flatPullbackMult_ne_zero D p hp p' hp' f hfbase r hflat hr L
      s hL W hWE (preimageComponentImage p' hp' p hp f.hom W j.1) hj)
    (isRegularMeromorphicSection_gysinComponentSection D p hp p' hp' f hfbase r hflat hr
      L s hL W hWE j.1 j.2.1)
    (deltaDimensionClosed_preimageComponent D p' hp' p hp f.hom W j.1 hVdim)

/-- Every integral closed subspace of `X'` occurring in `f^*[W]` is the image of a component of
`f^{-1}(W)` of top dimension. -/
theorem exists_topDimensionalComponent_of_flatPullbackMult_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D p W = k + 1)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X')
    (hT : flatPullbackMult D p' hp' p hp f.hom hfbase r hflat hr W T ≠ 0) :
    ∃ j : topDimensionalComponents D ((W.subspace.preimage f.hom).ι ≫ p') (k + 1 + r),
      preimageComponentImage p' hp' p hp f.hom W j.1 = T := by
  by_cases hex : ∃ V, preimageComponentImage p' hp' p hp f.hom W V = T
  · obtain ⟨V, rfl⟩ := hex
    have hd := deltaDimension_eq_of_flatPullbackMult_ne_zero D p' hp' p hp f.hom hfbase r hflat
      hr W _ hT
    refine ⟨⟨V, mem_irreducibleComponents_of_deltaDimension_preimageComponentImage D p' hp' p hp
      f.hom hfbase r hflat hr W V hd, ?_⟩, rfl⟩
    rw [← deltaDimension_preimageComponentImage D p' hp' p hp f.hom W V, hd, hW]
  · exact absurd (flatPullbackMult_eq_zero_of_forall_ne_preimageComponentImage D p' hp' p hp
      f.hom hfbase r hflat hr W T fun V hV => hex ⟨V, hV⟩) hT

/-- The multiplicity of the image of a component of top dimension in `f^*[W]` is the
multiplicity of the component in `f^{-1}(W)`. -/
theorem flatPullbackMult_preimageComponentImage_eq_spaceMultiplicity
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D p W = k + 1)
    (j : topDimensionalComponents D ((W.subspace.preimage f.hom).ι ≫ p') (k + 1 + r)) :
    flatPullbackMult D p' hp' p hp f.hom hfbase r hflat hr W
        (preimageComponentImage p' hp' p hp f.hom W j.1) =
      spaceMultiplicity D (W.subspace.preimage f.hom).toFunctor
        (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W).1 j.1 := by
  have hV : deltaDimension D p' (preimageComponentImage p' hp' p hp f.hom W j.1) =
      deltaDimension D p W + (r : ℤ) := by
    rw [deltaDimension_preimageComponentImage D p' hp' p hp f.hom W j.1, j.2.2, hW]
  exact flatPullbackMult_preimageComponentImage_eq_geometricLength D p' hp' p hp f.hom hfbase r
    hflat hr W j.1 hV

include hL in
/-- **Stacks 0ER6, the case `W ⊄ D`.**  For an integral closed subspace `W ⊄ E` of δ-dimension
`k + 1`, the defect `f^*(i^*[W]) - (i')^*f^*[W]`, read on `X'` through the pushforwards along
`i` and `i'`, vanishes.  This is Stacks 0EQQ for `h : f^{-1}(W) ⟶ W`, the divisors of the
restricted sections being the cycles `[E ∩ W]_k` and `[E' ∩ W']_{k+r}` of Stacks 0EQF. -/
theorem flatChernDefect_gysinChernRule_eq_zero_of_not_le
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    flatChernDefect D p' hp' p hp f.hom hfbase r hflat hr k (sectionGysinChernRule D p hp L s hL k)
      (gysinPullbackChernRule D p hp p' hp' f r L s hL k) W hW = 0 :=
  flatChernDefect_eq_zero_of_finsum D p' hp' p hp f.hom hfbase r hflat hr W k _ _ hW
    (J := topDimensionalComponents D ((W.subspace.preimage f.hom).ι ≫ p') (k + 1 + r))
    (fun j => j.1) Subtype.val_injective _
    (flatPullbackMult_preimageComponentImage_eq_spaceMultiplicity D p hp p' hp' f hfbase r hflat
      hr k W hW)
    (exists_topDimensionalComponent_of_flatPullbackMult_ne_zero D p hp p' hp' f hfbase r hflat hr
      k W hW)
    (locallyFinite_topDimensionalComponents D _
      (isGood_ι_preimage_integralClosedSubspace D p' hp' p hp f.hom W) _)
    (fun j => by rw [j.2.2]; ring) _
    (flatPullbackMap_gysinChernRule_apply_of_not_le D p hp p' hp' f hfbase r hflat hr L s hL k W
      hW hWE)
    (fun j hj => pushforwardCycleTransport_gysinComponentDivisor D p hp p' hp' f hfbase r hflat hr
      L s hL k W hWE j
      ((flatPullbackMult_preimageComponentImage_eq_spaceMultiplicity D p hp p' hp' f hfbase r
        hflat hr k W hW j).trans_ne hj) (by rw [j.2.2]; ring))

end NonContained

end AlgebraicGeometry.Space

end
