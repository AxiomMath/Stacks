module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveCompletionBundleFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VanishingLocusComplementPullbackInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VectorBundlePullbackSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankNotionBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartFamilyCoveringSieve
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionVectorBundleOpenImmersionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafIsoOfCartesianFamily

/-!
# Flat pullback along a vector bundle on Chow groups

Let `X/B` be good, `ℰ` a finite locally free `𝒪_X`-module of rank `r` and `p : E → X` its vector
bundle. This file proves the two halves of Stacks 0ERW for `p^* : CH_k(X) → CH_{k+r}(E)` on the
Chow groups of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK
(`AlgebraicGeometry.Space.chowGroupCanonical`).

* Surjectivity is the cycle-level statement
  `AlgebraicGeometry.Space.isFlatPullbackSurjective_vectorBundleProjection` (Stacks 0ERG).
* Injectivity is the source's argument through the projective completion
  `π : P = 𝐏(ℰ ⊕ 𝒪_X) → X`, the hyperplane at infinity `D = Z(s) ≅ 𝐏(ℰ)` and the open immersion
  `j : E → P ∖ D`
  (`AlgebraicGeometry.Space.injective_flatPullbackChowMapCanonical_of_vanishingLocus`), from the
  projective bundle formula of Stacks 0ERV: its surjectivity for `𝐏(ℰ)` and its injectivity for
  `𝐏(ℰ ⊕ 𝒪_X)`, which are the explicit arguments of
  `injective_flatPullbackChowMapCanonical_vectorBundleProjection_of_bundleFormula`.
  This needs `ℰ` of positive rank; in rank `0` the projection `p` is an isomorphism
  (`AlgebraicGeometry.Space.isIso_vectorBundleProjection_of_rank_zero`), since it is one over
  each affine chart trivializing `ℰ`, where it is `𝐀^0_V ⟶ V`.

## Main results

* `AlgebraicGeometry.Space.surjective_flatPullbackChowMapCanonical_vectorBundleProjection`
* `injective_flatPullbackChowMapCanonical_vectorBundleProjection_of_bundleFormula`
* `bijective_flatPullbackChowMapCanonical_vectorBundleProjection_of_bundleFormula`:
  Stacks 0ERW for every rank, from the conclusions of Stacks 0ERV.
* `AlgebraicGeometry.Space.isIso_vectorBundleProjection_of_rank_zero`,
  `AlgebraicGeometry.Space.injective_flatPullbackChowMapCanonical_of_isIso` and
  `injective_flatPullbackChowMapCanonical_vectorBundleProjection_of_rank_zero`

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0ERG](https://stacks.math.columbia.edu/tag/0ERG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

section Surjective

variable (D : BaseSpaceDimensionSituation.{u}) (W : AlgebraicSpaces D.site D.base D.base_mem)
    (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r]
    (sW : W.1 ⟶ D.space) (hW : D.IsGood sW)

/-- **The surjectivity half of Stacks 0ERW on Chow groups.** For a finite locally free module `ℰ`
of rank `r` on a good `W/B`, the flat pullback `p^* : CH_k(W) → CH_{k+r}(E)` along the vector
bundle `p : E → W` is surjective. -/
theorem surjective_flatPullbackChowMapCanonical_vectorBundleProjection (k : ℤ) :
    Function.Surjective (flatPullbackChowMapCanonical.{u + 1} D
      ((vectorBundleProjection D.site D.base D.base_mem W F).hom ≫ sW)
      (isGood_vectorBundle D W F sW hW) sW hW
      (vectorBundleProjection D.site D.base D.base_mem W F).hom
      rfl r (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
      (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F r) k
      (k + (r : ℤ)) rfl) := by
  intro b
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective b
  obtain ⟨β, hβ⟩ := isFlatPullbackSurjective_vectorBundleProjection D W F r sW hW k α
  refine ⟨chowClassCanonical.{u + 1} D sW hW k β, ?_⟩
  rw [flatPullbackChowMapCanonical_chowClassCanonical]
  exact (chowClassCanonical_eq_iff_rationallyEquivalentCanonical.{u + 1} D _
    (isGood_vectorBundle D W F sW hW) (k + (r : ℤ)) _ α).2
    (hβ.isRationallyEquivalentToZeroWithinCanonical.uliftIndex.{u + 1, u}
      ).isRationallyEquivalentToZeroCanonical

end Surjective

section Injective

variable (D : BaseSpaceDimensionSituation.{u})
    {X : AlgebraicSpaces D.site D.base D.base_mem} (sX : X.1 ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (m : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E (m + 1))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem X) from E)]

/-- The open immersion `j : E → P` of the vector bundle into its projective completion has image
the complement of the zero scheme `Z(s)`, read as the vanishing locus of `s`. -/
theorem range_vanishingLocus_ι_eq_compl_range_projectiveCompletionVectorBundleImmersion :
    Set.range (pointsMap D.site D.base D.base_mem _
        (vanishingLocus D _ (isGood_projectiveCompletionProj_comp D sX hX E m hr)
          (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1.ι) =
      (Set.range (pointsMap D.site D.base D.base_mem _
        (projectiveCompletionVectorBundleImmersion E hr).hom))ᶜ := by
  rw [range_pointsMap_projectiveCompletionVectorBundleImmersion_eq_compl_zeroScheme, compl_compl]

/-- **The injectivity half of Stacks 0ERW, from Stacks 0ERV.** For a finite locally free module
`ℰ` of rank `m + 1` on a good `X/B`, the flat pullback `p^* : CH_k(X) → CH_{k+m+1}(E)` along the
vector bundle `p : E → X` is injective, granted the conclusions of the projective bundle formula
of Stacks 0ERV for `ℰ` and `ℰ ⊕ 𝒪_X`: the surjectivity half for `𝐏(ℰ)` (`hQ`) and the injectivity
half for `𝐏(ℰ ⊕ 𝒪_X)` (`hP`), and the comparison `i^*𝒪_P(1) ≅ 𝒪_{𝐏(ℰ)}(1)` along the
hyperplane at infinity `i` (`htw`). -/
theorem injective_flatPullbackChowMapCanonical_vectorBundleProjection_of_bundleFormula
    (htw : (modulePullback D.site D.base D.base_mem
        (projectiveCompletionInfinityImmersion E hr)).obj (projectiveCompletionTwist E hr).obj ≅
      (@projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).obj)
    (hQ : BundleFormulaSurjective D sX hX _
      (isGood_projectiveBundleProj_comp_of_rank D sX hX E m hr)
      (@projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).hom rfl m
      (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) m hr
        hr.isFiniteLocallyFreeOnSite)
      (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) m hr
        hr.isFiniteLocallyFreeOnSite)
      (@projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).obj
      (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite))
    (hP : ∀ (N : ℤ) (d : Fin (m + 2) → ℤ) (hd : ∀ i, d i + ((m + 1 : ℕ) : ℤ) = N + (i : ℕ)),
      Function.Injective (bundleFormulaMap D sX hX _
        (isGood_projectiveCompletionProj_comp D sX hX E m hr) (projectiveCompletionProj E hr).hom
        rfl (m + 1) (isFlat_projectiveCompletionProj E hr)
        (hasRelativeDimension_projectiveCompletionProj E hr) (projectiveCompletionTwist E hr).obj
        (isInvertibleModule_projectiveCompletionTwist E hr) N d hd))
    (k : ℤ) :
    Function.Injective (flatPullbackChowMapCanonical.{u + 1} D
      ((vectorBundleProjection D.site D.base D.base_mem X E).hom ≫ sX)
      (isGood_vectorBundle D X E sX hX) sX hX
      (vectorBundleProjection D.site D.base D.base_mem X E).hom
      rfl (m + 1) (isFlat_vectorBundleProjection D.site D.base D.base_mem X E)
      (@hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem X E _ (m + 1)
        (isFiniteLocallyFreeOfRank_sheafOfModules E hr)) k
      (k + ((m + 1 : ℕ) : ℤ)) rfl) := by
  have hPg := isGood_projectiveCompletionProj_comp D sX hX E m hr
  have hQg := isGood_projectiveBundleProj_comp_of_rank D sX hX E m hr
  have hZg := isGood_vanishingLocus D _ hPg (projectiveCompletionTwist E hr).obj
    (projectiveCompletionSection E hr)
  have hE := isRelativeEffectiveCartierDivisor_projectiveCompletionZeroScheme D sX hX E m hr
  have hjq : (projectiveCompletionVectorBundleImmersion E hr).hom ≫
      (projectiveCompletionProj E hr).hom =
        (vectorBundleProjection D.site D.base D.base_mem X E).hom :=
    congrArg (fun f => f.hom)
      (projectiveCompletionVectorBundleImmersion_comp_projectiveCompletionProj E hr)
  have hjB : (projectiveCompletionVectorBundleImmersion E hr).hom ≫
      ((projectiveCompletionProj E hr).hom ≫ sX) =
        (vectorBundleProjection D.site D.base D.base_mem X E).hom ≫ sX := by
    rw [← Category.assoc, hjq]
  have hD := BundleFormulaSurjective.of_iso D sX hX _ hQg _ hZg _ rfl _ rfl m _ _
    (@isProper_projectiveBundleProj D.site D.base D.base_mem X E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite)
    hE.2 (hasRelativeDimension_ι_comp D _ hPg sX hX _ rfl m
      (hasRelativeDimension_projectiveCompletionProj E hr) _ hE)
    (isProper_vanishingLocus_ι_comp D sX hX _ hPg _ (isProper_projectiveCompletionProj E hr)
      (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr))
    _ _ _
    (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hPg.1
      (vanishingLocus D _ hPg (projectiveCompletionTwist E hr).obj
        (projectiveCompletionSection E hr)).1
      (vanishingLocus D _ hPg (projectiveCompletionTwist E hr).obj
        (projectiveCompletionSection E hr)).2) _
      (isInvertibleModule_projectiveCompletionTwist E hr))
    (inv (infinityLocusIso D sX hX E m hr))
    (by rw [← Category.assoc, ← zeroScheme_ι_comp_projectiveCompletionProj]; rfl)
    (zeroScheme_ι_comp_projectiveCompletionProj D sX hX E m hr).symm
    (infinityLocusTwistIso D sX hX E m hr htw) hQ
  exact injective_flatPullbackChowMapCanonical_of_vanishingLocus D sX hX _ hPg
    (projectiveCompletionProj E hr).hom rfl m (isFlat_projectiveCompletionProj E hr)
    (hasRelativeDimension_projectiveCompletionProj E hr) (projectiveCompletionTwist E hr).obj
    (isInvertibleModule_projectiveCompletionTwist E hr) (projectiveCompletionSection E hr) hE _
    (isGood_vectorBundle D X E sX hX)
    (isOpenImmersion_projectiveCompletionVectorBundleImmersion E hr)
    hjB (range_vanishingLocus_ι_eq_compl_range_projectiveCompletionVectorBundleImmersion D sX hX E m
      hr) _ rfl hjq _ _ hD hP k

end Injective

section Iso

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) [IsIso π] (hπB : π ≫ sX = sP)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension 0 D.site D.base D.base_mem π)

include hP in
/-- The flat pullback along `π⁻¹` of the flat pullback along an isomorphism `π` is the identity,
on coefficient families. -/
theorem coe_flatPullbackMap_inv_flatPullbackMap (m n : ℤ) (hmn : m + ((0 : ℕ) : ℤ) = n)
    (hnm : n + ((0 : ℕ) : ℤ) = m) (hψB : inv π ≫ sP = sX)
    (hψ : IsFlat D.site D.base D.base_mem (inv π) ∧
      HasRelativeDimension 0 D.site D.base D.base_mem (inv π)) (α : CycleGroup D sX m) :
    (flatPullbackMap D sX hX sP hP (inv π) hψB 0 hψ.1 hψ.2 n m hnm
      (flatPullbackMap D sP hP sX hX π hπB 0 hflat hrel m n hmn α)).1 = α.1 := by
  have hid := isFlat_and_hasRelativeDimension_zero_of_isIso D sX hX sX hX (𝟙 X)
  have h1 := congrArg (fun ψ => (ψ α).1)
    (flatPullbackMap_comp D sX hX sP hP sX hX (inv π) π hψB hπB 0 0 hψ.1 hψ.2 hflat hrel m m
      (by simp))
  refine (Eq.trans ?_ h1.symm).trans ((flatPullbackMap_coe_congr D sX hX sX hX
    (IsIso.inv_hom_id π) _ (Category.id_comp sX) rfl _ hid.1 _ hid.2 m m m m _ (by simp) _ _
    rfl).trans (flatPullbackMap_id_coe D sX hX (Category.id_comp sX) hid.1 hid.2 m m (by simp) α))
  exact coe_flatPullbackMap_congr D sP hP sX hX (inv π) hψB 0 hψ.1 hψ.2 (by omega) rfl hnm
    (by simp) _ _ (coe_flatPullbackMap_congr D sX hX sP hP π hπB 0 hflat hrel rfl (by omega) _ _
      _ _ rfl)

/-- **Flat pullback along an isomorphism is injective on Chow groups.** -/
theorem injective_flatPullbackChowMapCanonical_of_isIso (m n : ℤ)
    (hmn : m + ((0 : ℕ) : ℤ) = n) :
    Function.Injective (flatPullbackChowMapCanonical.{u + 1} D sP hP sX hX π hπB 0 hflat hrel m n
      hmn) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective a
  have hψB : inv π ≫ sP = sX := by rw [← hπB, IsIso.inv_hom_id_assoc]
  have hψ := isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sX hX (inv π)
  have h := isRationallyEquivalentToZeroCanonical_flatPullbackMap.{u + 1} D sX hX sP hP (inv π)
    hψB 0 hψ.1 hψ.2 n m (by omega)
    ((chowClassCanonical_eq_zero_iff.{u + 1} D sP hP n _).1 ha)
  rw [show flatPullbackMap D sX hX sP hP (inv π) hψB 0 hψ.1 hψ.2 n m (by omega)
      (flatPullbackMap D sP hP sX hX π hπB 0 hflat hrel m n hmn α) = α from
    Subtype.ext (coe_flatPullbackMap_inv_flatPullbackMap D sX hX sP hP π hπB hflat hrel m n hmn
      (by omega) hψB hψ α)] at h
  exact (chowClassCanonical_eq_zero_iff.{u + 1} D sX hX m α).2 h

end Iso

section RankZero

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (W : AlgebraicSpaces B S hS)
    (F : SheafOfModules.{u} (structureRingSheaf B S hS W))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F 0]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F 0] in
/-- On an affine chart `V` on which `ℰ` is free of rank `0`, the projection `E ×_W V ⟶ V` of the
vector bundle is an isomorphism: it is `𝐀^0_V ⟶ V`. -/
theorem isIso_vectorBundleChartHom_of_rank_zero (V : SmallEtale B S hS W.1)
    [IsAffine (chartScheme V)] {ι : Type u}
    (e : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι)
    (ε : ι ≃ Fin 0) : IsIso (vectorBundleChartHom B S hS W F V) := by
  have : IsEmpty ι := ε.isEmpty
  have : IsIso (𝔸(ι; chartScheme V) ↘ chartScheme V) := inferInstance
  have : IsIso ((BigFppfOver.toScheme B S hS).map (vectorBundleChartHom B S hS W F V)) := by
    rw [← vectorBundleChartIso_hom_over B S hS W F V e (Equiv.refl ι)]
    infer_instance
  exact isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)

/-- **The vector bundle of a module of rank `0` is the base**: its projection is an isomorphism,
since it is one over a covering family of affine charts trivializing `ℰ`
(`CategoryTheory.Presheaf.isIso_of_isPullback_family`). -/
theorem isIso_vectorBundleProjection_of_rank_zero :
    IsIso (vectorBundleProjection B S hS W F).hom := by
  classical
  let P := presentationOfIsAlgebraicSpace B S hS W.1 W.2
  let a : (BigFppfOver.toScheme B S hS).obj P.U ≃ points B S hS (yoneda.obj P.U) :=
    (Equiv.ofBijective _ ⟨injective_pointsToScheme B S hS P.U,
      surjective_pointsToScheme B S hS P.U⟩).symm
  choose V ι hι e ε z hV hz using fun k : (BigFppfOver.toScheme B S hS).obj P.U =>
    exists_trivializing_affine_chart_of_rank B S hS W F 0
      (pointsMap B S hS (yoneda.obj P.U) P.toSpace (a k))
  have hiso : ∀ x, IsIso (vectorBundleChartHom B S hS W F (V x)) := fun x =>
    have : IsAffine (chartScheme (V x)) := hV x
    isIso_vectorBundleChartHom_of_rank_zero B S hS W F (V x) (e x) (ε x)
  have hcov : ∀ p : points B S hS W.1, ∃ k,
      p ∈ Set.range (pointsMap B S hS _ (V k).obj.hom) := fun p => by
    obtain ⟨a', rfl⟩ := Presentation.pointsMap_surjective P p
    refine ⟨pointsToScheme B S hS P.U a',
      (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS W.1).obj (V _))).symm (z _), ?_⟩
    refine ((chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS W.1 (V _)
      (z _)).symm.trans (hz _)).trans ?_
    exact congrArg _ ((Equiv.ofBijective _ _).symm_apply_apply a')
  refine Presheaf.isIso_of_isPullback_family (BigFppfOver.topology B S hS)
    (vectorBundle B S hS W F).obj.left.2.isSheaf W.2.isSheaf
    (vectorBundleProjection B S hS W F).hom (𝟙 W.1) (vectorBundleProjection B S hS W F).hom
    (Category.comp_id _) (fun x => (V x).obj.hom)
    (familyImageSieve_chartHom_mem_topology V hcov)
    (fun x => vectorBundleChartToTotal B S hS W F (V x))
    (fun x => yoneda.map (vectorBundleChartHom B S hS W F (V x)))
    (fun x => isPullback_vectorBundleChart B S hS W F (V x)) (fun x => ?_)
  have := hiso x
  exact IsPullback.of_vert_isIso ⟨by
    rw [Category.comp_id]
    exact (isPullback_vectorBundleChart B S hS W F (V x)).w⟩

end RankZero

/-- **Stacks 0ERW in rank `0`, injectivity**: for a module of rank `0` the projection of the vector
bundle is an isomorphism, so `p^* : CH_k(W) → CH_k(E)` is injective. -/
theorem injective_flatPullbackChowMapCanonical_vectorBundleProjection_of_rank_zero
    (D : BaseSpaceDimensionSituation.{u}) (W : AlgebraicSpaces D.site D.base D.base_mem)
    (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F 0]
    (sW : W.1 ⟶ D.space) (hW : D.IsGood sW) (k : ℤ) :
    Function.Injective (flatPullbackChowMapCanonical.{u + 1} D
      ((vectorBundleProjection D.site D.base D.base_mem W F).hom ≫ sW)
      (isGood_vectorBundle D W F sW hW) sW hW
      (vectorBundleProjection D.site D.base D.base_mem W F).hom
      rfl 0 (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
      (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F 0) k
      (k + ((0 : ℕ) : ℤ)) rfl) :=
  have := isIso_vectorBundleProjection_of_rank_zero D.site D.base D.base_mem W F
  injective_flatPullbackChowMapCanonical_of_isIso D sW hW _ (isGood_vectorBundle D W F sW hW) _ rfl
    _ _ k _ rfl


/-! ### The assembly -/

section Assembly

variable (D : BaseSpaceDimensionSituation.{u})

/-- **Stacks 0ERW, from the conclusions of Stacks 0ERV.** In Situation 0EDT let `W/B` be good,
let `ℰ` be a finite locally free `𝒪_W`-module of rank `r` and `p : E → W` its vector bundle. Then
`p^* : CH_k(W) → CH_{k+r}(E)` is bijective for every `k`, on the Chow groups of Stacks 0EQ6 at the
canonical embeddings of Stacks 0ENK.

The three explicit inputs are the conclusions of the projective bundle formula used by the
source, for every good `X/B` and every module `ℰ'` of rank `n + 1`: the surjectivity half for
`𝐏(ℰ')` (`hQ`), the injectivity half for `𝐏(ℰ')` (`hP`, used at `ℰ' = ℰ ⊕ 𝒪_W`), and the
comparison `i^*𝒪_P(1) ≅ 𝒪_{𝐏(ℰ')}(1)` along the hyperplane at infinity `i` of the projective
completion (`htw`). Surjectivity of `p^*` is
`AlgebraicGeometry.Space.surjective_flatPullbackChowMapCanonical_vectorBundleProjection`;
injectivity is `injective_flatPullbackChowMapCanonical_vectorBundleProjection_of_rank_zero`
in rank `0` and
`injective_flatPullbackChowMapCanonical_vectorBundleProjection_of_bundleFormula`
in rank `m + 1`. -/
theorem bijective_flatPullbackChowMapCanonical_vectorBundleProjection_of_bundleFormula
    (hQ : ∀ (X : AlgebraicSpaces D.site D.base D.base_mem) (sX : X.1 ⟶ D.space) (hX : D.IsGood sX)
      (E : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (n : ℕ)
      (hr : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E (n + 1)),
      BundleFormulaSurjective D sX hX _ (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
        (@projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).hom rfl n
        (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
          hr.isFiniteLocallyFreeOnSite)
        (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
          hr.isFiniteLocallyFreeOnSite)
        (@projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).obj
        (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite))
    (hP : ∀ (X : AlgebraicSpaces D.site D.base D.base_mem) (sX : X.1 ⟶ D.space) (hX : D.IsGood sX)
      (E : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (n : ℕ)
      (hr : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E (n + 1))
      (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)),
      Function.Injective (bundleFormulaMap D sX hX _
        (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
        (@projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).hom rfl n
        (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
          hr.isFiniteLocallyFreeOnSite)
        (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
          hr.isFiniteLocallyFreeOnSite)
        (@projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).obj
        (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite) N d hd))
    (htw : ∀ (X : AlgebraicSpaces D.site D.base D.base_mem)
      (E : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (n : ℕ)
      (hr : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E (n + 1)),
      (modulePullback D.site D.base D.base_mem
          (projectiveCompletionInfinityImmersion E hr)).obj (projectiveCompletionTwist E hr).obj ≅
        (@projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).obj)
    (W : AlgebraicSpaces D.site D.base D.base_mem)
    (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r]
    (sW : W.1 ⟶ D.space) (hW : D.IsGood sW) (k : ℤ) :
    Function.Bijective (flatPullbackChowMapCanonical.{u + 1} D
      ((vectorBundleProjection D.site D.base D.base_mem W F).hom ≫ sW)
      (isGood_vectorBundle D W F sW hW) sW hW
      (vectorBundleProjection D.site D.base D.base_mem W F).hom
      rfl r (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
      (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F r) k
      (k + (r : ℤ)) rfl) := by
  refine ⟨?_, surjective_flatPullbackChowMapCanonical_vectorBundleProjection D W F r sW hW k⟩
  cases r with
  | zero =>
    exact injective_flatPullbackChowMapCanonical_vectorBundleProjection_of_rank_zero D W F sW hW k
  | succ m =>
    have hr : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem W.1 W.2) F (m + 1) :=
      isFiniteLocallyFreeOfRank_of_sheafOfModules F
    exact injective_flatPullbackChowMapCanonical_vectorBundleProjection_of_bundleFormula D sW hW F m
      hr (htw W F m hr) (hQ W sW hW F m hr)
      (fun N d hd => hP W sW hW (addUnit W.2 F) (m + 1) (isFiniteLocallyFreeOfRank_addUnit hr) N d
        hd) k

end Assembly

end AlgebraicGeometry.Space

end
