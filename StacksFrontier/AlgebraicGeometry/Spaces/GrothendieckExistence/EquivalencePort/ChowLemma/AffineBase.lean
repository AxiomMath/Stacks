module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.Datum
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.ResolveGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.GraphClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjectiveOfHQuasiProjective
public import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Morphisms.OpenImmersionOfFlatClosure
public import StacksFrontier.AlgebraicGeometry.C1573Port.Blowup.FlattenedGraph
public import StacksFrontier.AlgebraicGeometry.C1573Port.SectionsToProjectiveSpace.DenseOpen
public import StacksFrontier.AlgebraicGeometry.C1573Port.Blowup.ReesAlgebra.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleExtension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleEnlargementOfOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms

/-!
# Chow's lemma over an affine Noetherian base

Chow's lemma for algebraic spaces over an affine Noetherian base scheme `S`: an algebraic space
`X` separated and of finite type over `S` has a `U`-admissible blowup `X' ⟶ X`, for a dense open
subspace `U ⊆ X`, where `X'` is a scheme with a quasi-compact immersion into `ℙᴺ_S` over `S`.
This is the case of Stacks 088U in which the base `Y` is the affine Noetherian scheme `S`.

The proof follows Stacks 088R, 088S and the last paragraph of the proof of 088U. A dense affine
open `D ⊆ X` immerses into `ℙⁿ_S` (Stacks 088N in the affine case); let `Z` be its closure. The
flattened graph closure of `AlgebraicGeometry.Space.C1573.exists_flattenedGraphClosure` provides a
`D`-admissible blowup `Z₂ ⟶ Z` and an open `T₀ ⊆ Z₂` mapping to `X`, an isomorphism over `D`.
`Z₂` is H-projective over `S` (Stacks 087S, 01WE), and the rational map `X ⇢ T₀` is resolved by
the blowup of `X` in a finitely presented centre avoiding a dense open, which is the blowup of
`T₀` in the pulled back centre
(`AlgebraicGeometry.Space.C1573.exists_isBlowupAlong_resolution`). That blowup is H-projective
over `T₀`, hence immerses into projective space over `S`.

## Main results

* `AlgebraicGeometry.Space.C1573.isNoetherian_of_isFiniteType_of_isAffine`: a separated algebraic
  space of finite type over an affine Noetherian scheme is Noetherian.
* `AlgebraicGeometry.Space.C1573.exists_isAdmissibleBlowup_isImmersion_of_isAffine`: the statement
  above.

## References

* [Stacks Project, Tag 088U](https://stacks.math.columbia.edu/tag/088U)
* [Stacks Project, Tag 088R](https://stacks.math.columbia.edu/tag/088R)
-/

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
  _root_.CategoryTheory.Limits.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space of finite type and separated over an affine Noetherian scheme is
Noetherian**. -/
theorem C1573.isNoetherian_of_isFiniteType_of_isAffine [IsAffine S]
    [_root_.AlgebraicGeometry.IsNoetherian S]
    (X : AlgebraicSpaces B S hS) (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) :
    IsNoetherian B S hS B.contains_terminal X.1 := by
  have hY := isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))
  have hSaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS)))) :=
    inferInstanceAs (IsAffine S)
  refine ⟨isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ hSaff) hft.2,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal X.2
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ B.contains_terminal
        ⟨Over.mk (𝟙 (B.obj hS)), inferInstanceAs (QuasiSeparatedSpace S),
          ⟨Functor.RepresentableBy.yoneda _⟩⟩)
      (isQuasiSeparated_of_isSeparated B S hS hsep),
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 hY f hft.1
      ((exists_atlas_iff_of_representable B S hS (yoneda.obj (Over.mk (𝟙 (B.obj hS))))
        (fun T : Scheme.{u} => IsLocallyNoetherian T) (Over.mk (𝟙 (B.obj hS))) (Iso.refl _)).2
        (inferInstanceAs (IsLocallyNoetherian S)))⟩

/-- **The Chow datum over an affine Noetherian base.** Let `S` be an affine Noetherian scheme,
`X` an algebraic space separated and of finite type over `S`, and `f : X ⟶ Y` a morphism to a
presheaf separated over `S`. Then there is a `ChowDatum` for `f`: a dense affine open of `X`, its
closure in a projective space over `S` flattened by a blowup (Stacks 0815, 0879), and the
resulting immersion of the graph closure into a projective space over `Y`. -/
theorem C1573.exists_chowDatum_of_isAffine
    [IsAffine S] [_root_.AlgebraicGeometry.IsNoetherian S]
    (X : AlgebraicSpaces B S hS) (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f₀ : X.1 ⟶ Y)
    (hYsep : IsSeparated B S hS ((isTerminal_yoneda_obj_base B S hS).from Y)) :
    Nonempty (ChowDatum X f₀) := by
  let := BigFppfOver.hasSheafify_type B S hS
  let := pointTopology B S hS X.1
  have hXN := isNoetherian_of_isFiniteType_of_isAffine X f hsep hft
  have hY := isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))
  have hterm : ∀ {W : BigFppfOver B S hS}
      (x y : yoneda.obj W ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))), x = y :=
    fun x y => (isTerminal_yoneda_obj_base B S hS).hom_ext _ _
  obtain ⟨D, u, hDaff, hu, hudense⟩ :=
    exists_dense_affine_openImmersion_self B S hS B.contains_terminal X.1 X.2 hXN
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj D) := hDaff
  have : IsAffine (B.inclusion.obj D.left) := hDaff
  have : IsAffine (B.inclusion.obj (B.obj hS)) := inferInstanceAs (IsAffine S)
  set d : D ⟶ Over.mk (𝟙 (B.obj hS)) := Over.homMk D.hom (by simp)
  have hlft : ∀ {W : BigFppfOver B S hS} (w : yoneda.obj W ⟶ X.1), IsEtale B S hS w →
      LocallyOfFiniteType (B.inclusion.map W.hom) := fun {W} w hw => by
    have h1 := isLocallyOfFiniteType_comp' B S hS w f X.2 hY
      (isLocallyOfFiniteType_of_isEtale' B S hS w hw) hft.1
    rw [hterm (w ≫ f) (yoneda.map (Over.homMk W.hom (by simp)))] at h1
    exact (isLocallyOfFiniteType_yoneda_map_iff B S hS _).1 h1
  have hDlft := hlft u (isEtale_of_isOpenImmersion B S hS hu)
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) :=
    inferInstanceAs (IsLocallyNoetherian S)
  have hDnoeth : IsLocallyNoetherian (B.inclusion.obj D.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map D.hom)
  obtain ⟨n, ι₀, hι₀, hι₀S⟩ :=
    exists_isImmersion_projectiveSpaceOver_of_isAffine (B.inclusion.map D.hom)
  have : _root_.AlgebraicGeometry.IsImmersion ι₀ := hι₀
  have : QuasiCompact ι₀ := by
    have : QuasiCompact (ι₀ ≫ (projectiveSpaceOver n (B.inclusion.obj (B.obj hS)) ↘
        B.inclusion.obj (B.obj hS))) := by
      rw [hι₀S]; infer_instance
    exact QuasiCompact.of_comp ι₀
      (projectiveSpaceOver n (B.inclusion.obj (B.obj hS)) ↘ B.inclusion.obj (B.obj hS))
  have : AlgebraicGeometry.IsOpenImmersion ι₀.toImage := isOpenImmersion_toImage ι₀ (.inl ‹_›)
  have hPS : B.Contains (projectiveSpaceOver n (B.inclusion.obj (B.obj hS))) := by
    have := isProper_projectiveSpaceOver n (B.inclusion.obj (B.obj hS))
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (projectiveSpaceOver n (B.inclusion.obj (B.obj hS)) ↘ B.inclusion.obj (B.obj hS)) hS
  have hcZ : B.Contains ι₀.image := Scheme.size_lt_of_isClosedImmersion ι₀.imageι hPS
  set pZ := ι₀.imageι ≫ (projectiveSpaceOver n (B.inclusion.obj (B.obj hS)) ↘
    B.inclusion.obj (B.obj hS)) with hpZ
  set Z := BigFppfOver.mk B S hS hcZ pZ
  set j₀ : D ⟶ Z := BigFppfOver.homMk B S hS hcZ pZ ι₀.toImage (by
    rw [hpZ, ← Category.assoc, Scheme.Hom.toImage_imageι, hι₀S])
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j₀) :=
    inferInstanceAs (AlgebraicGeometry.IsOpenImmersion ι₀.toImage)
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map j₀) := by
    change QuasiCompact ι₀.toImage
    have : QuasiCompact (ι₀.toImage ≫ ι₀.imageι) := by
      rw [Scheme.Hom.toImage_imageι]; infer_instance
    exact QuasiCompact.of_comp _ ι₀.imageι
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj D) := inferInstance
  have hPc : CompactSpace (projectiveSpaceOver n (B.inclusion.obj (B.obj hS))) := by
    have := isProper_projectiveSpaceOver n (B.inclusion.obj (B.obj hS))
    exact (quasiCompact_iff_compactSpace
      (projectiveSpaceOver n (B.inclusion.obj (B.obj hS)) ↘ B.inclusion.obj (B.obj hS))).1
        inferInstance
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj Z) := by
    change CompactSpace ι₀.image
    exact (quasiCompact_iff_compactSpace pZ).1 inferInstance
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Z) := by
    change QuasiSeparatedSpace ι₀.image
    exact (quasiSeparated_iff_quasiSeparatedSpace pZ).1 inferInstance
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Z) := by
    change IsLocallyNoetherian ι₀.image
    exact LocallyOfFiniteType.isLocallyNoetherian pZ
  have : _root_.AlgebraicGeometry.IsSeparated (B.inclusion.map Z.hom) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsSeparated pZ)
  have huqc : IsQuasiCompact B S hS u := by
    refine isQuasiCompact_of_comp_of_isQuasiSeparated B S hS u f
      (isAlgebraicSpace_yoneda B S hS D) hY ?_ (isQuasiSeparated_of_isSeparated B S hS hsep)
    rw [hterm (u ≫ f) (yoneda.map d)]
    exact isQuasiCompact_yoneda_map B S hS d
      (inferInstanceAs (QuasiCompact (B.inclusion.map D.hom)))
  have : CompactSpace S := inferInstance
  obtain ⟨V, φ, hVaff, hφs, hφet⟩ :=
    exists_isAffine_isEtale_isSurjective_chart_of_isQuasiCompact B S hS X.2 f hft.2
  have hφe := (isEtale_iff_presheaf_of_yoneda B S hS φ).1 hφet
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVaff
  have : IsAffine (B.inclusion.obj V.left) := hVaff
  have hVlft := hlft φ hφet
  have : IsLocallyNoetherian (B.inclusion.obj V.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map V.hom)
  have : QuasiCompact (B.inclusion.map Z.hom) := inferInstanceAs (QuasiCompact pZ)
  have : CompactSpace (B.inclusion.obj V.left) := inferInstance
  obtain ⟨K, hKfp, hK, Z₂, T₀, TV, b, eZ₂, o, τ, σ, pT, tV, cS, heZ₂, hoopen, hσj, hσu, hσpb,
      hsq, hcS, hc1, hc2⟩ :=
    exists_flattenedGraphClosure X f hsep hft.1 u hu j₀ huqc φ hφs hφe
  obtain ⟨MS, hMSi, hMS⟩ := Stacks.HProjective.exists_isAmple_of_isAffine
    (B.inclusion.obj (B.obj hS))
  have hZproj : IsProjectiveMorphism pZ := ⟨n, ι₀.imageι, inferInstance, rfl⟩
  obtain ⟨MZ, hMZi, hMZ⟩ := exists_isAmple_of_isProjectiveMorphism pZ MS hMS hZproj
  have hKft : K.IsFiniteType := (finitePresentation_subschemeι_iff_isFiniteType K).mp hKfp
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj Z) MZ := hMZi
  have hbproj : IsProjectiveMorphism (AlgebraicGeometry.blowUpToBase K) :=
    isProjectiveMorphism_blowUpToBase K hKft MZ hMZ
  have hZ₂w : B.inclusion.map Z₂.hom =
      (eZ₂.hom ≫ AlgebraicGeometry.blowUpToBase K) ≫ pZ := by
    rw [heZ₂]
    change _ = B.inclusion.map b.left ≫ B.inclusion.map Z.hom
    rw [← B.inclusion.map_comp, Over.w b]
  have hZ₂proj : IsProjectiveMorphism (B.inclusion.map Z₂.hom) := by
    rw [hZ₂w]
    refine IsProjectiveMorphism.comp ?_ hZproj
    obtain ⟨a, i', hi', hi'o⟩ := hbproj
    exact ⟨a, eZ₂.hom ≫ i', inferInstance, by rw [Category.assoc, hi'o]⟩
  obtain ⟨m, i, hi, hiS⟩ := hZ₂proj
  have hRaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hφs)) := by
    have hw : (BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hφs) ≫
        B.inclusion.map V.hom = (BigFppfOver.toScheme B S hS).map
          (atlasRelationSource B S hS hφs) ≫ B.inclusion.map V.hom := by
      change B.inclusion.map (atlasRelationTarget B S hS hφs).left ≫ _ =
        B.inclusion.map (atlasRelationSource B S hS hφs).left ≫ _
      rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, Over.w, Over.w]
    have := isClosedImmersion_toScheme_lift_of_isSeparated X f hsep φ φ _ _
      (isPullback_yoneda_map_atlasRelation B S hS hφs) hw
    exact isAffine_of_isAffineHom (pullback.lift _ _ hw)
  have : LocallyOfFiniteType (B.inclusion.map Z₂.hom) := by
    have := isProper_of_isProjectiveMorphism _ ⟨m, i, hi, hiS⟩
    infer_instance
  have : IsLocallyNoetherian (B.inclusion.obj Z₂.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map Z₂.hom)
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Z₂) :=
    inferInstanceAs (IsLocallyNoetherian (B.inclusion.obj Z₂.left))
  have hT₀N : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T₀) := by
    have := hoopen
    exact LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map o)
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj TV) := by
    have hbc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    have := (presheaf_yoneda_map_etale_iff B S hS pT).1 (hbc.of_isPullback hsq.flip hφe)
    exact LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map pT)
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    inferInstanceAs (IsLocallyNoetherian (B.inclusion.obj V.left))
  have : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj D) :=
    { toIsLocallyNoetherian := hDnoeth }
  have : Finite (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj D)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have := hcS
  have hZ₂c : CompactSpace ((BigFppfOver.toScheme B S hS).obj Z₂) := by
    have := isProper_of_isProjectiveMorphism _ ⟨m, i, hi, hiS⟩
    exact (quasiCompact_iff_compactSpace (B.inclusion.map Z₂.hom)).1 inferInstance
  have : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Z₂) := {}
  have := hoopen
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj T₀) :=
    ⟨((BigFppfOver.toScheme B S hS).map o).isOpenEmbedding.isInducing.isCompact_iff.2
      (NoetherianSpace.isCompact _)⟩
  have hT₀w : B.inclusion.map T₀.hom =
      (BigFppfOver.toScheme B S hS).map o ≫ B.inclusion.map Z₂.hom := by
    change _ = B.inclusion.map o.left ≫ _
    rw [← B.inclusion.map_comp, Over.w o]
  have hZ₂H : Stacks.HProjective.IsHProjective (B.inclusion.map Z₂.hom) := ⟨m, i, hi, hiS⟩
  have hT₀qp : Stacks.HProjective.IsQuasiProjective (B.inclusion.map T₀.hom) := by
    refine Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective _ ?_
    rw [hT₀w]
    exact Stacks.HProjective.isHQuasiProjective_comp_of_isHProjective _ hZ₂H inferInstance
  obtain ⟨MT, hMTi, hMT⟩ := exists_isAmple_of_isQuasiProjective (B.inclusion.map T₀.hom) MS hMS
    hT₀qp
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj T₀) MT := hMTi
  set e : T₀ ⟶ projectiveSpaceSiteObject B S hS m := BigFppfOver.homMk B S hS
    (contains_projectiveSpaceOver B S hS m) _ ((BigFppfOver.toScheme B S hS).map o ≫ i) (by
      rw [Category.assoc]
      change _ ≫ i ≫ (projectiveSpaceOver m (B.inclusion.obj (B.obj hS)) ↘
        B.inclusion.obj (B.obj hS)) = _
      rw [hiS, ← hT₀w])
  have hiS' : _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map e) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map o ≫ i))
  set jT : yoneda.obj T₀ ⟶ projectiveSpacePresheaf B S hS Y m :=
    pullback.lift (τ ≫ f₀) (yoneda.map e) ((isTerminal_yoneda_obj_base B S hS).hom_ext _ _)
  have hjT : IsImmersion B S hS jT := by
    refine isImmersion_of_comp_of_isLocallySeparated B S hS jT (pullback.snd _ _) ?_
      (isLocallySeparated_of_isSeparated B S hS (isSeparated_pullback B S hS _ _ hYsep))
    rw [pullback.lift_snd]
    exact isImmersion_yoneda_map_of_isImmersion e hiS'
  exact ⟨⟨D, V, T₀, TV, Z₂, u, hu, hudense, φ, hφs, hφe, inferInstance, hRaff, inferInstance,
    hT₀N, inferInstance, inferInstance, inferInstance, τ, σ, hσpb, pT, tV, hsq, o, m, i, hi, hiS,
    cS, hcS, hc1, hc2, MT, hMTi, hMT, m, jT, hjT, pullback.lift_fst _ _ _⟩⟩

/-- **Chow's lemma over an affine Noetherian base.** Let `S` be an affine Noetherian scheme and
`X` an algebraic space separated and of finite type over `S`. Then there are a dense open
subspace `U ⊆ X` and a `U`-admissible blowup `X' ⟶ X` where `X'` is a scheme admitting a
quasi-compact immersion into `ℙᴺ_S` over `S`. This is Stacks 088U for the base `Y = S`. -/
theorem C1573.exists_isAdmissibleBlowup_isImmersion_of_isAffine
    [IsAffine S] [_root_.AlgebraicGeometry.IsNoetherian S]
    (X : AlgebraicSpaces B S hS) (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) :
    letI := pointTopology B S hS X.1
    ∃ (U : OpenSubspaces B S hS X.1), DenseRange (pointsMap B S hS U.1.toFunctor U.1.ι) ∧
      ∃ (N : ℕ) (W : BigFppfOver B S hS) (π : schemeSpace W ⟶ X)
        (i : (BigFppfOver.toScheme B S hS).obj W ⟶ projectiveSpaceOver N S),
        IsAdmissibleBlowup B S hS U π ∧ _root_.AlgebraicGeometry.IsImmersion i ∧ QuasiCompact i ∧
          i ≫ (projectiveSpaceOver N S ↘ S) = B.inclusion.map W.hom := by
  let := pointTopology B S hS X.1
  have hid : IsIso ((isTerminal_yoneda_obj_base B S hS).from
      (yoneda.obj (Over.mk (𝟙 (B.obj hS))))) := by
    rw [show (isTerminal_yoneda_obj_base B S hS).from (yoneda.obj (Over.mk (𝟙 (B.obj hS)))) =
      𝟙 _ from (isTerminal_yoneda_obj_base B S hS).hom_ext _ _]
    infer_instance
  obtain ⟨d⟩ := exists_chowDatum_of_isAffine X f hsep hft f
    (isSeparated_of_isIso B S hS ((isTerminal_yoneda_obj_base B S hS).from _))
  obtain ⟨U, hU, N, W, π, iN, hadm, himm, -, hWc⟩ := d.exists_isAdmissibleBlowup
  have : IsIso (pullback.snd ((isTerminal_yoneda_obj_base B S hS).from
      (yoneda.obj (Over.mk (𝟙 (B.obj hS)))))
      ((isTerminal_yoneda_obj_base B S hS).from
        (yoneda.obj (projectiveSpaceSiteObject B S hS N)))) := inferInstance
  set g : W ⟶ projectiveSpaceSiteObject B S hS N := yoneda.preimage (iN ≫ pullback.snd _ _) with hg
  have hgi : IsImmersion B S hS (yoneda.map g) := by
    rw [hg, Functor.map_preimage]
    exact MorphismProperty.RespectsIso.postcomp _ (pullback.snd _ _) iN himm
  have hFg : _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map g) :=
    (presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsImmersion.{u})
      inferInstance g).1 hgi
  have : QuasiSeparatedSpace (projectiveSpaceOver N S) :=
    (quasiSeparated_iff_quasiSeparatedSpace (projectiveSpaceOver N S ↘ S)).1 inferInstance
  have := hWc
  refine ⟨U, hU, N, W, π, (BigFppfOver.toScheme B S hS).map g, hadm, hFg,
    quasiCompact_of_compactSpace _, ?_⟩
  change B.inclusion.map g.left ≫ B.inclusion.map (projectiveSpaceSiteObject B S hS N).hom = _
  rw [← B.inclusion.map_comp, Over.w g]

end AlgebraicGeometry.Space

end
