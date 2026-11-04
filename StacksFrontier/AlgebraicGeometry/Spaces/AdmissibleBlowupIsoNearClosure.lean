module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupStrictTransformSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCompositeCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupStrictTransformSpaceEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceQuasiCompactOperations
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperIsomorphismOverOpenBlowupUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFlatCompositionUnassumed
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsoNearClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformOverAdmissibleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionIntoQuotientStackSubspace

/-!
# An admissible blowup making a proper morphism an isomorphism near a closure

Let `S` be a scheme and let `f : X ⟶ Y` be a proper morphism of quasi-compact and
quasi-separated algebraic spaces over `S`.  Let `V ⊆ Y` be a quasi-compact open subspace, put
`U = f⁻¹(V)`, and let `T ⊆ |V|` be a closed subset such that `f|_U : U ⟶ V` is an isomorphism
over an open neighbourhood of `T` in `V`.  Stacks 0F47 asserts that there is a `V`-admissible
blowup `Y' ⟶ Y` such that the strict transform `f' : X' ⟶ Y'` of `f` is an isomorphism over an
open neighbourhood of the closure of `T` in `|Y'|`.

## Main results

* `AlgebraicGeometry.Space.exists_isBlowupAlong_isIso_strictTransformSpaceToBlowUp_over_closure`:
  a `V`-admissible blowup `Y' ⟶ Y` whose strict transform of `f` is an isomorphism over an open
  neighbourhood of the closure of `T` in `|Y'|`.

## Notation

"Isomorphism over an open subspace `W`" is the statement that the base change `f⁻¹(W) ⟶ W` of
`f` along the inclusion of `W` is an isomorphism, written `IsIso (pullback.snd f W.ι)`.

## References

* [Stacks Project, Tag 0F47](https://stacks.math.columbia.edu/tag/0F47)
* [Stacks Project, Tag 0F46](https://stacks.math.columbia.edu/tag/0F46)
* [Stacks Project, Tag 0GUW](https://stacks.math.columbia.edu/tag/0GUW)
* [Stacks Project, Tag 087F](https://stacks.math.columbia.edu/tag/087F)
* [Stacks Project, Tag 086D](https://stacks.math.columbia.edu/tag/086D)
* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 0868](https://stacks.math.columbia.edu/tag/0868)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0860](https://stacks.math.columbia.edu/tag/0860)
* [Stacks Project, Tag 0A4G](https://stacks.math.columbia.edu/tag/0A4G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0F47.**  Let `S` be a scheme, let `f : X ⟶ Y` be a proper morphism of algebraic
spaces over `S` with `Y` quasi-compact and quasi-separated, let `V ⊆ Y` be a quasi-compact open
subspace and let `T ⊆ |V|` be a closed subset such that `f|_{f⁻¹(V)} : f⁻¹(V) ⟶ V` is an
isomorphism over an open neighbourhood `W` of `T` in `V`.  Then there is a `V`-admissible blowup
`b : Y' ⟶ Y`, the blowup of `Y` in a closed subspace `Yc` of finite presentation whose points
avoid those of `V`, such that the strict transform `f' : X' ⟶ Y'` of `f` is an isomorphism over
an open neighbourhood `W'` of the closure of `T` in `|Y'|`.

An open subspace of `V` is an open subspace `W` of `Y` with `W ≤ V`, and `f|_{f⁻¹(V)}` is an
isomorphism over it exactly when `f` is, i.e. when `f⁻¹(W) ⟶ W` is an isomorphism.  The centre
`Yc` is recorded, since the strict transform is taken relative to it.  The closure of `T` in
`|Y'|` is the closure of the set of points of `Y'` mapping into the image of `T` in `|Y|`, as in
Stacks 0F46 (`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_disjoint_closure`).  The source
also asks `X` to be quasi-compact and quasi-separated; this follows from properness of `f` over
the quasi-compact and quasi-separated `Y`, is not used, and is omitted. -/
@[stacks 0F47]
theorem exists_isBlowupAlong_isIso_strictTransformSpaceToBlowUp_over_closure
    {X Y : AlgebraicSpaces B S hS}
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (V : OpenSubspaces B S hS Y.1) (hVqc : IsQuasiCompactSpace B S hS V.1.toFunctor)
    (T : Set (points B S hS V.1.toFunctor)) (hT : IsClosed T)
    (W : OpenSubspaces B S hS Y.1) (hWV : W.1 ≤ V.1)
    (hTW : pointsMap B S hS _ V.1.ι '' T ⊆ subspacePointSet B S hS Y.1 W.1)
    (hWiso : IsIso (pullback.snd f.hom W.1.ι)) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y) (Yc : ClosedSubspaces B S hS Y.1),
      IsFinitePresentation B S hS Yc.1.ι ∧
        Disjoint (subspacePointSet B S hS Y.1 V.1) (subspacePointSet B S hS Y.1 Yc.1) ∧
          IsBlowupAlong B S hS Yc b ∧
            ∃ W' : OpenSubspaces B S hS Y'.1,
              closure (pointsMap B S hS _ b.hom ⁻¹' (pointsMap B S hS _ V.1.ι '' T)) ⊆
                  subspacePointSet B S hS Y'.1 W'.1 ∧
                IsIso (pullback.snd
                  (strictTransformSpaceToBlowUp B S hS f b (Yc.1.preimage b.hom)).hom
                  W'.1.ι) := by
  classical
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  have : CompactSpace (points B S hS V.1.toFunctor) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS V.2.1 hVqc
  have hVemb : Topology.IsOpenEmbedding (pointsMap B S hS _ V.1.ι) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
      (pointsMap_injective_of_mono B S hS _) (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ V.2.2)
  have : QuasiSeparatedSpace (points B S hS Y.1) :=
    quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS Y.1 Y.2 hYqs
  have : QuasiSeparatedSpace (points B S hS V.1.toFunctor) := hVemb.quasiSeparatedSpace
  have : PrespectralSpace (points B S hS V.1.toFunctor) := prespectralSpace_points B S hS _ V.2.1
  set T' : Set (points B S hS V.1.toFunctor) :=
    pointsMap B S hS _ V.1.ι ⁻¹' (subspacePointSet B S hS Y.1 W.1)ᶜ with hT'def
  have hWopen : IsOpen (subspacePointSet B S hS Y.1 W.1) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS _ W.2.2
  have hT' : IsClosed T' :=
    hWopen.isClosed_compl.preimage (continuous_pointsMap B S hS _)
  have hTT' : Disjoint T T' :=
    Set.disjoint_left.2 fun t ht ht' => ht' (hTW ⟨t, ht, rfl⟩)
  obtain ⟨Tc, T'c, hTc, hT'c, hcTc, hcT'c, hTTc, hT'T'c, hTcT'c⟩ :=
    Topology.exists_isConstructible_isClosed_supersets_of_disjoint hT hT' hTT'
  obtain ⟨Y₁, b₁, ⟨Z₁, hZ₁fp, hZ₁V, hb₁⟩, hsep⟩ :=
    exists_isAdmissibleBlowup_disjoint_closure hZ hYqc hYqs V hVqc Tc T'c hTc hT'c hcTc hcT'c
      hTcT'c
  have hb₁P := isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Z₁ b₁ hZ₁fp hb₁
  obtain ⟨hY₁qc, hY₁qs⟩ :=
    isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isBlowupAlong hZ hYqc hYqs hZ₁fp hb₁
  have : CompactSpace (points B S hS Y₁.1) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS Y₁.2 hY₁qc
  have : QuasiSeparatedSpace (points B S hS Y₁.1) :=
    quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS Y₁.1 Y₁.2 hY₁qs
  have : PrespectralSpace (points B S hS Y₁.1) := prespectralSpace_points B S hS _ Y₁.2
  obtain ⟨G, hGc, hGo, hKG, hGK'⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    isClosed_closure.isCompact isClosed_closure.isOpen_compl
    (Set.subset_compl_iff_disjoint_right.2 hsep)
  set Y₀s := openSubspaceOfPoints B S hS Y₁.1 G with hY₀s
  have hY₀ : IsOpenSubspace B S hS Y₀s := isOpenSubspace_openSubspaceOfPoints B S hS Y₁.2 G hGo
  have hY₀pts : subspacePointSet B S hS Y₁.1 Y₀s = G :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS G
  have hY₀qc : IsQuasiCompactSpace B S hS Y₀s.toFunctor :=
    isQuasiCompactSpace_openSubspaceOfPoints hGo hGc
  have hY₀qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₀s.toFunctor :=
    isAbsolutelyQuasiSeparated_of_mono B S hS hZ hY₀.1 Y₀s.ι inferInstance hY₁qs
  set Y₀ : AlgebraicSpaces B S hS := ⟨Y₀s.toFunctor, hY₀.1⟩ with hY₀def
  set v : Y₀ ⟶ Y₁ := ObjectProperty.homMk Y₀s.ι with hv
  set f₁ := strictTransformSpaceToBlowUp B S hS f b₁ (Z₁.1.preimage b₁.hom) with hf₁def
  have hf₁ : IsProper B S hS f₁.hom :=
    isProper_comp B S hS (strictTransformSpace B S hS f b₁ (Z₁.1.preimage b₁.hom)).2
      (strictTransformPullback B S hS f b₁).2 Y₁.2 _ _
      (isProper_of_isClosedImmersion B S hS
        (strictTransformSpace B S hS f b₁ (Z₁.1.preimage b₁.hom)).2
        (strictTransformPullback B S hS f b₁).2 _
        (strictTransform B S hS f b₁ (Z₁.1.preimage b₁.hom)).2.2)
      ((isProper_isStableUnderBaseChange B S hS).of_isPullback
        (AlgebraicSpaces.isPullback_fiberProduct B S hS f b₁) hf)
  set V₁ : OpenSubspaces B S hS Y₁.1 :=
    ⟨V.1.preimage b₁.hom, isOpenSubspace_preimage B S hS b₁.hom V.1 Y.2 Y₁.2 V.2⟩ with hV₁
  have hV₁qc : IsQuasiCompactSpace B S hS V₁.1.toFunctor :=
    isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS Y.2 Y₁.2 b₁.hom hb₁P.2.1.2 V.2 hVqc
  have hWZ₁ : Disjoint (subspacePointSet B S hS Y.1 W.1) (subspacePointSet B S hS Y.1 Z₁.1) :=
    hZ₁V.mono_left (range_pointsMap_ι_le B S hS hWV)
  have hf₁W : IsIso (pullback.snd f₁.hom (W.1.preimage b₁.hom).ι) :=
    isIso_pullbackSnd_strictTransformSpaceToBlowUp f b₁ Z₁ hb₁ W hWZ₁ hWiso
  have hX₁₀ : IsOpenSubspace B S hS (Y₀s.preimage f₁.hom) :=
    isOpenSubspace_preimage B S hS f₁.hom Y₀s Y₁.2
      (strictTransformSpace B S hS f b₁ (Z₁.1.preimage b₁.hom)).2 hY₀
  set X₁₀ : AlgebraicSpaces B S hS := ⟨(Y₀s.preimage f₁.hom).toFunctor, hX₁₀.1⟩ with hX₁₀def
  set u : X₁₀ ⟶ strictTransformSpace B S hS f b₁ (Z₁.1.preimage b₁.hom) :=
    ObjectProperty.homMk (Y₀s.preimage f₁.hom).ι with hu
  set w : X₁₀ ⟶ Y₀ := ObjectProperty.homMk (Y₀s.fromPreimage f₁.hom) with hw
  have hsq : IsPullback u.hom w.hom f₁.hom v.hom :=
    (Subfunctor.isPullback_preimage f₁.hom Y₀s).flip
  have hsqA : IsPullback u w f₁ v :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) hsq
  have hwP : IsProper B S hS w.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback hsqA hf₁
  set U₀ : OpenSubspaces B S hS Y₀.1 :=
    ⟨V₁.1.preimage Y₀s.ι, isOpenSubspace_preimage B S hS Y₀s.ι V₁.1 Y₁.2 hY₀.1 V₁.2⟩ with hU₀
  have hpre : ∀ (A : Subfunctor Y.1) (x : points B S hS Y₁.1),
      x ∈ subspacePointSet B S hS Y₁.1 (A.preimage b₁.hom) ↔
        pointsMap B S hS _ b₁.hom x ∈ subspacePointSet B S hS Y.1 A := fun A x =>
    Set.ext_iff.1 (range_pointsMap_preimage_ι B S hS b₁.hom A) x
  have hU₀W : V₁.1 ⊓ Y₀s ≤ W.1.preimage b₁.hom := by
    refine le_of_subspacePointSet_subset Y₁.2 (isOpenSubspace_inf B S hS Y₁.2 _ _ V₁.2 hY₀)
      (isOpenSubspace_preimage B S hS b₁.hom W.1 Y.2 Y₁.2 W.2) ?_
    rintro x hx
    rw [subspacePointSet_inf] at hx
    obtain ⟨hxV, hxG⟩ := hx
    rw [hY₀pts] at hxG
    rw [hpre]
    obtain ⟨t, ht⟩ := (hpre _ x).1 hxV
    by_contra hxW
    refine hGK' hxG (subset_closure ⟨t, hT'T'c ?_, ht⟩)
    change pointsMap B S hS _ V.1.ι t ∈ (subspacePointSet B S hS Y.1 W.1)ᶜ
    rwa [ht]
  have hw_iso : IsIso (pullback.snd w.hom U₀.1.ι) := by
    refine isIso_pullbackSnd_of_isPullback_of_isIso_comp hsq U₀.1.ι ?_
    have hle : Subfunctor.range (U₀.1.ι ≫ Y₀s.ι) ≤ W.1.preimage b₁.hom := by
      refine le_trans ?_ hU₀W
      rintro _ _ ⟨y, rfl⟩
      exact ⟨y.2, y.1.2⟩
    exact isIso_pullbackSnd_of_eq_comp _ _ _ (Subfunctor.lift_ι (U₀.1.ι ≫ Y₀s.ι) hle).symm hf₁W
  have hU₀qc : IsQuasiCompactSpace B S hS U₀.1.toFunctor := by
    refine isQuasiCompactSpace_of_isOpenImmersion_of_isCompact U₀.2.1 (U₀.1.ι ≫ Y₀s.ι)
      (isOpenImmersion_comp B S hS _ _ U₀.2.2 hY₀.2) ?_
    have hr : Set.range (pointsMap B S hS _ U₀.1.ι) =
        pointsMap B S hS _ Y₀s.ι ⁻¹' subspacePointSet B S hS Y₁.1 V₁.1 :=
      range_pointsMap_preimage_ι B S hS Y₀s.ι V₁.1
    rw [pointsMap_comp, Set.range_comp, hr, Set.image_preimage_eq_inter_range]
    change IsCompact (subspacePointSet B S hS Y₁.1 V₁.1 ∩ subspacePointSet B S hS Y₁.1 Y₀s)
    rw [hY₀pts]
    exact (isCompact_range_of_isQuasiCompactSpace B S hS V₁.2 hV₁qc).inter_of_isOpen hGc
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS _ V₁.2.2) hGo
  obtain ⟨Y'₀, c₀, Z'₀, hZ'₀fp, hZ'₀U₀, hc₀, hF₀iso⟩ :=
    exists_isBlowupAlong_isIso_strictTransformSpaceToBlowUp_of_isProper_unconditional w U₀
      hY₀qc hY₀qs hU₀qc hwP hw_iso
  obtain ⟨Z's, hZ'c, hZ'fp, hZ'V₁, hZ'Y₀⟩ := exists_closedSubspace_extension_disjoint hZ hY₁qc
    hY₁qs V₁.1 Y₀s V₁.2 hY₀ hV₁qc hY₀qc Z'₀.1 Z'₀.2 hZ'₀fp hZ'₀U₀
  set Z' : ClosedSubspaces B S hS Y₁.1 := ⟨Z's, hZ'c⟩ with hZ'def
  obtain ⟨Y', c, hc⟩ := exists_isBlowupAlong_of_isFinitePresentation Z' hZ'fp
  obtain ⟨Yc, hYcfp, hYccomp, hYcb⟩ :=
    exists_isCompositeCentre_isBlowupAlong_of_isQuasiCompactSpace hZ hYqc hYqs hb₁ hZ₁fp hc hZ'fp
  have hYcV : Disjoint (subspacePointSet B S hS Y.1 V.1) (subspacePointSet B S hS Y.1 Yc.1) := by
    rw [show subspacePointSet B S hS Y.1 Yc.1 = subspacePointSet B S hS Y.1 Z₁.1 ∪
        pointsMap B S hS Y₁.1 b₁.hom '' subspacePointSet B S hS Y₁.1 Z'.1 from hYccomp]
    refine Set.disjoint_union_right.2 ⟨hZ₁V, Set.disjoint_left.2 fun y hyV ⟨z, hz, hzy⟩ => ?_⟩
    exact Set.disjoint_left.1 hZ'V₁ ((hpre V.1 z).2 (hzy ▸ hyV)) hz
  have hvE : IsEtale B S hS v.hom := isEtale_ι_of_isOpenSubspace hY₀
  have huE : IsEtale B S hS u.hom := isEtale_ι_of_isOpenSubspace hX₁₀
  have hcomm : u ≫ f₁ = w ≫ v := ObjectProperty.hom_ext _ hsq.w
  have hpre : preimageClosedSubspace v Z' = Z'₀ := Subtype.ext hZ'Y₀
  have hv' : IsBlowupAlong B S hS (preimageClosedSubspace v Z') c₀ := hpre ▸ hc₀
  obtain ⟨m, can, hsqm, -, -, hcanB, hcanP, hST⟩ :=
    exists_strictTransform_eq_preimage_of_isEtale B S hS hc hvE huE hcomm hv'
      (strictTransform_exists_of_isEffectiveCartierDivisor B S hS f₁ c
        (preimageClosedSubspace c Z') hc.isPullbackDefined)
  obtain ⟨k, j, -, hk, hj⟩ :=
    exists_strictTransformSpace_comp_iso_unconditional B S hS f b₁ c Z₁ Z' Yc hb₁ hc hYccomp hYcb
  refine ⟨Y', c ≫ b₁, Yc, hYcfp, hYcV, hYcb, ?_⟩
  set F₀ := strictTransformSpaceToBlowUp B S hS w c₀ (Z'₀.1.preimage c₀.hom) with hF₀
  set F'' := strictTransformSpaceToBlowUp B S hS f₁ c (Z'.1.preimage c.hom) with hF''
  set F' := strictTransformSpaceToBlowUp B S hS f (c ≫ b₁) (Yc.1.preimage (c ≫ b₁).hom)
    with hF'
  have hF''F' : F'' = j.hom ≫ F' := by
    simp only [hF'', hF', strictTransformSpaceToBlowUp]
    rw [← Category.assoc, hj, Category.assoc, hk]
  have hm : IsOpenImmersion B S hS m.hom := isOpenImmersion_of_isPullback B S hS hsqm hY₀.2
  have : Mono m.hom := mono_of_isOpenImmersion B S hS _ hm
  set W's := Subfunctor.range m.hom with hW's
  have hW' : IsOpenSubspace B S hS W's :=
    isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace B S hS _ Y'₀.2 hm
  refine ⟨⟨W's, hW'⟩, ?_, ?_⟩
  · intro x hx
    have hβ : pointsMap B S hS _ (c ≫ b₁).hom ⁻¹' (pointsMap B S hS _ V.1.ι '' T) ⊆
        pointsMap B S hS _ c.hom ⁻¹'
          closure (pointsMap B S hS _ b₁.hom ⁻¹' (pointsMap B S hS _ V.1.ι '' Tc)) := by
      rintro y ⟨t, ht, hty⟩
      refine subset_closure ⟨t, hTTc ht, ?_⟩
      rw [hty]
      exact pointsMap_comp_apply B S hS c.hom b₁.hom y
    have hxK := closure_minimal hβ
      (isClosed_closure.preimage (continuous_pointsMap B S hS c.hom)) hx
    obtain ⟨g₀, hg₀⟩ : pointsMap B S hS _ c.hom x ∈ subspacePointSet B S hS Y₁.1 Y₀s :=
      hY₀pts ▸ hKG hxK
    obtain ⟨p, -, hp⟩ := exists_points_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_hom B S hS hsqm) g₀ x hg₀
    change _ ∈ subspacePointSet B S hS Y'.1 W's
    rw [subspacePointSet_range]
    exact ⟨p, hp⟩
  · rw [hpre] at hST
    obtain ⟨φ, hS1⟩ := exists_isPullback_of_eq_preimage can.hom hST
    have hS2 : IsPullback can.hom (strictTransformPullbackToBlowUp B S hS w c₀).hom
        (strictTransformPullbackToBlowUp B S hS f₁ c).hom m.hom :=
      IsPullback.of_cube pullback.condition pullback.condition hsq
        (AlgebraicSpaces.isPullback_hom B S hS hsqm) (AlgebraicSpaces.isPullback_hom B S hS hcanP)
        (congrArg (fun k => k.hom) hcanB)
    have hQ : IsPullback φ F₀.hom F''.hom m.hom := hS1.paste_vert hS2
    have hA3 : IsIso (pullback.snd F''.hom m.hom) := isIso_pullbackSnd_of_isPullback hQ hF₀iso
    have hA4 : IsIso (pullback.snd F''.hom W's.ι) :=
      isIso_pullbackSnd_of_isIso_comp F''.hom W's.ι (asIso (Subfunctor.toRange m.hom))
        (isIso_pullbackSnd_of_eq rfl (Subfunctor.toRange_ι _).symm hA3)
    let jP : (strictTransformSpace B S hS f₁ c (Z'.1.preimage c.hom)).1 ≅
        (strictTransformSpace B S hS f (c ≫ b₁) (Yc.1.preimage (c ≫ b₁).hom)).1 :=
      { hom := j.hom.hom, inv := j.inv.hom,
        hom_inv_id := congrArg (fun k => k.hom) j.hom_inv_id,
        inv_hom_id := congrArg (fun k => k.hom) j.inv_hom_id }
    refine isIso_pullbackSnd_of_eq ?_ rfl (isIso_pullbackSnd_iso_comp jP.symm F''.hom W's.ι hA4)
    rw [hF''F']
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ F'.hom) (congrArg (fun k => k.hom) j.inv_hom_id)).trans
        (Category.id_comp _))

end AlgebraicGeometry.Space

end
