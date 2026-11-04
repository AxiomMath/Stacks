module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Extension
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.DeformationDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Scheme models of a cartesian morphism of thickenings of algebraic spaces

A cartesian morphism of thickenings of algebraic spaces over `S` can be presented by a
cartesian morphism of thickenings of *schemes*: choose a surjective étale chart `V' → Y'` of
the ambient target, lift it through the ambient morphism to a surjective étale chart
`U' → X' ×_{Y'} V'` of the ambient source, and base change both charts along the two
inclusions. The two resulting vertical maps of the site are thickenings of schemes and the
square they form with the two horizontal maps is cartesian.

## Main definitions

* `AlgebraicGeometry.Space.SchemeModels` records the four charts of the site, their
  surjectivity and étaleness, the two cartesian squares exhibiting the lower row as the base
  change of the upper one, and the thickening and cartesianness properties of the resulting
  morphism of thickenings of schemes.

## Main results

* `AlgebraicGeometry.Space.exists_schemeModels`: every cartesian morphism of thickenings of
  algebraic spaces admits such a model.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_cartesianMorphismOfThickenings`: a
  property of morphisms of schemes which is étale local on the source and target is invariant
  under a cartesian morphism of thickenings of algebraic spaces as soon as it is invariant
  under every cartesian, locally finite type morphism of thickenings of schemes.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme-level cartesian model of a cartesian morphism of thickenings of algebraic
spaces over `S`. The upper-row charts `V'` and `U'` cover the ambient algebraic spaces; the
lower-row charts `V` and `U` are their base changes along the two thickening inclusions. -/
structure SchemeModels
    (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) where
  /-- The chart of the ambient target. -/
  V' : BigFppfOver B S hS
  /-- The chart of the ambient source. -/
  U' : BigFppfOver B S hS
  /-- The chart of the smaller target. -/
  V : BigFppfOver B S hS
  /-- The chart of the smaller source. -/
  U : BigFppfOver B S hS
  /-- The atlas `V' → Y'` of the ambient target. -/
  v' : yoneda.obj V' ⟶ T.Y'.1
  /-- The atlas of the ambient target is surjective. -/
  v'_surjective : (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf v'
  /-- The atlas of the ambient target is étale. -/
  v'_etale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf v'
  /-- The atlas `U' → X' ×_{Y'} V'` of the ambient source over the chosen target chart. -/
  u' : yoneda.obj U' ⟶ pullback T.f' v'
  /-- The atlas of the ambient source is surjective. -/
  u'_surjective : (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf u'
  /-- The atlas of the ambient source is étale. -/
  u'_etale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf u'
  /-- The vertical map of target charts. -/
  v_to_V' : V ⟶ V'
  /-- The vertical map of source charts. -/
  u_to_U' : U ⟶ U'
  /-- The horizontal map of the lower row. -/
  f_scheme : U ⟶ V
  /-- The horizontal map of the upper row. -/
  f'_scheme : U' ⟶ V'
  /-- The chart `V → Y` of the smaller target. -/
  v : yoneda.obj V ⟶ T.Y.toFunctor
  /-- The chart `U → X` of the smaller source. -/
  u : yoneda.obj U ⟶ T.X.toFunctor
  /-- The chart of the smaller target is surjective. -/
  v_surjective : (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf v
  /-- The chart of the smaller target is étale. -/
  v_etale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf v
  /-- The chart of the smaller source is surjective. -/
  u_surjective : (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf u
  /-- The chart of the smaller source is étale. -/
  u_etale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf u
  /-- The target chart is `Y ×_{Y'} V'`. -/
  target_pullback : IsPullback v (yoneda.map v_to_V') T.Y.ι v'
  /-- The source chart is `X ×_{X'} U'`. -/
  source_pullback :
    IsPullback u (yoneda.map u_to_U') T.X.ι (u' ≫ pullback.fst T.f' v')
  /-- The map between ambient charts is the projection of the source atlas. -/
  ambient_compat : yoneda.map f'_scheme = u' ≫ pullback.snd T.f' v'
  /-- The map of smaller charts lies over `f`. -/
  small_compat : u ≫ T.f = yoneda.map f_scheme ≫ v
  /-- The vertical map of source charts is a thickening of schemes. -/
  source_thickening :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map u_to_U')
  /-- The vertical map of target charts is a thickening of schemes. -/
  target_thickening :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map v_to_V')
  /-- The resulting morphism of thickenings of schemes is cartesian. -/
  cartesian :
    IsPullback ((BigFppfOver.toScheme B S hS).map f_scheme)
      ((BigFppfOver.toScheme B S hS).map u_to_U')
      ((BigFppfOver.toScheme B S hS).map v_to_V')
      ((BigFppfOver.toScheme B S hS).map f'_scheme)

/-- Surjective étale charts of the two ambient algebraic spaces, base changed along the two
thickening inclusions, give a cartesian scheme model of a cartesian morphism of thickenings
of algebraic spaces. -/
theorem exists_schemeModels
    (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) :
    Nonempty (SchemeModels B S hS T) := by
  obtain ⟨V', v', hv'_surjective, hv'_etale⟩ := T.Y'.property.exists_atlas
  have hP : IsAlgebraicSpace B S hS (pullback T.f' v') :=
    isAlgebraicSpace_pullback B S hS T.f' v' T.X'.property
      (isAlgebraicSpace_yoneda B S hS V') T.Y'.property
  obtain ⟨U', u', hu'_surjective, hu'_etale⟩ := hP.exists_atlas
  let Tscheme := BigFppfOver.toScheme B S hS
  let Psurjective :=
    MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Tscheme
  let Petale :=
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Tscheme
  have : Psurjective.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition.{u}
  have : Petale.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have : Psurjective.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have : Petale.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  have : Psurjective.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Psurjective
  have : Petale.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Petale
  have : Psurjective.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Psurjective
  have : Petale.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Petale
  have hYclosed := T.targetThickening.1.2
  have hXclosed := T.sourceThickening.1.2
  let V := hYclosed.1.pullback v'
  let v_to_V' := hYclosed.1.snd v'
  let v := hYclosed.1.fst v'
  have target_pullback : IsPullback v (yoneda.map v_to_V') T.Y.ι v' :=
    hYclosed.1.isPullback v'
  let uambient := u' ≫ pullback.fst T.f' v'
  let U := hXclosed.1.pullback uambient
  let u_to_U' := hXclosed.1.snd uambient
  let u := hXclosed.1.fst uambient
  have source_pullback : IsPullback u (yoneda.map u_to_U') T.X.ι uambient :=
    hXclosed.1.isPullback uambient
  let f'_scheme := yoneda.preimage (u' ≫ pullback.snd T.f' v')
  have ambient_compat : yoneda.map f'_scheme = u' ≫ pullback.snd T.f' v' := by
    simp [f'_scheme]
  have hmor : T.f ≫ T.Y.ι = T.X.ι ≫ T.f' := T.morphism.w
  have hcomp : (u ≫ T.f) ≫ T.Y.ι = yoneda.map (u_to_U' ≫ f'_scheme) ≫ v' := by
    calc
      (u ≫ T.f) ≫ T.Y.ι = u ≫ T.X.ι ≫ T.f' := by
        rw [Category.assoc, hmor]
      _ = yoneda.map u_to_U' ≫ uambient ≫ T.f' := by
        rw [← Category.assoc, source_pullback.w]; simp [Category.assoc]
      _ = yoneda.map u_to_U' ≫ (u' ≫ pullback.snd T.f' v') ≫ v' := by
        simp [uambient, Category.assoc, pullback.condition]
      _ = yoneda.map (u_to_U' ≫ f'_scheme) ≫ v' := by
        rw [← ambient_compat]; simp [Category.assoc]
  let f_pre :=
    target_pullback.lift (u ≫ T.f) (yoneda.map (u_to_U' ≫ f'_scheme)) hcomp
  let f_scheme := yoneda.preimage f_pre
  have small_compat : u ≫ T.f = yoneda.map f_scheme ≫ v := by
    simp [f_scheme, f_pre]
  have hPullP : IsPullback (pullback.fst T.f' v') (pullback.snd T.f' v') T.f' v' :=
    IsPullback.of_hasPullback _ _
  have hv_surjective : Psurjective.presheaf v :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      target_pullback.flip hv'_surjective
  have hv_etale : Petale.presheaf v :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback target_pullback.flip hv'_etale
  have huambient_surjective : Psurjective.presheaf uambient :=
    MorphismProperty.comp_mem Psurjective.presheaf _ _ hu'_surjective
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hPullP.flip hv'_surjective)
  have huambient_etale : Petale.presheaf uambient :=
    MorphismProperty.comp_mem Petale.presheaf _ _ hu'_etale
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hPullP.flip hv'_etale)
  have hu_surjective : Psurjective.presheaf u :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      source_pullback.flip huambient_surjective
  have hu_etale : Petale.presheaf u :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      source_pullback.flip huambient_etale
  let Ysp : AlgebraicSpaces B S hS := ⟨T.Y.toFunctor, T.targetThickening.1.1⟩
  let Xsp : AlgebraicSpaces B S hS := ⟨T.X.toFunctor, T.sourceThickening.1.1⟩
  have hTargetSpace : IsPullback (ObjectProperty.homMk v : schemeSpace V ⟶ Ysp)
      (schemeSpaceMap v_to_V') (ObjectProperty.homMk T.Y.ι : Ysp ⟶ T.Y')
      (ObjectProperty.homMk v' : schemeSpace V' ⟶ T.Y') := by
    apply IsPullback.of_map (ObjectProperty.ι _)
    · apply ObjectProperty.hom_ext
      exact target_pullback.w
    · exact target_pullback
  have hSourceSpace : IsPullback (ObjectProperty.homMk u : schemeSpace U ⟶ Xsp)
      (schemeSpaceMap u_to_U') (ObjectProperty.homMk T.X.ι : Xsp ⟶ T.X')
      (ObjectProperty.homMk uambient : schemeSpace U' ⟶ T.X') := by
    apply IsPullback.of_map (ObjectProperty.ι _)
    · apply ObjectProperty.hom_ext
      exact source_pullback.w
    · exact source_pullback
  have hVToSurjective : Surjective (Tscheme.map v_to_V') :=
    MorphismProperty.of_relative_map (F := yoneda) (P := Psurjective)
      ((surjective_iff_surjective_pointsMap B S hS (yoneda.obj V')
        (isAlgebraicSpace_yoneda B S hS V') V (yoneda.map v_to_V')).mpr
        (isSurjective_of_isPullback B S hS hTargetSpace T.targetThickening.2))
  have hUToSurjective : Surjective (Tscheme.map u_to_U') :=
    MorphismProperty.of_relative_map (F := yoneda) (P := Psurjective)
      ((surjective_iff_surjective_pointsMap B S hS (yoneda.obj U')
        (isAlgebraicSpace_yoneda B S hS U') U (yoneda.map u_to_U')).mpr
        (isSurjective_of_isPullback B S hS hSourceSpace T.sourceThickening.2))
  have hUtoY : IsPullback (u ≫ T.f) (yoneda.map u_to_U') T.Y.ι (uambient ≫ T.f') :=
    IsPullback.paste_horiz source_pullback T.cartesian
  have hrw : yoneda.map f'_scheme ≫ v' = 𝟙 (yoneda.obj U') ≫ (uambient ≫ T.f') := by
    calc
      yoneda.map f'_scheme ≫ v' = (u' ≫ pullback.snd T.f' v') ≫ v' := by
        rw [ambient_compat]
      _ = (u' ≫ pullback.fst T.f' v') ≫ T.f' := by
        simp [Category.assoc, pullback.condition]
      _ = 𝟙 (yoneda.obj U') ≫ (uambient ≫ T.f') := by simp [uambient, Category.assoc]
  let qV := pullback.fst v_to_V' f'_scheme
  let qU' := pullback.snd v_to_V' f'_scheme
  have hQsite : IsPullback qV qU' v_to_V' f'_scheme := IsPullback.of_hasPullback _ _
  have hQ : IsPullback (yoneda.map qV) (yoneda.map qU') (yoneda.map v_to_V')
      (yoneda.map f'_scheme) := IsPullback.map yoneda hQsite
  have hQcomm : (yoneda.map qV ≫ v) ≫ T.Y.ι = yoneda.map qU' ≫ (uambient ≫ T.f') := by
    calc
      (yoneda.map qV ≫ v) ≫ T.Y.ι = (yoneda.map qV ≫ yoneda.map v_to_V') ≫ v' := by
        simp only [Category.assoc, target_pullback.w]
      _ = (yoneda.map qU' ≫ yoneda.map f'_scheme) ≫ v' := by rw [hQ.w]
      _ = yoneda.map qU' ≫ (uambient ≫ T.f') := by rw [Category.assoc, hrw]; simp
  let tpre := hUtoY.lift (yoneda.map qV ≫ v) (yoneda.map qU') hQcomm
  have htpre_fst := hUtoY.lift_fst (yoneda.map qV ≫ v) (yoneda.map qU') hQcomm
  have htpre_snd := hUtoY.lift_snd (yoneda.map qV ≫ v) (yoneda.map qU') hQcomm
  have htpre_f : tpre ≫ yoneda.map f_scheme = yoneda.map qV := by
    refine target_pullback.hom_ext ?_ ?_
    · simpa only [tpre, Category.assoc, small_compat] using htpre_fst
    · calc
        tpre ≫ yoneda.map f_scheme ≫ yoneda.map v_to_V' =
            tpre ≫ yoneda.map u_to_U' ≫ yoneda.map f'_scheme := by
          rw [show yoneda.map f_scheme = f_pre by simp [f_scheme],
            target_pullback.lift_snd (u ≫ T.f) (yoneda.map (u_to_U' ≫ f'_scheme)) hcomp]
          simp [Functor.map_comp]
        _ = yoneda.map qU' ≫ yoneda.map f'_scheme :=
          congrArg (fun k => k ≫ yoneda.map f'_scheme) htpre_snd
        _ = yoneda.map qV ≫ yoneda.map v_to_V' := by rw [hQ.w.symm]
  have hTwist : IsPullback tpre (yoneda.map qU') (yoneda.map u_to_U') (𝟙 (yoneda.obj U')) :=
    IsPullback.paste_twist_right target_pullback hUtoY (yoneda.map f'_scheme)
      (𝟙 (yoneda.obj U')) hrw (yoneda.map qV) (yoneda.map qU') hQ (t := tpre)
      (by simp [tpre]) (by simp [tpre])
  have : IsIso tpre := hTwist.isIso_fst_of_isIso inferInstance
  let t := yoneda.preimage tpre
  have ht_f : t ≫ f_scheme = qV :=
    yoneda.map_injective (by simpa [t, f_scheme, f_pre] using htpre_f)
  have ht_u : t ≫ u_to_U' = qU' := yoneda.map_injective (by simpa [t] using hTwist.w)
  have : IsIso (yoneda.map t) := by simpa [t]
  have : IsIso t := Yoneda.fullyFaithful.isIso_of_isIso_map t
  have hFinalSite : IsPullback f_scheme u_to_U' v_to_V' f'_scheme :=
    IsPullback.of_iso hQsite (asIso t) (Iso.refl V) (Iso.refl U') (Iso.refl V')
      ht_f.symm ht_u.symm (Category.id_comp v_to_V').symm (Category.id_comp f'_scheme).symm
  exact ⟨{ V' := V', U' := U', V := V, U := U
           v' := v', v'_surjective := hv'_surjective, v'_etale := hv'_etale
           u' := u', u'_surjective := hu'_surjective, u'_etale := hu'_etale
           v_to_V' := v_to_V', u_to_U' := u_to_U'
           f_scheme := f_scheme, f'_scheme := f'_scheme
           v := v, u := u
           v_surjective := hv_surjective, v_etale := hv_etale
           u_surjective := hu_surjective, u_etale := hu_etale
           target_pullback := target_pullback
           source_pullback := source_pullback
           ambient_compat := ambient_compat
           small_compat := small_compat
           source_thickening :=
             ⟨hXclosed.2 uambient u u_to_U' source_pullback, hUToSurjective.surj⟩
           target_thickening :=
             ⟨hYclosed.2 v' v v_to_V' target_pullback, hVToSurjective.surj⟩
           cartesian := IsPullback.map Tscheme hFinalSite }⟩

/-- A property of morphisms of schemes which is étale local on the source and target is
invariant under a cartesian morphism of thickenings of algebraic spaces as soon as it is
invariant under every cartesian, locally finite type morphism of thickenings of schemes. -/
theorem holdsOnEveryEtaleChart_iff_of_cartesianMorphismOfThickenings
    (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hSchemes : ∀ E : Stacks.Thickenings.CartesianFiniteTypeMorphism.{u}, P E.f ↔ P E.f') :
    HoldsOnEveryEtaleChart B S hS P T.f ↔ HoldsOnEveryEtaleChart B S hS P T.f' := by
  obtain ⟨M⟩ := exists_schemeModels B S hS T
  let F := BigFppfOver.toScheme B S hS
  let Psurjective := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) F
  let Petale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F
  have : Psurjective.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have : Petale.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  have : Psurjective.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition.{u}
  have : Petale.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have : Psurjective.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : Petale.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : Psurjective.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have : Petale.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have hambientChart : Petale.presheaf (M.u' ≫ pullback.fst T.f' M.v') :=
    MorphismProperty.comp_mem _ _ _ M.u'_etale
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback T.f' M.v').flip M.v'_etale)
  have hambientSurj : Psurjective.presheaf (M.u' ≫ pullback.fst T.f' M.v') :=
    MorphismProperty.comp_mem _ _ _ M.u'_surjective
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback T.f' M.v').flip M.v'_surjective)
  have hambientComm : yoneda.map M.f'_scheme ≫ M.v' =
      (M.u' ≫ pullback.fst T.f' M.v') ≫ T.f' := by
    rw [M.ambient_compat]
    simp only [Category.assoc]
    exact congrArg (fun q => M.u' ≫ q) (IsPullback.of_hasPullback T.f' M.v').w.symm
  have : LocallyOfFiniteType (F.map M.f_scheme) :=
    T.locallyOfFiniteType_left M.U M.V M.u M.v M.f_scheme M.u_etale M.v_etale M.small_compat.symm
  have : LocallyOfFiniteType (F.map M.f'_scheme) :=
    T.locallyOfFiniteType_right M.U' M.V' (M.u' ≫ pullback.fst T.f' M.v') M.v' M.f'_scheme
      hambientChart M.v'_etale hambientComm
  let E : Stacks.Thickenings.CartesianFiniteTypeMorphism.{u} :=
    { X := F.obj M.U
      X' := F.obj M.U'
      Y := F.obj M.V
      Y' := F.obj M.V'
      i := F.map M.u_to_U'
      j := F.map M.v_to_V'
      morphism :=
        { left := F.map M.f_scheme
          right := F.map M.f'_scheme
          w := M.cartesian.w }
      sourceThickening := M.source_thickening
      targetThickening := M.target_thickening
      cartesian := M.cartesian }
  have hsmall : HoldsOnEveryEtaleChart B S hS P T.f ↔ P (F.map M.f_scheme) := by
    refine ⟨fun h => h M.U M.V M.u M.v M.f_scheme M.u_etale M.v_etale M.small_compat.symm,
      fun hp => ?_⟩
    refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP T.sourceThickening.1.1
      T.targetThickening.1.1 T.f).mpr ?_
    exact ⟨M.U, M.V, M.u, M.v, M.f_scheme, M.u_etale, M.v_etale, M.u_surjective,
      M.small_compat.symm, hp⟩
  have hambient : HoldsOnEveryEtaleChart B S hS P T.f' ↔ P (F.map M.f'_scheme) := by
    refine ⟨fun h => h M.U' M.V' (M.u' ≫ pullback.fst T.f' M.v') M.v' M.f'_scheme
      hambientChart M.v'_etale hambientComm, fun hp => ?_⟩
    refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP T.X'.property
      T.Y'.property T.f').mpr ?_
    exact ⟨M.U', M.V', M.u' ≫ pullback.fst T.f' M.v', M.v', M.f'_scheme, hambientChart,
      M.v'_etale, hambientSurj, hambientComm, hp⟩
  exact hsmall.trans ((hSchemes E).trans hambient.symm)

end AlgebraicGeometry.Space

end
