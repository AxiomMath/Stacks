module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LowerSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Lower semicontinuity of the fibre dimension of a flat morphism

The fibre-dimension function of a flat morphism of algebraic spaces over a scheme `S` of finite
presentation is lower semicontinuous on the points of its target.

## Main results

* `AlgebraicGeometry.Space.fiberDimension_yoneda_map_class`: for a morphism of the big fppf site
  the fibre-dimension function of the represented morphism of algebraic spaces is the
  fibre-dimension function of the underlying morphism of schemes.
* `AlgebraicGeometry.Space.lowerSemicontinuous_fiberDimension` is **Stacks 0D4P**.

## Implementation notes

The statement is reduced to the corresponding statement for schemes, Stacks 0D4H, in two steps.

First, for a morphism `h` of the big fppf site over `S` whose represented morphism of algebraic
spaces is of finite type, the fibre dimension of `yoneda.map h` at a field-valued point is the
dimension of the fibre of the morphism of schemes over the corresponding scheme point: by Stacks
0D4M the former is the dimension of a fibre product, which is represented by a fibre product in
the site, whose underlying scheme is the scheme-theoretic fibre because the base is a one-point
affine scheme. Points of a represented presheaf are homeomorphic to points of the representing
scheme (Stacks 03BX), so lower semicontinuity transports.

Second, the general case is local on the target in two stages. An étale atlas of the target is
surjective and open on points, and lower semicontinuity descends along a surjective open map; so
it suffices to treat the base change along the atlas, which by Stacks 0D4N has the same
fibre-dimension function read through the map on points. The atlas is represented, so its points
are those of a scheme, and the question becomes local on that scheme; on an affine open the base
change has an affine surjective étale cover (Stacks 03H6) whose induced morphism of schemes is
flat and of finite presentation, which is the case already treated.

## References

* [Stacks Project, Tag 0D4P](https://stacks.math.columbia.edu/tag/0D4P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a morphism `h` of the big fppf site over `S` whose represented morphism of algebraic
spaces is of finite type, the fibre dimension at a field-valued point of the target is the
dimension of the scheme-theoretic fibre of the underlying morphism of schemes over the
corresponding point.

By Stacks 0D4M the left-hand side is the dimension of the fibre product of `yoneda.map h` with
the morphism the point represents. That fibre product is represented, by a fibre product taken in
the site, and the scheme representing it is the scheme-theoretic fibre: the base of the second
projection is the one-point scheme `Spec k`. -/
theorem fiberDimension_yoneda_map_class {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hft : IsFiniteType B S hS (yoneda.map h))
    (p : FieldValuedPoint B S hS (yoneda.obj V)) :
    fiberDimension B S hS (yoneda.map h) (p.class B S hS (yoneda.obj V)) =
      ((BigFppfOver.toScheme B S hS).map h).fiberDimension (schemePoint B S hS V p) := by
  classical
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget h).mp hft.1
  have hvalue : (yonedaEquiv.symm p.value :
      yoneda.obj (p.siteObject B S hS (yoneda.obj V)) ⟶ yoneda.obj V) = yoneda.map p.value :=
    yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map p.value).symm
  have hsite : IsPullback (yoneda.map (pullback.fst p.value h))
      (yoneda.map (pullback.snd p.value h)) (yonedaEquiv.symm p.value) (yoneda.map h) := by
    rw [hvalue]
    exact Functor.map_isPullback yoneda (IsPullback.of_hasPullback p.value h)
  have hscheme : IsPullback
      ((BigFppfOver.toScheme B S hS).map (pullback.snd p.value h))
      ((BigFppfOver.toScheme B S hS).map (pullback.fst p.value h))
      ((BigFppfOver.toScheme B S hS).map h)
      ((BigFppfOver.toScheme B S hS).map p.value) :=
    (Functor.map_isPullback (BigFppfOver.toScheme B S hS)
      (IsPullback.of_hasPullback p.value h)).flip
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (p.siteObject B S hS (yoneda.obj V))) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have hpre : ((BigFppfOver.toScheme B S hS).map (pullback.fst p.value h)) ⁻¹'
      {(IsLocalRing.closedPoint p.carrier :
        (BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS (yoneda.obj V)))} = Set.univ :=
    Set.eq_univ_of_forall fun z ↦
      Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (@Subsingleton.elim _ hsub _ _))
  have hfibre : topologicalKrullDim
        (((BigFppfOver.toScheme B S hS).map (pullback.fst p.value h)).fiber
          (IsLocalRing.closedPoint p.carrier)) =
      topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj (pullback p.value h)) :=
    IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.isHomeomorph
        ((((BigFppfOver.toScheme B S hS).map (pullback.fst p.value h)).fiberHomeo _).trans
          ((Homeomorph.setCongr hpre).trans
            (Homeomorph.Set.univ
              ((BigFppfOver.toScheme B S hS).obj (pullback p.value h))))))
  calc fiberDimension B S hS (yoneda.map h) (p.class B S hS (yoneda.obj V))
      = dimension B S hS (pullback (yonedaEquiv.symm p.value) (yoneda.map h))
        (isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm p.value) (yoneda.map h)
          (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS (yoneda.obj V)))
          (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)) :=
        (fiberDimension_eq_dimension_pullback B S hS (yoneda.map h)
          (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V) hft p).1
    _ = dimension B S hS (yoneda.obj (pullback p.value h))
          (isAlgebraicSpace_yoneda B S hS (pullback p.value h)) :=
        (dimension_eq_of_iso B S hS (isAlgebraicSpace_yoneda B S hS (pullback p.value h))
          (isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm p.value) (yoneda.map h)
            (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS (yoneda.obj V)))
            (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V))
          (hsite.isoIsPullback _ _ (IsPullback.of_hasPullback _ _))).symm
    _ = topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj (pullback p.value h)) :=
        dimension_yoneda_eq_topologicalKrullDim B S hS (pullback p.value h)
    _ = ((BigFppfOver.toScheme B S hS).map (pullback.fst p.value h)).fiberDimension
          (IsLocalRing.closedPoint p.carrier) := hfibre.symm
    _ = ((BigFppfOver.toScheme B S hS).map h).fiberDimension (schemePoint B S hS V p) :=
        congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback hscheme) _

/-- For a morphism of the big fppf site over `S` which is flat and of finite presentation on
underlying schemes, the fibre-dimension function of the represented morphism of algebraic spaces
is lower semicontinuous: it is the fibre-dimension function of the morphism of schemes read
through the homeomorphism of Stacks 03BX, which is lower semicontinuous by Stacks 0D4H. -/
theorem lowerSemicontinuous_fiberDimension_yoneda_map {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hft : IsFiniteType B S hS (yoneda.map h))
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map h))
    (hfp : FinitePresentation ((BigFppfOver.toScheme B S hS).map h)) :
    LowerSemicontinuous (fiberDimension B S hS (yoneda.map h)) := by
  have hcomp : fiberDimension B S hS (yoneda.map h) =
      ((BigFppfOver.toScheme B S hS).map h).fiberDimension ∘
        schemePointsHomeomorph B S hS V := by
    funext z
    obtain ⟨p, rfl⟩ := Quot.exists_rep z
    exact fiberDimension_yoneda_map_class B S hS h hft p
  rw [hcomp, lowerSemicontinuous_iff_isOpen_preimage]
  intro b
  rw [Set.preimage_comp]
  exact ((lowerSemicontinuous_iff_isOpen_preimage.mp
    (AlgebraicGeometry.lowerSemicontinuous_fiberDimension _ hfp)) b).preimage
    (schemePointsHomeomorph B S hS V).continuous

/-- For a morphism `j : W ⟶ U` of the site, the map on points induced by `yoneda.map j` is the
map of schemes read through the homeomorphisms of Stacks 03BX. -/
theorem pointsMap_yoneda_map_schemePointsHomeomorph_symm {W U : BigFppfOver B S hS} (j : W ⟶ U)
    (x : (BigFppfOver.toScheme B S hS).obj W) :
    pointsMap B S hS (yoneda.obj W) (yoneda.map j) ((schemePointsHomeomorph B S hS W).symm x) =
      (schemePointsHomeomorph B S hS U).symm ((BigFppfOver.toScheme B S hS).map j x) := by
  apply (schemePointsHomeomorph B S hS U).injective
  rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply, pointsToScheme_pointsMap]
  exact congrArg _ ((schemePointsHomeomorph B S hS _).apply_symm_apply x)

section

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)

include hX hY

/-- The affine case of Stacks 0D4P: for a flat morphism of finite presentation and a morphism to
its target from an affine object of the site, the fibre-dimension function of the base change is
lower semicontinuous.

The base change is quasi-compact over an affine base, so it has an affine surjective étale cover
(Stacks 03H6); the induced morphism of schemes is flat and of finite presentation between affine
schemes, and passing to a surjective étale chart of the source does not change the
fibre-dimension function. -/
private theorem lowerSemicontinuous_fiberDimension_pullback_of_isAffine
    (hflat : IsFlat B S hS f) (hfp : IsFinitePresentation B S hS f)
    (W : BigFppfOver B S hS) (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (g : yoneda.obj W ⟶ Y) :
    LowerSemicontinuous (fiberDimension B S hS (pullback.snd f g)) := by
  classical
  have hW := isAlgebraicSpace_yoneda B S hS W
  have hP : IsAlgebraicSpace B S hS (pullback f g) :=
    isAlgebraicSpace_pullback B S hS f g hX hW hY
  have hpb := AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
    (ObjectProperty.homMk g : (⟨yoneda.obj W, hW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
  have hfpq : IsFinitePresentation B S hS (pullback.snd f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃A C : AlgebraicSpaces B S hS⦄ (k : A ⟶ C) ↦ IsFinitePresentation B S hS k.hom)
      hpb hfp
  have hflatq : IsFlat B S hS (pullback.snd f g) :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hpb hflat
  have hPqc : IsQuasiCompactSpace B S hS (pullback f g) :=
    isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry g f)
      (hfp.2.1 (yoneda.obj W) hW (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) g)
  obtain ⟨A, a, hAaff, haSurj, haEtale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (pullback f g) hP).mp hPqc
  have haEt := presheaf_etale_of_isEtale B S hS haEtale
  have hh : yoneda.map (yoneda.preimage (a ≫ pullback.snd f g)) = a ≫ pullback.snd f g :=
    yoneda.map_preimage _
  have hAaffine : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hAaff
  have hc : yoneda.map (yoneda.preimage (a ≫ pullback.snd f g)) ≫ 𝟙 (yoneda.obj W) =
      a ≫ pullback.snd f g := by rw [hh, Category.comp_id]
  have hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (a ≫ pullback.snd f g))) :=
    hfpq.1 A W a (𝟙 (yoneda.obj W)) _ haEt (presheaf_etale_id B S hS W) hc
  have hflatS : Flat ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (a ≫ pullback.snd f g))) :=
    hflatq A W a (𝟙 (yoneda.obj W)) _ haEt (presheaf_etale_id B S hS W) hc
  have hfpS : FinitePresentation ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (a ≫ pullback.snd f g))) :=
    FinitePresentation.mk hlfp inferInstance inferInstance
  have hftq : IsFiniteType B S hS
      (yoneda.map (yoneda.preimage (a ≫ pullback.snd f g))) :=
    ⟨(holdsOnEveryEtaleChart_yoneda_map_iff B S hS
        LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget _).mpr inferInstance,
      quasiCompact_schemeMap_isQuasiCompact B S hS _ hfpS.2.1⟩
  rw [fiberDimension_eq_of_surjective_etale_chart B S hS hP W (pullback.snd f g) A a _
    haEt haSurj hh]
  exact lowerSemicontinuous_fiberDimension_yoneda_map B S hS _ hftq hflatS hfpS

/-- For a morphism `j : W ⟶ U` of the site, the fibre dimension of the base change of `f` along
`yoneda.map j ≫ g` at a scheme point of `W` is that of the base change along `g` at its image. -/
theorem fiberDimension_pullback_snd_yoneda_map_comp {W U : BigFppfOver B S hS} (j : W ⟶ U)
    (g : yoneda.obj U ⟶ Y) (hft : IsFiniteType B S hS f)
    (x : (BigFppfOver.toScheme B S hS).obj W) :
    fiberDimension B S hS (pullback.snd f (yoneda.map j ≫ g))
        ((schemePointsHomeomorph B S hS W).symm x) =
      fiberDimension B S hS (pullback.snd f g)
        ((schemePointsHomeomorph B S hS U).symm ((BigFppfOver.toScheme B S hS).map j x)) := by
  rw [congrFun (fiberDimension_pullback_snd B S hS f (yoneda.map j ≫ g) hX hY
      (isAlgebraicSpace_yoneda B S hS W) hft),
    ← pointsMap_yoneda_map_schemePointsHomeomorph_symm,
    congrFun (fiberDimension_pullback_snd B S hS f g hX hY (isAlgebraicSpace_yoneda B S hS U) hft)]
  simp only [Function.comp_apply, pointsMap_comp_apply]

/-- For an open map of schemes `j : W ⟶ U` of the site and a morphism `g` from `U`, if the
fibre-dimension function of the base change of `f` along `yoneda.map j ≫ g` is lower
semicontinuous, then on the image of `j` the superlevel sets of the fibre-dimension function of the
base change along `g`, read on the scheme points of `U`, are open. -/
theorem isOpen_range_inter_preimage_fiberDimension_pullback_snd {W U : BigFppfOver B S hS}
    (j : W ⟶ U) (hj : IsOpenMap ((BigFppfOver.toScheme B S hS).map j)) (g : yoneda.obj U ⟶ Y)
    (hft : IsFiniteType B S hS f)
    (hlsc : LowerSemicontinuous (fiberDimension B S hS (pullback.snd f (yoneda.map j ≫ g))))
    (b : WithBot ℕ∞) :
    IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map j) ∩
      (fiberDimension B S hS (pullback.snd f g) ∘ (schemePointsHomeomorph B S hS U).symm) ⁻¹'
        Set.Ioi b) := by
  have himage : Set.range ((BigFppfOver.toScheme B S hS).map j) ∩
      (fiberDimension B S hS (pullback.snd f g) ∘ (schemePointsHomeomorph B S hS U).symm) ⁻¹'
        Set.Ioi b =
      (BigFppfOver.toScheme B S hS).map j ''
        ((fiberDimension B S hS (pullback.snd f (yoneda.map j ≫ g)) ∘
          (schemePointsHomeomorph B S hS W).symm) ⁻¹' Set.Ioi b) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_image, Set.mem_preimage,
      Function.comp_apply]
    constructor
    · rintro ⟨⟨z, rfl⟩, hz⟩
      rw [← fiberDimension_pullback_snd_yoneda_map_comp B S hS hX hY f j g hft z] at hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rw [fiberDimension_pullback_snd_yoneda_map_comp B S hS hX hY f j g hft z] at hz
      exact ⟨⟨z, rfl⟩, hz⟩
  rw [himage, Set.preimage_comp]
  exact hj _ ((lowerSemicontinuous_iff_isOpen_preimage.mp hlsc b).preimage
    (schemePointsHomeomorph B S hS W).symm.continuous)

/-- For a flat morphism of finite presentation and a morphism to its target from an object of the
site, the fibre-dimension function of the base change is lower semicontinuous: lower
semicontinuity is local on the scheme, and holds over each affine open. -/
theorem lowerSemicontinuous_fiberDimension_pullback_snd_yoneda
    (hflat : IsFlat B S hS f) (hfp : IsFinitePresentation B S hS f)
    {U : BigFppfOver B S hS} (g : yoneda.obj U ⟶ Y) :
    LowerSemicontinuous (fiberDimension B S hS (pullback.snd f g)) := by
  classical
  have hft := isFiniteType_of_isFinitePresentation B S hS hfp
  refine lowerSemicontinuous_of_open_surjective _ (schemePointsHomeomorph B S hS U).symm
    (schemePointsHomeomorph B S hS U).symm.isOpenMap
    (schemePointsHomeomorph B S hS U).symm.surjective ?_
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro b
  have hcover : (⋃ O : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      ((O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
        Set ((BigFppfOver.toScheme B S hS).obj U))) = Set.univ := by
    rw [← TopologicalSpace.Opens.coe_iSup, iSup_affineOpens_eq_top,
      TopologicalSpace.Opens.coe_top]
  rw [isOpen_iff_of_cover (fun O : ((BigFppfOver.toScheme B S hS).obj U).affineOpens ↦
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens).2) hcover]
  rintro ⟨O, hO⟩
  have hw := map_openSiteObjectHom B S hS U O
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map
      (openSiteObjectHom B S hS U O)) =
      (O :
        Set ((BigFppfOver.toScheme B S hS).obj U)) := by
    rw [hw]
    exact O.range_ι
  have h := isOpen_range_inter_preimage_fiberDimension_pullback_snd B S hS hX hY f
    (openSiteObjectHom B S hS U O)
    (by rw [hw]; exact O.ι.isOpenMap) g hft
    (lowerSemicontinuous_fiberDimension_pullback_of_isAffine B S hS hX hY f hflat hfp
      (openSiteObject B S hS U O) hO _) b
  rwa [hrange] at h

/-- **Stacks 0D4P.** The fibre-dimension function of a flat morphism of algebraic spaces over `S`
of finite presentation is lower semicontinuous on the points of its target. -/
@[stacks 0D4P]
theorem lowerSemicontinuous_fiberDimension
    (hflat : IsFlat B S hS f) (hfp : IsFinitePresentation B S hS f) :
    LowerSemicontinuous (fiberDimension B S hS f) := by
  classical
  have hft := isFiniteType_of_isFinitePresentation B S hS hfp
  obtain ⟨U, atlas, hatlasSurj, hatlasEtale⟩ := hY.exists_atlas
  have hdimAtlas := fiberDimension_pullback_snd B S hS f atlas hX hY
    (isAlgebraicSpace_yoneda B S hS U) hft
  exact lowerSemicontinuous_of_open_surjective _ (pointsMap B S hS (yoneda.obj U) atlas)
    (isOpenMap_pointsMap_of_etale B S hS hY U atlas hatlasEtale)
    ((surjective_iff_surjective_pointsMap B S hS Y hY U atlas).mp hatlasSurj)
    (hdimAtlas ▸ lowerSemicontinuous_fiberDimension_pullback_snd_yoneda B S hS hX hY f hflat hfp
      atlas)

end

end AlgebraicGeometry.Space

end
