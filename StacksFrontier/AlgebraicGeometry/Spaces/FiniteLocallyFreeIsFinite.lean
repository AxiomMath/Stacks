module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardCartesianCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal

/-!
# A finite locally free morphism of algebraic spaces is finite

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is finite locally free
in the sense of Stacks 03ZV: affine, with direct image `f_*𝒪_X` a finite locally free
`𝒪_Y`-module on the small étale site of `Y`. Then `f` is a finite morphism of algebraic spaces in
the sense of Stacks 03ZP.

## Main results

* `AlgebraicGeometry.Space.isFinite_chartSchemeBaseChangeProjection_of_isAffine`: the base change
  of a finite locally free morphism over an affine étale chart is a finite morphism of schemes.
* `AlgebraicGeometry.Space.isFinite_chartSchemeBaseChangeProjection`: the same over an arbitrary
  étale chart.
* `AlgebraicGeometry.Space.presheaf_isFinite_of_isFiniteLocallyFree`: every represented base
  change of a finite locally free morphism is a finite morphism of schemes.
* `AlgebraicGeometry.Space.isFinite_of_isFiniteLocallyFree`: a finite locally free morphism of
  algebraic spaces is finite.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_presheaf_isFiniteLocallyFreeOfRank`: a
  representable morphism all of whose represented base changes are finite locally free of rank `r`
  is finite locally free of rank `r` in the sense of Stacks 03ZV.

## References

* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The base change over an affine chart -/

/-- Finiteness of morphisms of schemes is invariant under isomorphism of arrows. -/
private theorem isFinite_iff_of_arrow_iso {A B A' B' : Scheme.{u}} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    _root_.AlgebraicGeometry.IsFinite f ↔ _root_.AlgebraicGeometry.IsFinite g :=
  have _hri := Stacks.Morphisms.isFinite_respectsIso.{u}
  MorphismProperty.arrow_mk_iso_iff
    (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) e

/-- The sections of `f_*𝒪_X` over an affine étale chart of `Y` form a finite module for a finite
locally free `f : X ⟶ Y`. -/
theorem moduleFinite_sections_pushforwardStructureModule (f : X ⟶ Y)
    (hflf : IsFiniteLocallyFree B S hS f) (V : SmallEtale B S hS Y.1)
    (hV : IsAffine (chartScheme V)) :
    Module.Finite (chartRing B S hS Y.1 Y.2 V)
      ((pushforwardStructureModule B S hS f).val.obj (op V)) :=
  moduleFinite_sections_of_isFiniteType B S hS Y.1 Y.2
    (isCartesianOnAffineCharts_pushforwardStructureModule B S hS f hflf.1)
    (isFiniteType_of_isFiniteLocallyFreeOnSite _ hflf.2) hV

/-- The global functions on the base change of a finite locally free morphism over an affine étale
chart form a finite module over the functions on the chart. -/
theorem finite_appTop_chartSchemeBaseChangeProjection (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (hflf : IsFiniteLocallyFree B S hS f)
    (V : SmallEtale B S hS Y.1) (hV : IsAffine (chartScheme V)) :
    RingHom.Finite (chartSchemeBaseChangeProjection B S hS f hf V).appTop.hom := by
  have := moduleFinite_sections_pushforwardStructureModule B S hS f hflf V hV
  have hfin : Module.Finite (chartRing B S hS Y.1 Y.2 V)
      ((chartBaseChangeStructureModule B S hS f hf).val.obj (op V)) :=
    Module.Finite.equiv (pushforwardStructureModuleChartLinearEquiv B S hS f hf V)
  let := ((chartSchemeBaseChangeProjection B S hS f hf V).appTop).hom.toAlgebra
  exact hfin

/-- The base change of a finite locally free morphism of algebraic spaces over an affine étale
chart is a finite morphism of schemes. -/
theorem isFinite_chartSchemeBaseChangeProjection_of_isAffine (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (hflf : IsFiniteLocallyFree B S hS f)
    (V : SmallEtale B S hS Y.1) (hV : IsAffine (chartScheme V)) :
    _root_.AlgebraicGeometry.IsFinite (chartSchemeBaseChangeProjection B S hS f hf V) := by
  have : IsAffine (chartScheme ((smallBaseChange B S hS f hf).obj V)) :=
    isAffine_smallBaseChange_obj B S hS f hf hflf.1 V hV
  refine (isFinite_iff_of_arrow_iso
    (arrowIsoSpecΓOfIsAffine (chartSchemeBaseChangeProjection B S hS f hf V))).2 ?_
  exact (_root_.AlgebraicGeometry.IsFinite.SpecMap_iff _).2
    (finite_appTop_chartSchemeBaseChangeProjection B S hS f hf hflf V hV)

/-! ### The base change over an arbitrary chart -/

/-- The base change of a finite locally free morphism of algebraic spaces over an arbitrary étale
chart is a finite morphism of schemes. -/
theorem isFinite_chartSchemeBaseChangeProjection (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (hflf : IsFiniteLocallyFree B S hS f)
    (V : SmallEtale B S hS Y.1) :
    _root_.AlgebraicGeometry.IsFinite (chartSchemeBaseChangeProjection B S hS f hf V) := by
  have _hzar := isZariskiLocalAtTarget_isFinite.{u}
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun O : (chartScheme V).affineOpens => (O : (chartScheme V).Opens))
    (iSup_affineOpens_eq_top (chartScheme V)) fun O => ?_
  have hOaff : IsAffine (chartScheme (openChart B S hS Y.1 V (O : (chartScheme V).Opens))) :=
    inferInstanceAs (IsAffine ((O : (chartScheme V).Opens) : Scheme.{u}))
  have heq : (BigFppfOver.toScheme B S hS).map
      (openChartInclusion B S hS Y.1 V (O : (chartScheme V).Opens)).hom.left =
      (O : (chartScheme V).Opens).ι :=
    toScheme_map_toOver_map_openChartInclusion B S hS Y.1 V (O : (chartScheme V).Opens)
  have hsmall : IsPullback
      ((BigFppfOver.toScheme B S hS).map
        ((smallBaseChange B S hS f hf).map
          (openChartInclusion B S hS Y.1 V (O : (chartScheme V).Opens))).hom.left)
      (chartSchemeBaseChangeProjection B S hS f hf
        (openChart B S hS Y.1 V (O : (chartScheme V).Opens)))
      (chartSchemeBaseChangeProjection B S hS f hf V)
      (O : (chartScheme V).Opens).ι :=
    heq ▸ isPullback_smallBaseChange_map B S hS f hf
      (openChartInclusion B S hS Y.1 V (O : (chartScheme V).Opens))
  have hrestr := (isPullback_morphismRestrict
    (chartSchemeBaseChangeProjection B S hS f hf V) (O : (chartScheme V).Opens)).flip
  refine (isFinite_iff_of_arrow_iso
    (Arrow.isoMk (hsmall.isoIsPullback _ _ hrestr) (Iso.refl _) ?_)).1
    (isFinite_chartSchemeBaseChangeProjection_of_isAffine B S hS f hf hflf _ hOaff)
  exact (IsPullback.isoIsPullback_hom_snd _ _ hsmall hrestr).trans (Category.comp_id _).symm

/-! ### Finiteness of the morphism -/

/-- Every represented base change of a finite locally free morphism of algebraic spaces is a finite
morphism of schemes. -/
theorem presheaf_isFinite_of_isFiniteLocallyFree (f : X ⟶ Y)
    (hflf : IsFiniteLocallyFree B S hS f) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom := by
  have hf := relativelyRepresentable_of_isAffineHom B S hS f hflf.1
  have _hri := Stacks.Morphisms.isFinite_respectsIso.{u}
  have _hfppf := isFinite_descendsAlong_fppf.{u}
  obtain ⟨V, hVsurj⟩ := exists_isSurjective_chart B S hS Y
  exact (presheaf_iff_of_etaleChart_surjectiveOnPoints B S hS
      isZariskiLocalAtTarget_isFinite.{u}
      (fun p hp hZ => isAffine_of_isFinite p hp hZ)
      (isEffectiveDescentAlongSurjectiveEtale_isFinite B S hS) X.2 Y.2 hf V.2 hVsurj).2
    (isFinite_chartSchemeBaseChangeProjection B S hS f hf hflf V)

/-- A finite locally free morphism of algebraic spaces is finite. -/
theorem isFinite_of_isFiniteLocallyFree (f : X ⟶ Y) (hflf : IsFiniteLocallyFree B S hS f) :
    IsFinite B S hS f.hom :=
  isFinite_of_presheaf_isFinite f.hom (presheaf_isFinite_of_isFiniteLocallyFree B S hS f hflf)

/-! ### The rank clause of Stacks 03ZV from condition (1) of Stacks 03ZW -/

/-- A representable morphism of algebraic spaces all of whose represented base changes are finite
locally free of rank `r` is finite locally free of rank `r` in the sense of Stacks 03ZV. -/
theorem isFiniteLocallyFreeOfRank_of_presheaf_isFiniteLocallyFreeOfRank (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (r : ℕ)
    (h : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf f.hom) :
    IsFiniteLocallyFreeOfRank B S hS f r :=
  isFiniteLocallyFreeOfRank_of_presheaf_of_isCartesianOnAffineCharts B S hS f hf r
    (isCartesianOnAffineCharts_pushforwardStructureModule B S hS f
      (isAffineHom_of_presheaf_isFiniteLocallyFreeOfRank B S hS r h)) h

end AlgebraicGeometry.Space

end
