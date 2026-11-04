module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesPrestableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeCharts
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProperFlatFibreGenus

/-!
# The genus loci of a prestable family of curves are open

Let `f : X ⟶ S` be a prestable family of curves. The genus loci of `f`, the sets of points of `S`
at which the fibre has genus `g`, are open in `S`. This is the input
`AlgebraicGeometry.C1590Private.PrestableGenusLociOpen` of the decomposition of
`Curves^{prestable}` by genus (Stacks 0E6V).

The source reads it on `R¹f_*𝒪_X`, which is finite locally free with formation commuting with base
change (Stacks 0E1J). Here the genus is read on the Euler characteristic instead. Étale locally on
`S` the family is a scheme (Stacks 0E6F, the hypothesis `h0E6F`), so it suffices to treat a proper
flat morphism of schemes `q : Z ⟶ U` of finite presentation whose fibres are proper curves with
`H⁰ = κ`. There the derived-fibre Euler characteristic of `Rq_*𝒪_Z` is locally constant (Stacks
0BDJ) and equals `1 - g` at a point whose fibre has genus `g`
(`AlgebraicGeometry.C1590Private.chiDerivedFibre_eq_one_sub_genus`), so the genus loci of the
chart are its level sets; their images under the étale, hence open, chart morphism are open
neighbourhoods inside the genus loci of `S`, since the genus loci commute with base change.

## Main results

* `AlgebraicGeometry.C1590Private.chiDerivedFibre_eq_one_sub_genus_of_presentation`: on a scheme
  chart, the Euler characteristic at a field-valued point is `1 - g` for every scheme presenting
  the fibre.
* `AlgebraicGeometry.C1590Private.isOpen_genusLocus_of_isPrestableCurveFamily`: the genus loci of
  a prestable family are open.
* `AlgebraicGeometry.C1590Private.prestableGenusLociOpen_of`: the input `PrestableGenusLociOpen`,
  from Stacks 0E6F.

## References

* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

open ProperFlatFibreEulerCharacteristic

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **A presentation of a fibre of a morphism of schemes of the site is a cartesian square of
schemes.** If `V` presents the fibre of `yoneda.map q` at a field-valued point `P` of `U`, then
`V` is the base change of `q` along the morphism of schemes `Spec κ(P) ⟶ U` of `P`. -/
theorem exists_isPullback_toScheme_of_presentation {U Z : BigFppfOver B integerBase hZ}
    (q : Z ⟶ U) (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace U).obj)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ P.siteObject)
    (r : yoneda.obj V ⟶ (schemeSpace Z).obj)
    (hV : IsPullback r (yoneda.map v) (schemeSpaceMap q).hom (yonedaEquiv.symm P.value)) :
    ∃ r₀ : V ⟶ Z, IsPullback ((BigFppfOver.toScheme B integerBase hZ).map r₀)
      ((BigFppfOver.toScheme B integerBase hZ).map v)
      ((BigFppfOver.toScheme B integerBase hZ).map q)
      ((BigFppfOver.toScheme B integerBase hZ).map (show P.siteObject ⟶ U from P.value)) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B integerBase hZ) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  rw [yonedaEquiv_symm_value P] at hV
  have hr₀ : yoneda.map (Yoneda.fullyFaithful.preimage r) = r := Yoneda.fullyFaithful.map_preimage r
  refine ⟨Yoneda.fullyFaithful.preimage r, ?_⟩
  refine (IsPullback.of_map_of_faithful yoneda ?_).map (BigFppfOver.toScheme B integerBase hZ)
  rw [hr₀]
  exact hV

/-- A morphism to the spectrum of a field with `K = H⁰` is bijective on global functions. -/
theorem bijective_appTop_of_isIso {K : Type u} [Field K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) (h : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop)) :
    Function.Bijective g.appTop := by
  have : IsIso g.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of K)).inv g.appTop
  exact ConcreteCategory.bijective_of_isIso _

section Chart

variable (X : CurveFamily B hZ) {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ X.base}
  {p : schemeSpace Z ⟶ X.total} {q : Z ⟶ U}
  (sq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))

include sq

/-- A base change of a family of curves represented by a morphism of schemes is of finite
presentation. -/
theorem finitePresentation_toScheme_map_of_isPullback :
    FinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map q) :=
  have := CurveFamily.isProper_toScheme_map_of_isPullback_schemeSpaceMap X sq
  have := CurveFamily.locallyOfFinitePresentation_toScheme_map_of_isPullback X sq
  FinitePresentation.mk inferInstance inferInstance inferInstance

/-- **The genus loci of a prestable family over a scheme chart are open.** Over a chart on which
the prestable family `X` is a morphism of schemes `q : Z ⟶ U`, the genus-`g` locus of the base
change is the level set at `1 - g` of the derived-fibre Euler characteristic of `Rq_*𝒪_Z`, which
is locally constant. -/
theorem isOpen_genusLocus_curveFamilyOfIsPullback (hX : IsPrestableCurveFamily B hZ X) (g : ℕ) :
    IsOpen ((curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq).genusLocus g) := by
  set T := BigFppfOver.toScheme B integerBase hZ
  have := CurveFamily.isProper_toScheme_map_of_isPullback_schemeSpaceMap X sq
  have := CurveFamily.flat_toScheme_map_of_isPullback X sq
  have hfp := finitePresentation_toScheme_map_of_isPullback X sq
  set XU := curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq
  have hXU : IsPrestableCurveFamily B hZ XU :=
    CurveFamily.isPrestableCurveFamily_of_hom
      (curveFamilyOfIsPullbackHom X φ p (schemeSpaceMap q) sq) hX
  set χ := DerivedFibreBetti.chiDerivedFibre (T.obj U)
    (derivedPushforwardModule (T.map q) (SheafOfModules.unit (T.obj Z).ringCatSheaf))
    (isPseudoCoherent_derivedPushforwardModule_unit _ hfp)
  have key : XU.genusLocus g = χ ⁻¹' {1 - (g : ℤ)} := by
    ext u'
    set P := XU.residueFieldPoint u'
    obtain ⟨V, v, r, hV⟩ := exists_isPullback_yoneda_fieldValuedPoint B hZ XU P
    obtain ⟨-, hdim, hiso, -⟩ := fibre_properties_of_isPrestableCurveFamily hXU P v r hV
    obtain ⟨r₀, hsq⟩ := exists_isPullback_toScheme_of_presentation q P v r hV
    have hχ := chiDerivedFibre_eq_one_sub_genus (T.map q) hfp _ _ (T.map r₀) (T.map v) hsq
      (IsLocalRing.closedPoint P.carrier) hdim.le (bijective_appTop_of_isIso _ hiso)
    have hpt : (T.map (show P.siteObject ⟶ U from P.value)).base
        (IsLocalRing.closedPoint P.carrier) = u' := CurveFamily.schemePoint_residueFieldPoint XU u'
    rw [hpt] at hχ
    show XU.HasGenusAt P g ↔ χ u' = 1 - (g : ℤ)
    rw [show χ u' = _ from hχ]
    exact ⟨fun h => by rw [h.genus_eq v r hV],
      fun h => ⟨V, v, r, hV, by exact_mod_cast sub_right_injective h⟩⟩
  rw [key]
  exact (isLocallyConstant_chiDerivedFibre_unit _ hfp).isOpen_fiber _

end Chart

/-- **The genus loci of a prestable family of curves are open**, given the étale local scheme
charts of Stacks 0E6F. Every point `s` of the base lies in the image of an étale chart over which
the family is a morphism of schemes; there the genus loci are open, and the image of the genus-`g`
locus of the chart is an open neighbourhood of `s` inside the genus-`g` locus of the base. -/
theorem isOpen_genusLocus_of_isPrestableCurveFamily (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (X : CurveFamily B hZ) (hX : IsPrestableCurveFamily B hZ X) (g : ℕ) :
    IsOpen (X.genusLocus g) := by
  set T := BigFppfOver.toScheme B integerBase hZ
  rw [isOpen_iff_forall_mem_open]
  intro s hs
  obtain ⟨U, Z, φ, q, p, hφ, ⟨u, hu⟩, sq⟩ := h0E6F X s
  have : Etale (T.map φ) := hφ
  have hpre : (curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq).genusLocus g =
      T.map φ ⁻¹' X.genusLocus g :=
    genusLocus_eq_preimage (curveFamilyOfIsPullbackHom X φ p (schemeSpaceMap q) sq) g
  refine ⟨T.map φ '' (curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq).genusLocus g, ?_, ?_, ?_⟩
  · rw [hpre]
    exact Set.image_preimage_subset _ _
  · exact (T.map φ).isOpenMap _ (isOpen_genusLocus_curveFamilyOfIsPullback X sq hX g)
  · refine ⟨u, ?_, hu⟩
    rw [hpre, Set.mem_preimage, hu]
    exact hs

/-- **The input `PrestableGenusLociOpen`**, from the étale local scheme charts of Stacks 0E6F. -/
theorem prestableGenusLociOpen_of (h0E6F : HasEtaleLocalSchemeCharts B hZ) :
    PrestableGenusLociOpen B hZ :=
  fun X hX g => isOpen_genusLocus_of_isPrestableCurveFamily h0E6F X hX g

end AlgebraicGeometry.C1590Private

end
