module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleOnFlatLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleTorsionFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.WeaklyAssociatedLocallyFinite

/-!
# A flat module of finite type is of finite presentation

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite presentation, and assume the weakly associated points of `Y` are locally
finite.  Stacks 0DLR says that a quasi-coherent `𝒪_X`-module `F` of finite type is of finite
presentation on the open subspace `U ⊂ X` where it is flat over `Y`.  If `F` is flat over `Y`
then `U` is all of `X`, and so `F` itself is of finite presentation.  The proof of Stacks 0DM0
uses this over a valuation ring `R`: "by Theorem 0DLR any finite type quasi-coherent
`𝒪_X`-module `F` flat over `R` is of finite presentation", the hypothesis on the weakly
associated points being met because `Spec R` is integral and so has a single one.

## Main results

* `AlgebraicGeometry.Space.flatLocus_eq_univ_of_isFlatOver` and
  `AlgebraicGeometry.Space.flatLocus_eq_univ_iff_isFlatOver`: the relative flat locus of a module
  flat over the target is all of the source, and conversely for a quasi-coherent module.
* `AlgebraicGeometry.Space.isIso_flatLocusSpaceι_hom_of_isFlatOver`: for a flat module the open
  immersion of the flat locus into the source is an isomorphism.
* `AlgebraicGeometry.Space.isFinitePresentationOnCharts_of_isFlatOver`: **a quasi-coherent module
  of finite type flat over the target is of finite presentation**, at the conditions of
  Stacks 0DLR.
* `AlgebraicGeometry.Space.isFinitePresentationOnCharts_of_isFlatOver_of_isDomain`: the case of a
  target represented by the spectrum of a domain, in particular of a valuation ring, which is the
  form used in the proof of Stacks 0DM0.
* `AlgebraicGeometry.Space.isFlatOver_and_isFinitePresentationOnCharts_of_isTorsionFreeOver`:
  over a valuation ring, a quasi-coherent module of finite type which is torsion free is flat
  and of finite presentation.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_of_isFlatOver` and
  `AlgebraicGeometry.Space.isFlatOver_and_isFinitePresentationOnSite_of_isTorsionFreeOver`: the
  same conclusions on the small étale site.

## Implementation notes

The finite presentation assertion of Stacks 0DLR is stated about the module `F|_U` on the open
subspace `U` cut out by the flat locus, which is a different algebraic space from `X` even when
`U` is everything.  Rather than transport along the identification of that subspace with `X`,
the proof reads the same assertion on the charts of `X`, where it is
`AlgebraicGeometry.Space.isFinitePresentation_restrict_preimage_flatLocus`: on a commuting square
of étale scheme charts the restriction of `F` to the preimage of `U` in the source chart is of
finite presentation, and that preimage is the whole chart.  Finite presentation on one chart
surjective on points and lying over a chart of `Y` (Tag 02X1) then spreads to every chart by
`AlgebraicGeometry.Space.isFinitePresentation_restrictToChartScheme_of_isSurjective`, which is
the étale locality used in the source's proof of Stacks 0DLR.

The conclusion is finite presentation on the étale scheme charts,
`AlgebraicGeometry.Space.IsFinitePresentationOnCharts`, which is the form in which Stacks 0DLR is
stated here.  Finite presentation on the small étale site,
`SheafOfModules.IsFinitePresentationOnSite`, is equivalent to it for a quasi-coherent module by
`AlgebraicGeometry.Space.isFinitePresentationOnSite_iff_isFinitePresentationOnCharts`, which gives
the site-level forms of the results.

## References

* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Xs Ys : AlgebraicSpaces B S hS}

/-! ### The flat locus of a flat module -/

/-- The relative flat locus of a module flat over the target is the whole point space of the
source: every point lies on a chart of a commuting square of étale scheme charts, on which the
module is flat. -/
theorem flatLocus_eq_univ_of_isFlatOver (f : Xs ⟶ Ys) (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    (h : IsFlatOver B S hS Xs.2 f.hom F) : flatLocus B S hS Xs.2 f.hom F = Set.univ :=
  Set.eq_univ_of_forall fun x => by
    obtain ⟨d, u, hu⟩ := exists_chartDiagram_pointOfEtaleChart B S hS Xs.2 Ys.2 f.hom x
    exact ⟨d, u, hu, h d u⟩

/-- A quasi-coherent module is flat over the target exactly when its relative flat locus is the
whole point space of the source.  The converse direction is the chart independence of
Stacks 05VU. -/
theorem flatLocus_eq_univ_iff_isFlatOver (f : Xs ⟶ Ys) (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    (hF : F.IsQuasicoherentOnSite) :
    flatLocus B S hS Xs.2 f.hom F = Set.univ ↔ IsFlatOver B S hS Xs.2 f.hom F := by
  refine ⟨fun h d u => ?_, flatLocus_eq_univ_of_isFlatOver f F⟩
  have hu : pointOfEtaleChart B S hS d.U u ∈ flatLocus B S hS Xs.2 f.hom F := h ▸ Set.mem_univ _
  exact (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d u).2 hu

/-- **The open subspace cut out by the flat locus of a flat module is the whole source.**  When
the module is flat over the target, its relative flat locus is all of `|X|`, and the open
immersion `U ⟶ X` of Stacks 0DLR is an isomorphism, so that the module `F|_U` of that tag is the
inverse image of `F` along an isomorphism. -/
theorem isIso_flatLocusSpaceι_hom_of_isFlatOver (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    (hopen : IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS Xs.2 f.hom F))
    (h : IsFlatOver B S hS Xs.2 f.hom F) :
    IsIso (flatLocusSpaceι B S hS f F hopen).hom := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  refine ⟨Subtype.val_injective, fun x => ⟨⟨x, fun y _ => ?_⟩, rfl⟩⟩
  exact (flatLocus_eq_univ_of_isFlatOver f F h).symm ▸ Set.mem_univ y

/-! ### Finite presentation of a flat module of finite type -/

/-- An open of a scheme equal to the whole scheme, on which a quasi-coherent module restricts to
a module of finite presentation, forces the module itself to be of finite presentation. -/
private theorem isFinitePresentation_of_restrict_eq_top {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (Z : X.Opens) (h : (M.restrict Z.ι).IsFinitePresentation) (hZ : Z = ⊤) :
    M.IsFinitePresentation := by
  subst hZ
  exact _root_.AlgebraicGeometry.isFinitePresentation_of_restrict_top M h

/-- **A quasi-coherent module of finite type flat over the target is of finite presentation.**
Let `f : X ⟶ Y` be a morphism of algebraic spaces locally of finite presentation, let `F` be a
quasi-coherent `𝒪_X`-module of finite type, and assume the weakly associated points of `Y` are
locally finite on the scheme of one surjective étale chart.  If `F` is flat over `Y`
(Stacks 05VV), then `F` is of finite presentation, read on the étale scheme charts of `X`.

This is Stacks 0DLR at a module whose flat locus is all of `X`: the hypotheses are those of
`AlgebraicGeometry.Space.isFinitePresentationOnCharts_flatLocusRestrict`, and its finite
presentation assertion is read on the charts of `X`, where the preimage of the flat locus is
the whole chart. -/
theorem isFinitePresentationOnCharts_of_isFlatOver (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [hqc : F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) (V₀ : SmallEtale B S hS Ys.1)
    (hV₀ : IsSurjectiveChart B S hS V₀)
    (h₀ : ∀ v : etaleChartScheme B S hS V₀,
      ∃ W : (etaleChartScheme B S hS V₀).Opens, v ∈ W ∧
        (Stacks.Divisors.schemeWeaklyAssociatedPoints (etaleChartScheme B S hS V₀) ∩
          (W : Set (etaleChartScheme B S hS V₀))).Finite)
    (hflat : IsFlatOver B S hS Xs.2 f.hom F) :
    IsFinitePresentationOnCharts B S hS Xs.2 F := by
  have hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Ys.1 :=
    hasLocallyFiniteWeaklyAssociatedPointsOnCharts_of_isSurjectiveChart B S hS V₀ hV₀ h₀
  -- Finite presentation on the source chart of every commuting square of charts.
  have hfp : ∀ d : ChartDiagram B S hS Xs.1 Ys.1 f.hom,
      (chartModule B S hS Xs.2 F d.U).IsFinitePresentation := fun d => by
    have := isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS Xs F hqc d.U
    refine isFinitePresentation_of_restrict_eq_top _ _
      (isFinitePresentation_restrict_preimage_flatLocus B S hS f F hf hft hwa d) ?_
    exact TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun u => ⟨d, u, rfl, hflat d u⟩)
  -- A chart of `X` surjective on points and lying over a chart of `Y`.
  obtain ⟨V, hVsurj⟩ := exists_surjective_smallEtale_chart B S hS Ys.1 Ys.2
  obtain ⟨U₀, p, α, hsq, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS Xs.2 Ys.2 f.hom V.1.left V.1.hom
      ((presheafSurjective_iff_isSurjective_yoneda B S hS Ys.1 Ys.2 V.1.left V.1.hom).2 hVsurj)
      V.property
  set A : SmallEtale B S hS Xs.1 := ⟨CostructuredArrow.mk p, hpEtale⟩ with hA
  have hAsurj : IsSurjective B S hS A.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS Xs.1 Xs.2 U₀ p).1 hpSurj
  have hAfp : (chartModule B S hS Xs.2 F A).IsFinitePresentation := hfp ⟨A, V, α, hsq⟩
  -- Étale locality of finite presentation spreads it to every chart.
  intro A'
  exact SheafOfModules.IsFinitePresentation.of_iso
    (isFinitePresentation_restrictToChartScheme_of_isSurjective B S hS _ Xs.2 F hqc A hAsurj
      (SheafOfModules.IsFinitePresentation.of_iso hAfp
        (restrictToChartIsoRestrictToChartScheme B S hS _ _ A)) A')
    (restrictToChartIsoRestrictToChartScheme B S hS _ _ A').symm

/-! ### Over the spectrum of a domain -/

/-- The identity chart of a represented algebraic space is surjective. -/
theorem isSurjectiveChart_selfChart (W : BigFppfOver B S hS) :
    IsSurjectiveChart B S hS (selfChart B S hS W) :=
  presheaf_id_of_iso B S hS _ (fun {_ _} g hg => by
    have : IsIso ((BigFppfOver.toScheme B S hS).map g) := by
      let _ := hg; infer_instance
    change Surjective ((BigFppfOver.toScheme B S hS).map g)
    infer_instance) W

/-- **A quasi-coherent module of finite type flat over the spectrum of a domain is of finite
presentation.**  Let `R` be a domain — for instance a valuation ring — let `W` be an object of
the big fppf site whose scheme is `Spec R`, and let `f : X ⟶ h_W` be a morphism of algebraic
spaces locally of finite presentation.  A quasi-coherent `𝒪_X`-module of finite type which is
flat over `h_W` (Stacks 05VV) is of finite presentation, read on the étale scheme charts of `X`.

This is the step of the proof of Stacks 0DM0 citing Stacks 0DLR: `Spec R` is integral, so its
weakly associated points, a single generic point, are finite. -/
theorem isFinitePresentationOnCharts_of_isFlatOver_of_isDomain {R : Type u} [CommRing R]
    [IsDomain R] {W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ Spec (CommRingCat.of R))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace W)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) (hflat : IsFlatOver B S hS X.2 f.hom F) :
    IsFinitePresentationOnCharts B S hS X.2 F := by
  have : Nonempty ((BigFppfOver.toScheme B S hS).obj W) :=
    ⟨e.inv.base (Nonempty.some inferInstance)⟩
  have : IsIntegral ((BigFppfOver.toScheme B S hS).obj W) := isIntegral_of_isOpenImmersion e.hom
  refine isFinitePresentationOnCharts_of_isFlatOver f F hf hft (selfChart B S hS W)
    (isSurjectiveChart_selfChart W) (fun _ => ⟨⊤, trivial, ?_⟩) hflat
  exact (_root_.AlgebraicGeometry.schemeWeaklyAssociatedPoints_finite_of_isIntegral
    ((BigFppfOver.toScheme B S hS).obj W)).subset Set.inter_subset_left

/-- **A torsion free module of finite type over a valuation ring is flat and of finite
presentation.**  Let `R` be a valuation ring, let `W` be an object of the big fppf site whose
scheme is `Spec R`, and let `f : X ⟶ h_W` be a morphism of algebraic spaces locally of finite
presentation.  A quasi-coherent `𝒪_X`-module of finite type which is torsion free over `h_W` is
flat over `h_W` (Stacks 05VV) and of finite presentation, read on the étale scheme charts of
`X`.

These are the two properties the proof of Stacks 0DM0 needs of the finite type submodules of
`j_*F_K`: flatness because over a valuation ring torsion free modules are flat (Stacks 0539),
and then finite presentation by Stacks 0DLR. -/
theorem isFlatOver_and_isFinitePresentationOnCharts_of_isTorsionFreeOver {R : Type u}
    [CommRing R] [IsDomain R] [ValuationRing R] {W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ Spec (CommRingCat.of R))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace W)
    (F : Modules.{u, u} B S hS X.1 X.2) [hqc : F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) (htf : IsTorsionFreeOver B S hS X.2 f.hom F) :
    IsFlatOver B S hS X.2 f.hom F ∧ IsFinitePresentationOnCharts B S hS X.2 F := by
  have hflat : IsFlatOver B S hS X.2 f.hom F :=
    (isFlatOver_iff_isTorsionFreeOver_of_valuationRing e f F hqc).2 htf
  exact ⟨hflat, isFinitePresentationOnCharts_of_isFlatOver_of_isDomain e f F hf hft hflat⟩

/-- **A quasi-coherent module of finite type flat over the target is of finite presentation on
the small étale site.** -/
theorem isFinitePresentationOnSite_of_isFlatOver (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [hqc : F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) (V₀ : SmallEtale B S hS Ys.1)
    (hV₀ : IsSurjectiveChart B S hS V₀)
    (h₀ : ∀ v : etaleChartScheme B S hS V₀,
      ∃ W : (etaleChartScheme B S hS V₀).Opens, v ∈ W ∧
        (Stacks.Divisors.schemeWeaklyAssociatedPoints (etaleChartScheme B S hS V₀) ∩
          (W : Set (etaleChartScheme B S hS V₀))).Finite)
    (hflat : IsFlatOver B S hS Xs.2 f.hom F) :
    SheafOfModules.IsFinitePresentationOnSite F :=
  isFinitePresentationOnSite_of_isFinitePresentationOnCharts Xs F hqc
    (isFinitePresentationOnCharts_of_isFlatOver f F hf hft V₀ hV₀ h₀ hflat)

/-- **A torsion free module of finite type over a valuation ring is flat and of finite
presentation on the small étale site.**  Let `R` be a valuation ring, let `W` be an object of the
big fppf site whose scheme is `Spec R`, and let `f : X ⟶ h_W` be a morphism of algebraic spaces
locally of finite presentation.  A quasi-coherent `𝒪_X`-module of finite type which is torsion
free over `h_W` is flat over `h_W` (Stacks 05VV) and of finite presentation on the small étale
site (Stacks 03DL).

These are the conditions on the module of an object of `Coh_{X/Y}` that the proof of
Stacks 0DM0 verifies for the finite type submodules of `j_*F_K`, in the form
`AlgebraicGeometry.Space.CoherentSituation.ExtendsOverValuationRings` asks for them. -/
theorem isFlatOver_and_isFinitePresentationOnSite_of_isTorsionFreeOver {R : Type u}
    [CommRing R] [IsDomain R] [ValuationRing R] {W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ Spec (CommRingCat.of R))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace W)
    (F : Modules.{u, u} B S hS X.1 X.2) [hqc : F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) (htf : IsTorsionFreeOver B S hS X.2 f.hom F) :
    IsFlatOver B S hS X.2 f.hom F ∧ SheafOfModules.IsFinitePresentationOnSite F := by
  obtain ⟨hflat, hfp⟩ :=
    isFlatOver_and_isFinitePresentationOnCharts_of_isTorsionFreeOver e f F hf hft htf
  exact ⟨hflat, isFinitePresentationOnSite_of_isFinitePresentationOnCharts X F hqc hfp⟩

end AlgebraicGeometry.Space

end
