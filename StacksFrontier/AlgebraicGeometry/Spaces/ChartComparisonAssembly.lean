module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeViaEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeChartFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsEtale
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorFree

/-!
# The chart comparison of Stacks 03ZU, and what it unblocks

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S`, let `V` be an
étale scheme chart of `Y`, let `U = V ×_Y X` be the base-changed chart of `X` and let
`ψ : U ⟶ V` be the cartesian projection.  This file identifies the restriction `(f_*𝒪_X)|_V` of
the direct image of the structure sheaf to the slice at `V`, read on the small étale site of the
chart scheme of `V`, with the direct image of `𝒪_U` along the morphism of ringed sites of the
morphism of schemes underlying `ψ`.

That identification is the comparison Stacks 03ZU performs implicitly, as the abuse of notation
of its Equation 03LW.  With it the module conjunct of Stacks 03ZV at the chart `V` becomes the
module conjunct of Stacks 02KA for `ψ`, so finite local freeness of `f_*𝒪_X` on the slice at `V`
gives that `ψ` is a finite locally free morphism of schemes.  Hence a morphism finite locally
free in the sense of Stacks 03ZV has every represented base change finite locally free, which is
the "only if" direction of Stacks 03ZU, and in particular finite.

That scheme-level finiteness is what the section-space results of Stacks 05XQ ask for, so the
second half of the file discharges the clause
`AlgebraicGeometry.Space.IsFibreSectionsSurjective` and states the surjectivity conclusions of
Stacks 05YD and Stacks 05Y5 at the hypotheses of the source.

## Main results

* `AlgebraicGeometry.Space.chartSchemePushforwardStructureModuleIso`: **the identification**, at
  the structure sheaf.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_baseChangeChartHom_of_isFiniteLocallyFreeOnSite`:
  **the chart comparison of Stacks 03ZU**, for an affine `f`.
* `AlgebraicGeometry.Space.presheaf_of_isFiniteLocallyFree`: **Stacks 03ZU, the "only if"
  direction**, and
  `AlgebraicGeometry.Space.isFinite_of_isPullback_of_isFiniteLocallyFree`: a represented base
  change of such a morphism is a finite morphism of schemes.
* `AlgebraicGeometry.Space.isFibreSectionsSurjective`: **Stacks 05XQ for the fibre data of
  Stacks 05YD**, which that tag's statements carried as a hypothesis.
* `AlgebraicGeometry.Space.isSurjective_restrictionOfScalarsMap_of_isFiniteLocallyFree` and
  `AlgebraicGeometry.Space.isSurjective_relativeHomPostcompose_of_isFiniteLocallyFree`:
  **the surjectivity conclusions of Stacks 05YD and Stacks 05Y5**, with nothing carried.

## Implementation notes

The chain is the same one `AlgebraicGeometry.Space.isFinitePresentation_over_baseChangeChart_iff`
runs for finite presentation, with the module fixed to be the structure sheaf:

* the restriction of `f_*𝒪_X` to `V` is the direct image, along the chart-localized base change,
  of the restriction of `𝒪_X` to `U`.  This is Stacks 04CF,
  `AlgebraicGeometry.Space.over_smallBaseChangeModulePushforward_obj`, applied after the
  identification `AlgebraicGeometry.Space.modulePushforwardChartIso` of the direct image of
  Stacks 03LU with the concrete base-change direct image;
* the restriction of `𝒪_X` to the slice at `U` is the structure sheaf of the slice, by
  `SheafOfModules.overFunctorUnitIso`;
* both readings on the small étale sites of the chart *schemes* are identified by
  `AlgebraicGeometry.Space.chartSchemeSiteModulePushforwardIso`, the chart base-change square of
  ringed sites carried to sheaves of modules, whose structure map
  `AlgebraicGeometry.Space.chartSchemeBaseChangeSharp` *is*
  `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing` at the morphism of schemes underlying
  `ψ`;
* and the structure sheaf of the slice at `U`, read on the small étale site of the chart scheme of
  `U`, is the structure sheaf of that site.

No comparison of the structure sheaves intervenes at the two chart-scheme readings: the slice of
the small étale site of an algebraic space at a chart and the small étale site of the scheme of
that chart have equal structure sheaves, so the reading of a module is the reindexing along the
identification of Stacks 04M0 with the identity as its comparison of coefficients.  That is why
the chart-scheme readings of both sides are `AlgebraicGeometry.Space.chartSchemeSiteModule`, and
why finite local freeness crosses them by
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff` with nothing to transport.

The isomorphisms at the two unit modules are `CategoryTheory.Iso.refl`: the direct image of
modules along a reindexing with identity comparison of coefficients carries the structure sheaf
to the structure sheaf on the nose, exactly as `SheafOfModules.overFunctorUnitIso` and
`SheafOfModules.overMapUnitIso` do.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
* [Stacks Project, Tag 05Y5](https://stacks.math.columbia.edu/tag/05Y5)
* [Stacks Project, Tag 05YD](https://stacks.math.columbia.edu/tag/05YD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finite local freeness across the chart-scheme identification -/

/-- **Finite local freeness transports across the chart-scheme identification.**  A module on
the slice at an étale chart is finite locally free on the site if and only if the module it
becomes on the small étale site of the scheme underlying that chart is.

This is `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff`, the clause 03DL (2) of
Modules on Sites, Lemma 03DM, applied to
`AlgebraicGeometry.Space.chartSchemeIdentification`; it is the companion of
`AlgebraicGeometry.Space.isFinitePresentation_chartSchemeModule_iff`. -/
@[stacks 03DM "finite locally free, at the chart-scheme identification"]
theorem isFiniteLocallyFreeOnSite_chartSchemeModule_iff (U : AlgebraicSpaces B S hS)
    (W : (smallEtaleRingedSite B S hS U.1 U.2).C)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((smallEtaleRingedSite B S hS U.1 U.2).over W).O)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (chartSchemeSiteModule B S hS U W M) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite M := by
  have := isContinuous_chartSchemeIdentification_functor B S hS U W
  have := isContinuous_chartSchemeIdentification_inverse B S hS U W
  have := isDenseSubsite_chartSchemeIdentification_inverse B S hS U W
  exact Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff
    (chartSchemeIdentification B S hS U W) _ M

/-- **The chart-scheme reading of the structure sheaf of a slice is the structure sheaf of the
small étale site of the chart scheme.**  The identification of Stacks 04M0 has the identity as
its comparison of coefficients, so reindexing along it carries the structure sheaf of the slice
to the structure sheaf of the chart scheme on the nose. -/
noncomputable def chartSchemeSiteModuleUnitIso (U : AlgebraicSpaces B S hS)
    (W : (smallEtaleRingedSite B S hS U.1 U.2).C) :
    chartSchemeSiteModule B S hS U W
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS U.1 U.2).over W).O)) ≅
      SheafOfModules.unit (chartSchemeSiteStructureSheaf B S hS U W) :=
  Iso.refl _

/-! ### Affineness of the chart base change -/

section ChartComparison

variable {X Y : AlgebraicSpaces B S hS}

/-- **The chart base change of an affine morphism is an affine morphism of schemes.**  For `f`
affine in the sense of Stacks 03WF and `V` an étale scheme chart of `Y`, the projection
`ψ : V ×_Y X ⟶ V` carries `AlgebraicGeometry.IsAffineHom` on the underlying morphism of schemes.

Affineness of `ψ` as a morphism of algebraic spaces is stability of Stacks 03WF under base
change along the cartesian square, Stacks 03WI; the passage to the underlying morphism of
schemes is Stacks 03WG, (2) implies (1). -/
theorem isAffineHom_baseChangeChartHom (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (baseChangeChartHom B S hS f hrep V)) :=
  (presheaf_yoneda_map_iff B S hS
      (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance
      (baseChangeChartHom B S hS f hrep V)).1
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
      (IsAffineHom.of_isPullback (isPullback_baseChangeChartHom B S hS f hrep V) haff)).2

/-! ### The identification at the structure sheaf -/

/-- **The chart-scheme reading of `(f_*𝒪_X)|_V` is the small étale direct image of `𝒪_U` along
`ψ`.**  For a representable morphism `f : X ⟶ Y` of algebraic spaces over `S` and an étale
scheme chart `V` of `Y`, the restriction of `f_*𝒪_X` to the slice at `V`, read on the small
étale site of the chart scheme of `V`, is the direct image of the structure sheaf of the small
étale site of the chart scheme of `U = V ×_Y X` along the morphism of ringed sites of the
morphism of schemes underlying the cartesian projection `ψ : U ⟶ V`.

This is the comparison Stacks 03ZU leaves implicit; see the implementation notes for the
chain. -/
noncomputable def chartSchemePushforwardStructureModuleIso (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) :
    chartSchemeSiteModule B S hS Y V ((pushforwardStructureModule B S hS f).over V) ≅
      (SheafOfModules.pushforward.{u}
        (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
          (baseChangeChartHom B S hS f hrep V).left)).obj
        (SheafOfModules.unit (chartSchemeSiteStructureSheaf B S hS X
          (baseChangeChart B S hS f hrep V))) :=
  (SheafOfModules.pushforward.{u}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).O)
      (F := (chartSchemeIdentification B S hS Y V).functor) (𝟙 _)).mapIso
      ((SheafOfModules.overFunctor (smallEtaleRingSheaf B S hS Y.1 Y.2) V).mapIso
          ((modulePushforwardChartIso B S hS f hrep).app _) ≪≫
        eqToIso (over_smallBaseChangeModulePushforward_obj B S hS f hrep V _)) ≪≫
    chartSchemeSiteModulePushforwardIso B S hS f hrep V _ ≪≫
    (SheafOfModules.pushforward.{u}
      (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
        (baseChangeChartHom B S hS f hrep V).left)).mapIso
      (chartSchemeSiteModuleUnitIso B S hS X (baseChangeChart B S hS f hrep V))

/-! ### The chart comparison of Stacks 03ZU -/

/-- **The chart comparison of Stacks 03ZU.**  For an affine representable morphism `f : X ⟶ Y`
of algebraic spaces over `S` and an étale scheme chart `V` of `Y`, finite local freeness of the
restriction of `f_*𝒪_X` to the slice at `V` gives that the base change `ψ : V ×_Y X ⟶ V` of `f`
over `V` is a finite locally free morphism of schemes in the sense of Stacks 02KA.

The module is carried to the direct image of `𝒪_U` along `ψ` by
`AlgebraicGeometry.Space.chartSchemePushforwardStructureModuleIso`, where
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_pushforward`
applies; its affineness hypothesis is
`AlgebraicGeometry.Space.isAffineHom_baseChangeChartHom`. -/
theorem isFiniteLocallyFree_baseChangeChartHom_of_isFiniteLocallyFreeOnSite (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V)
      ((pushforwardStructureModule B S hS f).over V)) :
    Stacks.Morphisms.IsFiniteLocallyFree
      ((BigFppfOver.toScheme B S hS).map (baseChangeChartHom B S hS f hrep V)) := by
  have : _root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (baseChangeChartHom B S hS f hrep V).left) :=
    isAffineHom_baseChangeChartHom B S hS f hrep haff V
  exact AlgebraicGeometry.SmallEtale.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_pushforward
    (associatedBigEtaleSite B) (baseChangeChartHom B S hS f hrep V).left
    (SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      (chartSchemePushforwardStructureModuleIso B S hS f hrep V)
      ((isFiniteLocallyFreeOnSite_chartSchemeModule_iff B S hS Y V _).2 h))

/-! ### Stacks 03ZU, the "only if" direction, unconditionally -/

/-- **Stacks 03ZU, the "only if" direction.**  A representable morphism `f : X ⟶ Y` of algebraic
spaces over `S` which is finite locally free in the sense of Stacks 03ZV — affine with `f_*𝒪_X`
a finite locally free `𝒪_Y`-module — is finite locally free in the sense of Section 03HA: every
represented base change of `f` is a finite locally free morphism of schemes.

This is `AlgebraicGeometry.Space.presheaf_of_isFiniteLocallyFree_of_chartComparison_at` with its
hypothesis `hcross` discharged by
`AlgebraicGeometry.Space.isFiniteLocallyFree_baseChangeChartHom_of_isFiniteLocallyFreeOnSite`,
at an étale chart whose structure morphism is surjective on points; one exists by
`AlgebraicGeometry.Space.exists_surjective_smallEtale_chart`.  The affineness that the chart
comparison consumes is the first conjunct of Stacks 03ZV, so nothing is assumed beyond it. -/
@[stacks 03ZU "the only if direction: finite locally free in the sense of 03ZV implies every \
represented base change is a finite locally free morphism of schemes"]
theorem presheaf_of_isFiniteLocallyFree (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (h : IsFiniteLocallyFree B S hS f) :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom := by
  obtain ⟨V, hV⟩ := exists_surjective_smallEtale_chart B S hS Y.1 Y.2
  exact presheaf_of_isFiniteLocallyFree_of_chartComparison_at B S hS f hrep V hV
    (isFiniteLocallyFree_baseChangeChartHom_of_isFiniteLocallyFreeOnSite B S hS f hrep h.1 V) h

/-- **A represented base change of a morphism finite locally free in the sense of Stacks 03ZV is
a finite locally free morphism of schemes.**  This is
`AlgebraicGeometry.Space.presheaf_of_isFiniteLocallyFree` read at one Cartesian square. -/
theorem isFiniteLocallyFree_of_isPullback_of_isFiniteLocallyFree (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (h : IsFiniteLocallyFree B S hS f)
    {a b : BigFppfOver B S hS} (g : yoneda.obj a ⟶ Y.1) (fst : yoneda.obj b ⟶ X.1)
    (snd : b ⟶ a) (sq : IsPullback fst (yoneda.map snd) f.hom g) :
    Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map snd) :=
  (presheaf_of_isFiniteLocallyFree B S hS f hrep h).property g fst snd sq

/-- **A represented base change of a morphism finite locally free in the sense of Stacks 03ZV is
a finite morphism of schemes**, a finite locally free morphism of schemes being finite. -/
theorem isFinite_of_isPullback_of_isFiniteLocallyFree (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (h : IsFiniteLocallyFree B S hS f)
    {a b : BigFppfOver B S hS} (g : yoneda.obj a ⟶ Y.1) (fst : yoneda.obj b ⟶ X.1)
    (snd : b ⟶ a) (sq : IsPullback fst (yoneda.map snd) f.hom g) :
    _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map snd) :=
  have := isFiniteLocallyFree_of_isPullback_of_isFiniteLocallyFree B S hS f hrep h g fst snd sq
  Stacks.Morphisms.IsFiniteLocallyFree.isFinite _

end ChartComparison

/-! ### Stacks 05XQ at a base change of a finite locally free morphism -/

section SectionSpaces

/-- **Stacks 05XQ for the fibre data of Stacks 05YD.**  Let `z : Z ⟶ Q` be a finite locally free
morphism of algebraic spaces over `S`, let `U` be an object of the big fppf category over `S`,
let `Z_U` be an algebraic space exhibited as a base change `U ×_{a, Q} Z` of `z`, and let
`w : W ⟶ Z_U` be surjective and étale.  Then the restriction of scalars `Res_{Z_U/U}(W) ⟶ U` is
surjective.

Stacks 05XQ is formalized at a morphism of the site whose underlying morphism of schemes is finite,
as `AlgebraicGeometry.Space.isSurjective_restrictionOfScalars_projection`.  Here `Z_U` is only
*isomorphic* to a representable presheaf: `z` is affine, hence representable, so the chosen
represented base change `ψ : Z' ⟶ U` of `z` along `a` identifies `Z_U` with `yoneda.obj Z'`, and
`ψ` is finite as a morphism of schemes by
`AlgebraicGeometry.Space.isFinite_of_isPullback_of_isFiniteLocallyFree`.  Transporting the
section produced over `Z'` back along that identification gives a pair of Stacks 05Y9 over a
surjective base change of `U`, which is what surjectivity of the projection asks for. -/
@[stacks 05XQ "surjectivity of `Res_{Z_U/U}(W) ⟶ U` for `Z_U` a base change of a finite locally \
free morphism of algebraic spaces"]
theorem isSurjective_restrictionOfScalars_projection_of_isPullback
    {Z Q : AlgebraicSpaces B S hS} (z : Z ⟶ Q) (hz : IsFiniteLocallyFree B S hS z)
    (U : BigFppfOver B S hS) (ZU W : AlgebraicSpaces B S hS)
    (ζ : ZU ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
    (w : W ⟶ ZU) (a : yoneda.obj U ⟶ Q.obj) (ι : ZU.obj ⟶ Z.obj)
    (sq : IsPullback ζ.hom ι a z.hom)
    (hw_surjective : IsSurjective B S hS w.hom) (hw_etale : IsEtale B S hS w.hom) :
    IsSurjective B S hS (restrictionOfScalars B S hS w ζ).projection := by
  classical
  have hrep : yoneda.relativelyRepresentable z.hom :=
    relativelyRepresentable_of_isAffineHom B S hS z hz.1
  have : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (hrep.snd a)) :=
    isFinite_of_isPullback_of_isFiniteLocallyFree B S hS z hrep hz a (hrep.fst a) (hrep.snd a)
      (hrep.isPullback a)
  -- `Z_U` is the represented base change of `z` along `a`.
  let e : ZU.obj ≅ yoneda.obj (hrep.pullback a) :=
    sq.isoIsPullback _ _ (hrep.isPullback a).flip
  have he : e.hom ≫ yoneda.map (hrep.snd a) = ζ.hom :=
    sq.isoIsPullback_hom_fst _ _ (hrep.isPullback a).flip
  have hsurj' : IsSurjective B S hS (w.hom ≫ e.hom) := by
    change Function.Surjective (pointsMap B S hS W.obj (w.hom ≫ e.hom))
    rw [pointsMap_comp]
    exact (pointsMap_surjective_of_isIso B S hS e.hom).comp hw_surjective
  obtain ⟨T, τ, hτ_surjective, -, σ, hσ⟩ :=
    exists_surjective_etale_section_of_isFinite B S hS (hrep.snd a) W.obj (w.hom ≫ e.hom)
      W.property hsurj' (isEtale_comp B S hS hw_etale (isEtale_of_isIso B S hS e.hom))
  obtain ⟨σ', hσ'⟩ : ∃ σ' : _ ⟶ W.obj,
      σ' ≫ (w.hom ≫ e.hom) = pullback.snd (yoneda.map τ) (yoneda.map (hrep.snd a)) :=
    ⟨(PreservesPullback.iso yoneda τ (hrep.snd a)).inv ≫ σ, by
      rw [Category.assoc, hσ, ← PreservesPullback.iso_hom_snd yoneda τ (hrep.snd a),
        Iso.inv_hom_id_assoc]⟩
  let c : pullback (yoneda.map τ) ζ.hom ⟶
      pullback (yoneda.map τ) (yoneda.map (hrep.snd a)) :=
    pullback.map (yoneda.map τ) ζ.hom (yoneda.map τ) (yoneda.map (hrep.snd a))
      (𝟙 _) e.hom (𝟙 _) (by simp) (by simpa using he.symm)
  have hliftover : (c ≫ σ') ≫ w.hom = pullback.snd (yoneda.map τ) ζ.hom := by
    refine (cancel_mono e.hom).1 ?_
    calc ((c ≫ σ') ≫ w.hom) ≫ e.hom = c ≫ (σ' ≫ (w.hom ≫ e.hom)) := by simp
      _ = pullback.snd (yoneda.map τ) ζ.hom ≫ e.hom := by simp [hσ', c]
  let pr : RestrictionPair B S hS w ζ (yoneda.obj T) := ⟨yoneda.map τ, c ≫ σ', hliftover⟩
  have hbase : pr.base = yoneda.map τ := rfl
  have hproj : yonedaEquiv.symm (((restrictionOfScalars B S hS w ζ).pairEquiv T).symm pr) ≫
      (restrictionOfScalars B S hS w ζ).projection = yoneda.map τ := by
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply,
      (restrictionOfScalars B S hS w ζ).projection_pairEquiv T _,
      Equiv.apply_symm_apply, hbase, yonedaEquiv_yoneda_map]
  have hpoints : Function.Surjective (pointsMap B S hS (yoneda.obj T) (yoneda.map τ)) :=
    isSurjective_yoneda_map B S hS τ hτ_surjective
  rw [← hproj, pointsMap_comp] at hpoints
  exact hpoints.of_comp

/-- **Stacks 05XQ in the form the proof of Stacks 05YD and of Stacks 05Y5 uses it.**  For
`g : X' ⟶ X` étale and surjective and `z : Z ⟶ Q` finite locally free, the restriction of
scalars `Res_{Z_U/U}(W) ⟶ U` is surjective for every base change `Z_U = U ×_{a, Q} Z` of `z`
and every fibre product `W = Z_U ×_{b, X} X'` of `g`.

Surjectivity and étaleness of `w : W ⟶ Z_U` are the base-change stability of Stacks 03MH and
Stacks 03FU at the second square, and the rest is
`AlgebraicGeometry.Space.isSurjective_restrictionOfScalars_projection_of_isPullback`. -/
theorem isSurjective_restrictionOfScalars_projection_of_fibreData
    {X' X Z Q : AlgebraicSpaces B S hS} (g : X' ⟶ X) (z : Z ⟶ Q)
    (hg_etale : IsEtale B S hS g.hom) (hg_surjective : IsSurjective B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z)
    (U : BigFppfOver B S hS) (ZU W : AlgebraicSpaces B S hS)
    (ζ : ZU ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
    (w : W ⟶ ZU) (a : yoneda.obj U ⟶ Q.obj) (ι : ZU.obj ⟶ Z.obj) (b : ZU.obj ⟶ X.obj)
    (κ : W.obj ⟶ X'.obj)
    (sq : IsPullback ζ.hom ι a z.hom) (sq' : IsPullback w.hom κ b g.hom) :
    IsSurjective B S hS (restrictionOfScalars B S hS w ζ).projection :=
  have sqSpace : IsPullback (ObjectProperty.homMk κ : W ⟶ X') w g
      (ObjectProperty.homMk b : ZU ⟶ X) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq'.flip
  isSurjective_restrictionOfScalars_projection_of_isPullback B S hS z hz U ZU W ζ w a ι sq
    (isSurjective_of_isPullback B S hS sqSpace hg_surjective)
    (isEtale_of_isPullback B S hS _ w g _ sqSpace hg_etale)

/-! ### Stacks 05YD, surjectivity, at the hypotheses of the source -/

/-- **Stacks 05XQ for the fibre data of Stacks 05YD, outright.**  For `g : X' ⟶ X` étale and
surjective and `z : Z ⟶ Q` finite locally free, the restriction of scalars
`Res_{Z_U/U}(W) ⟶ U` is surjective for every base change `Z_U` of `z` over an object of the site
and every fibre product `W = Z_U ×_{b, X} X'` of `g`.

This discharges `AlgebraicGeometry.Space.IsFibreSectionsSurjective`, the clause the statements of
Stacks 05YD and Stacks 05Y5 consume.  What its docstring records as needed — the passage from
the library's form of Stacks 05XQ, which asks for a *finite* morphism of the site underneath
`Z_U ⟶ U`, to surjectivity of the projection — is
`AlgebraicGeometry.Space.isSurjective_restrictionOfScalars_projection_of_fibreData`, and the
finiteness it needs comes from Stacks 03ZV through
`AlgebraicGeometry.Space.presheaf_of_isFiniteLocallyFree`. -/
theorem isFibreSectionsSurjective {X' X Z Q : AlgebraicSpaces B S hS} (g : X' ⟶ X) (z : Z ⟶ Q) :
    IsFibreSectionsSurjective B S hS g z :=
  fun hg_etale hg_surjective hz U ZU W ζ w a ι b κ sq sq' =>
    isSurjective_restrictionOfScalars_projection_of_fibreData B S hS g z hg_etale hg_surjective
      hz U ZU W ζ w a ι b κ sq sq'

/-- **Stacks 05YD, third conclusion, at the hypotheses of the source.**  Let
`X' → X → Z → Q` be morphisms of algebraic spaces over `S` with `X' → X` étale and surjective
and `Z → Q` finite locally free.  Then `Res_{Z/Q}(X') → Res_{Z/Q}(X)` is surjective.

This is `AlgebraicGeometry.Space.isSurjective_restrictionOfScalarsMap` with its hypothesis
`h05XQ` discharged by `AlgebraicGeometry.Space.isFibreSectionsSurjective`.  It is stated here
rather than beside that theorem because
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartLocalizationBaseChange.lean`, which the
chart comparison of Stacks 03ZU is built on, already imports the file where it lives. -/
@[stacks 05YD "surjective, given `X' ⟶ X` surjective: at the hypotheses of the source, with
nothing carried"]
theorem isSurjective_restrictionOfScalarsMap_of_isFiniteLocallyFree
    {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Z} {x : X ⟶ Z} (g : X' ⟶ X)
    (hg : g ≫ x = x') (z : Z ⟶ Q)
    (hg_etale : IsEtale B S hS g.hom) (hg_surjective : IsSurjective B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z) :
    IsSurjective B S hS (restrictionOfScalarsMap g hg z).1 :=
  isSurjective_restrictionOfScalarsMap g hg z hg_etale hg_surjective hz
    (isFibreSectionsSurjective B S hS g z)

/-- **Stacks 05Y5, third conclusion, at the hypotheses of the source.**  Let `z : Z ⟶ Q` and
`x' : X' ⟶ X ⟶ Q` be morphisms of algebraic spaces over `S` with `X' ⟶ X` étale and surjective
and `z` finite locally free.  Then `Mor_Q(Z, X') ⟶ Mor_Q(Z, X)` is surjective.

This is `AlgebraicGeometry.Space.isSurjective_relativeHomPostcompose` with its hypothesis
`h05XQ` discharged by `AlgebraicGeometry.Space.isFibreSectionsSurjective`; it is stated here for
the reason recorded on
`AlgebraicGeometry.Space.isSurjective_restrictionOfScalarsMap_of_isFiniteLocallyFree`. -/
@[stacks 05Y5 "surjective, given `X' ⟶ X` surjective: at the hypotheses of the source, with
nothing carried"]
theorem isSurjective_relativeHomPostcompose_of_isFiniteLocallyFree
    {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Q} {x : X ⟶ Q} {z : Z ⟶ Q}
    (HX' : RelativeHomConstruction B S hS Z.obj X'.obj Q.obj z.hom x'.hom)
    (HX : RelativeHomConstruction B S hS Z.obj X.obj Q.obj z.hom x.hom)
    (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (hg_etale : IsEtale B S hS g.hom) (hg_surjective : IsSurjective B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z) :
    IsSurjective B S hS (relativeHomPostcompose HX' HX g.hom hg) :=
  isSurjective_relativeHomPostcompose HX' HX g hg hg_etale hg_surjective hz
    (isFibreSectionsSurjective B S hS g z)

end SectionSpaces

end AlgebraicGeometry.Space

end
