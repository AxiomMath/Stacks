module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Quasi-coherence of the direct image: the reduction to an affine base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 03M9 asserts that if `f` is quasi-compact and quasi-separated then the direct
image `f_*` carries quasi-coherent `𝒪_X`-modules to quasi-coherent `𝒪_Y`-modules.  This file
carries out the *first step* of that proof — the reduction to the case of an affine base — and
assembles the whole statement from that reduction and one explicit hypothesis holding the
second step.

The reduction is: quasi-coherence of `f_*F` is tested on the affine étale scheme charts `V`
of `Y` (Stacks 03M0, conditions (1) and (4)), and on such a chart the restriction `(f_*F)|_V`
is `f'_*(F|_U)` for `U = V ×_Y X` and `f'` the base change of `f` (Stacks 04CF).  Along the way
the base-changed morphism `f'` is shown to be quasi-compact and quasi-separated (Stacks 03HF
and Stacks 03KL, part (3)), and its source `U` to be a quasi-compact algebraic space admitting
an affine surjective étale chart (Stacks 03H6) — which is the data the second step consumes.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeProjection` is the base change `f' : U ⟶ V` of `f`
  along an étale scheme chart `V` of `Y`, as a morphism of algebraic spaces, with
  `U = V ×_Y X` the algebraic space `AlgebraicGeometry.Space.chartBaseChange`.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_chartBaseChangeProjection` and
  `AlgebraicGeometry.Space.isQuasiSeparated_chartBaseChangeProjection`: the base change of a
  quasi-compact, quasi-separated morphism along an étale chart of the target is quasi-compact
  and quasi-separated.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_chartBaseChange` and
  `AlgebraicGeometry.Space.exists_affine_etale_surjective_chart_chartBaseChange`: for an
  *affine* chart `V` and a quasi-compact `f` the algebraic space `U = V ×_Y X` is quasi-compact
  and therefore has an affine surjective étale chart.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_iff_forall_affine` is the
  reduction itself, an unconditional equivalence.
* `AlgebraicGeometry.Space.pushforward_isQuasicoherentOnSite_of_forall_affine` is Stacks 03M9
  in the binders of its source statement, conditional on the single hypothesis `haffine`.

## Implementation notes

**No `@[stacks 03M9]` attribute is carried and no part of Stacks 03M9 is proved here.**  The
conclusion is reached only from `haffine`, the case of an affine base, which is the entire
mathematical content of the lemma: the exact sequence of Stacks 03M8, quasi-coherence of the
direct image along a quasi-compact quasi-separated morphism of *schemes* (Descent,
Proposition 03LC, part (3)) and stability of quasi-coherence under kernels (Stacks 03M1) are
all absent from this development.

`haffine` is stated in the reading of Stacks 04CF that
`AlgebraicGeometry.Space.modulePushforward_comp_overFunctorIso` delivers, namely with `F|_U`
restriction to the slice of the *spaces-étale* site of `X` at `U` and `f'_*` the direct image
along the localized base-change functor, rather than with `F|_U` a module on the small étale
site of the algebraic space `U` and `f'_*` the functor
`AlgebraicGeometry.Space.modulePushforward` of the morphism
`AlgebraicGeometry.Space.chartBaseChangeProjection`.  That is forced, and it is the reason the
reduction cannot be continued here: identifying the slice of `X_{spaces,étale}` at `U` with the
small étale site of `U`, compatibly with the structure sheaves, is the spaces-étale analogue of
Stacks 04M0, and for a non-representable `f` the object `U` is an algebraic space rather than an
étale scheme chart, so
`AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart` does not apply.  Every citation that
the second step of the Stacks proof makes — Stacks 03M8, Stacks 03H6 and Stacks 03M1 — is a
statement about modules on the small étale site of an algebraic space, so none of them can be
applied to `f'_*(F|_U)` in the slice reading.

What is *not* blocked by that gap is the geometry of `f'`: the base-changed morphism is
available as an honest morphism of algebraic spaces, because the objects of the spaces-étale
site of `X` are algebraic spaces over `X` and the base-change datum
`AlgebraicGeometry.Space.spacesBaseChange` carries its cartesian projection.  So the three
geometric citations of the first step — Stacks 03HF, Stacks 03KL, part (3) and Stacks 03H6 —
are discharged here rather than assumed, and the quasi-compactness and quasi-separatedness
hypotheses on `f` are consumed in doing so.

Quasi-separatedness is stable under base change by
`AlgebraicGeometry.Space.isQuasiSeparated_pullbackSnd`, but only for the chosen fibre product.
The cartesian-square form needed here is obtained by reading quasi-compactness of a morphism as
a `CategoryTheory.MorphismProperty` of presheaves, which is stable under base change by
Stacks 03HF, and quasi-separatedness as its
`CategoryTheory.MorphismProperty.diagonal`; Mathlib's
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.diagonal` then supplies the statement.
The two instances are introduced locally, so no new global instance on morphisms of presheaves
is registered.

The module universe is the universe `u` of the schemes and not the free universe `m` of the
source statement, because `AlgebraicGeometry.Space.modulePushforward` exists only at that
universe; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleDirectImage.lean`.

Quasi-coherence of `F` itself is kept as an instance hypothesis, in the binder position of the
source statement, although the reduction does not use it: it is an input to `haffine`, through
quasi-coherence of the restriction `F|_U`.

## References

* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The base change of a morphism along an étale chart of the target -/

/-- The base change `f' : U ⟶ V` of a morphism `f : X ⟶ Y` of algebraic spaces along an étale
scheme chart `V` of `Y`, as a morphism of algebraic spaces over `S`.

Its source is the algebraic space `U = V ×_Y X` of
`AlgebraicGeometry.Space.chartBaseChange`, étale over `X`, and its target is the algebraic
space represented by the scheme underlying `V`.  The morphism is the cartesian projection of
the base-change datum `AlgebraicGeometry.Space.spacesBaseChange` on the spaces-étale sites. -/
noncomputable abbrev chartBaseChangeProjection (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    (SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V) ⟶
      (SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj V) :=
  (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V)

/-- The base change of a chart is cartesian, as a square of morphisms of presheaves: the
algebraic space `U = V ×_Y X` is the fibre product of the chart `V ⟶ Y` and `f : X ⟶ Y`.

This is the `isPullback` field of `AlgebraicGeometry.Space.spacesBaseChange` transported from
the category of algebraic spaces to presheaves by
`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`. -/
theorem isPullback_chartBaseChangeProjection (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    IsPullback (chartBaseChangeProjection B S hS f V).hom
      (chartBaseChange B S hS f V).1.hom.hom
      ((comparisonFunctor B S hS Y).obj V).1.hom.hom f.hom :=
  AlgebraicSpaces.isPullback_hom _ _ _ ((spacesBaseChange B S hS f).isPullback
    ((comparisonFunctor B S hS Y).obj V))

/-- **Stacks 03HF for the base change along an étale chart.** The base change of a
quasi-compact morphism of algebraic spaces along an étale scheme chart of its target is
quasi-compact. -/
theorem isQuasiCompact_chartBaseChangeProjection (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (hfqc : IsQuasiCompact B S hS f.hom) :
    IsQuasiCompact B S hS (chartBaseChangeProjection B S hS f V).hom :=
  isQuasiCompact_of_isPullback B S hS
    (isPullback_chartBaseChangeProjection B S hS f V).flip hfqc

/-- **Stacks 03KL, part (3), for the base change along an étale chart.** The base change of a
quasi-separated morphism of algebraic spaces along an étale scheme chart of its target is
quasi-separated. -/
theorem isQuasiSeparated_chartBaseChangeProjection (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (hfqs : IsQuasiSeparated B S hS f.hom) :
    IsQuasiSeparated B S hS (chartBaseChangeProjection B S hS f V).hom :=
  isQuasiSeparated_of_isPullback B S hS
    (isPullback_chartBaseChangeProjection B S hS f V).flip hfqs

/-- An étale scheme chart with affine underlying scheme is a quasi-compact algebraic space.

The presheaf it represents is an affine algebraic space, and an affine algebraic space is
quasi-compact in the sense of Stacks 03E3. -/
theorem isQuasiCompactSpace_chart (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V))) :
    IsQuasiCompactSpace B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V)) :=
  IsAffineSpace.isQuasiCompactSpace ⟨_, hV, ⟨Iso.refl _⟩⟩

/-- For a quasi-compact `f` and an *affine* étale chart `V` of `Y` the algebraic space
`U = V ×_Y X` is quasi-compact.

This is quasi-compactness of `f` in the sense of Stacks 03HE applied to the quasi-compact
algebraic space represented by the scheme underlying `V`, together with invariance of
quasi-compactness of an algebraic space under isomorphism. -/
theorem isQuasiCompactSpace_chartBaseChange (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))
    (hfqc : IsQuasiCompact B S hS f.hom) :
    IsQuasiCompactSpace B S hS
      ((SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V)).1 :=
  IsQuasiCompactSpace.of_iso B S hS
    (hfqc _ (isAlgebraicSpace_yoneda B S hS _) (isQuasiCompactSpace_chart B S hS V hV)
      ((comparisonFunctor B S hS Y).obj V).1.hom.hom)
    (IsPullback.isoPullback (h := isPullback_chartBaseChangeProjection B S hS f V)).symm

/-- **Stacks 03H6 for the base change along an affine étale chart.** For a quasi-compact `f`
and an affine étale chart `V` of `Y` the algebraic space `U = V ×_Y X` admits a surjective
étale morphism from a presheaf represented by an *affine* object of the big fppf site.

This is the chart that the second step of the proof of Stacks 03M9 feeds to the exact sequence
of Stacks 03M8. -/
theorem exists_affine_etale_surjective_chart_chartBaseChange (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))
    (hfqc : IsQuasiCompact B S hS f.hom) :
    ∃ (W : BigFppfOver B S hS)
      (p : yoneda.obj W ⟶
        ((SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V)).1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
        (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        IsEtale B S hS p :=
  (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _
    ((SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V)).2).1
    (isQuasiCompactSpace_chartBaseChange B S hS f V hV hfqc)

/-! ### The reduction of Stacks 03M9 to an affine base -/

/-- **The first step of the proof of Stacks 03M9.** The direct image `f_*F` of an
`𝒪_X`-module along a morphism of algebraic spaces is quasi-coherent exactly when, for every
affine étale scheme chart `V` of `Y`, the localized direct image `f'_*(F|_U)` of Stacks 04CF
is quasi-coherent on the slice of the small étale site of `Y` at `V`.

Quasi-coherence is tested on the affine étale charts by Stacks 03M0, conditions (1) and (4),
and the restriction of `f_*F` to such a chart is identified with `f'_*(F|_U)` by Stacks 04CF,
`AlgebraicGeometry.Space.modulePushforward_comp_overFunctorIso`; quasi-coherence on a site is
invariant under isomorphism.  No hypothesis on `f` and no quasi-coherence of `F` is used. -/
theorem isQuasicoherentOnSite_modulePushforward_iff_forall_affine (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite ↔
      ∀ V : SmallEtale B S hS Y.1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS Y.1).obj V)) →
        ((chartLocalizedModulePushforward B S hS f V).obj
          ((moduleChartBaseChangeRestriction B S hS f V).obj F)).IsQuasicoherentOnSite := by
  rw [isQuasicoherentOnSite_iff_forall_affine_over]
  refine ⟨fun h V hV ↦ ?_, fun h V hV ↦ ?_⟩
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((modulePushforward_comp_overFunctorIso B S hS f V).app F) (h V hV)
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((modulePushforward_comp_overFunctorIso B S hS f V).app F).symm (h V hV)

/-- **Stacks 03M9, conditional on its affine-base case.** Let `f : X ⟶ Y` be a quasi-compact,
quasi-separated morphism of algebraic spaces over `S` and let `F` be a quasi-coherent
`𝒪_X`-module on the small étale site of `X`.  Then `f_*F` is quasi-coherent, granted
`haffine`: the same conclusion for the base change of `f` along every affine étale scheme chart
of `Y`, in the reading of Stacks 04CF.

The quasi-compactness and quasi-separatedness of the base-changed morphism, which `haffine`
takes as hypotheses, are supplied here from those of `f` by Stacks 03HF and Stacks 03KL,
part (3).  **This is not a proof of Stacks 03M9**: `haffine` holds the whole of the second step
of the Stacks argument, and no `@[stacks 03M9]` attribute is carried.  See the implementation
notes, which also record why `haffine` cannot be stated with `f'_*` taken to be
`AlgebraicGeometry.Space.modulePushforward` of
`AlgebraicGeometry.Space.chartBaseChangeProjection`. -/
theorem pushforward_isQuasicoherentOnSite_of_forall_affine (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (haffine : ∀ V : SmallEtale B S hS Y.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
      IsQuasiCompact B S hS (chartBaseChangeProjection B S hS f V).hom →
      IsQuasiSeparated B S hS (chartBaseChangeProjection B S hS f V).hom →
      ((chartLocalizedModulePushforward B S hS f V).obj
        ((moduleChartBaseChangeRestriction B S hS f V).obj F)).IsQuasicoherentOnSite) :
    ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_modulePushforward_iff_forall_affine B S hS f F).2 fun V hV ↦
    haffine V hV (isQuasiCompact_chartBaseChangeProjection B S hS f V hfqc)
      (isQuasiSeparated_chartBaseChangeProjection B S hS f V hfqs)

end AlgebraicGeometry.Space

end
