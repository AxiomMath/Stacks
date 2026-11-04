module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Specializing a relative weakly associated point into a flat fibre

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` with `X` decent and `f`
locally of finite type, let `F` be a finite type quasi-coherent `𝒪_X`-module and let `s` be a
point of `Y` at which `F` is flat over `Y` at every point of the fibre `X_s`. A point of the
relative weak assassin `WeakAss_{X/Y}(F)` whose closure meets `|X_s|` specializes to a point of
`WeakAss_{X/Y}(F)` lying over `s`.

The source reduces this to the corresponding statement on an étale scheme chart. Choose a chart
`φ : U → X` by a scheme through a point `t` of `|X_s|` in the closure of `x'`, with `u` above
`t`. Decency lifts the specialization `x' ⤳ t` to a specialization `u' ⤳ u` in `|U|` with `u'`
above `x'` (Stacks 03IL), the relative weak assassin is the preimage of the relative weak
assassin along an étale morphism (Stacks 0CUZ), so `u'` lies in `WeakAss_{U/Y}(φ^*F)`, and the
criterion on the chart produces a specialization `u' ⤳ v` with `v` in `WeakAss_{U/Y}(φ^*F)` over
`s`. Its image `φ(v)` is then the required point, the map on points being continuous.

## Main definitions

* `AlgebraicGeometry.Space.ChartPurityCriterion`: the criterion for purity of Stacks 05L3 read
  on an étale scheme chart of `X`, for the relative weak assassin of Stacks 0CV0.
* `AlgebraicGeometry.Space.ChartPuritySpecialization`: the conclusion of that criterion, with
  its hypotheses stripped off, which is all that the descent to the algebraic space consumes.
* `AlgebraicGeometry.Space.ChartPurityCriterionFlatOver`: the same criterion carrying the
  source's own flatness hypothesis — flatness of the *module* `F` over `Y` along the fibre,
  rather than of the morphism `f`.  See the section on the two flatness conditions below.

## Main results

* `AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre`: the
  generalization of Stacks 0CW1 to an arbitrary algebraic-space base, carrying that criterion
  on the chart as a hypothesis.
* `AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_isFlatOver`:
  the same generalization with the source's own flatness hypothesis, carrying the corresponding
  criterion on the chart as a hypothesis.

Neither of those two is registered against Stacks 0CW1, because each carries its chart
criterion as a hypothesis rather than proving it.  Stacks 0CW1 itself is registered on
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase`
of `StacksFrontier/AlgebraicGeometry/Spaces/Flat/PuritySchemeBase.lean`, which is the source's own
statement — base a scheme of the site — and is unconditional.
* `AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_chart`:
  the descent of the criterion's conclusion from the chart to the algebraic space, which is
  the proof shared by the two statements above.

## The two flatness conditions

The flatness hypothesis of the source of Stacks 0CW1 is on the *module*: it reads "`F` is flat
over `S` at all points of `X_s`", which at a point is Stacks 05VV at a point, the predicate
`AlgebraicGeometry.Space.IsFlatOverAtPoint`.  Flatness of the *morphism* at a point,
`AlgebraicGeometry.Space.IsFlatAt` of Stacks 03ML part (2), is a different condition: the two
agree for `F = 𝒪_X` and are incomparable in general.

`AlgebraicGeometry.Space.ChartPurityCriterion` and
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre` take the
morphism condition, so they are the morphism-flat analogue of the source's lemma rather than
the lemma itself.  `AlgebraicGeometry.Space.ChartPurityCriterionFlatOver` and
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_isFlatOver`
take the module condition, which is the source's own.  Nothing else changes: the flatness
hypothesis enters the proof only by being handed to the criterion on the chart, so the descent
from the chart to the algebraic space is literally the same argument for both, and it is
factored out as
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_chart`.

The module condition is also the one the schemes-level statement carries: the flatness
hypothesis of `Stacks.RelativeAssassin.exists_specializes_mem_associatedPoints_fibre` of
Stacks 05L3 is `AlgebraicGeometry.IsFlatOverAt`, the ringed-space module condition of
Stacks 08KT part (1), at the points of the fibre.  So it is
`AlgebraicGeometry.Space.ChartPurityCriterionFlatOver`, not
`AlgebraicGeometry.Space.ChartPurityCriterion`, whose content is that available theorem
transported across the comparison recorded below.

## Implementation notes

The criterion on a chart is carried as the hypothesis `ChartPurityCriterion`, respectively
`ChartPurityCriterionFlatOver`, and not proved. The content of
`ChartPurityCriterionFlatOver` — the one carrying the source's own flatness condition, see the
section above — is the schemes-level criterion for purity
`Stacks.RelativeAssassin.exists_specializes_mem_associatedPoints_fibre` of Stacks 05L3, which
is available, transported across the comparison of the relative weak assassin
`AlgebraicGeometry.Space.IsRelativeWeaklyAssociatedPoint` of Stacks 0CV0, for a *represented*
algebraic space over a represented target, with the relative weak assassin
`AlgebraicGeometry.relativeWeaklyAssociatedPoints` of Stacks 05AV of the representing morphism
of schemes — which for a morphism locally of finite type is the relative assassin
`Stacks.Divisors.relativeAssassin`, by
`AlgebraicGeometry.relativeWeaklyAssociatedPoints_eq_relativeAssassin` of Stacks 05F2. That
comparison is
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints`,
in `StacksFrontier/AlgebraicGeometry/Divisors/MorphismWeaklyAssociated/`
`StacksFrontier/AlgebraicGeometry/Divisors/MorphismWeaklyAssociated/RepresentedFibreComparison.lean`, and it is *proved* there — see the implementation notes
below.

It is *not* the comparison of `AlgebraicGeometry.Scheme.Modules` of a scheme of the site with
`AlgebraicGeometry.Space.Modules` of the algebraic space it represents that is missing, as this
file previously recorded. That comparison is
`AlgebraicGeometry.Space.representedZariskiRestriction`: it matches the two weak assassins
(unconditionally in one direction, and over finite generation of the maximal ideals of the
representing scheme in the other, which on the fibres of a morphism locally of finite type is
available since those fibres are locally Noetherian by Stacks 0CUY), and it commutes with
inverse images along an arbitrary morphism of the site by
`AlgebraicGeometry.Space.representedZariskiRestrictionBaseChangeIso`. Nor is it the flatness
hypothesis: Stacks 05VU **is** registered,
as `AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint`,
and with it the existential over chart diagrams in
`AlgebraicGeometry.Space.IsFlatOverAtPoint` may be read at any one square — at the identity
square of a represented situation it is exactly the `AlgebraicGeometry.IsFlatOverAt` on the
representing morphism of schemes that Stacks 05L3 asks for, which is
`AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAt_representedZariskiRestriction` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModulePointChartIndependence.lean`.

Both things that stood between that and the criterion are now closed, and the comparison is
*proved* for a target represented by a scheme of the site:

* the fibre of a morphism of represented algebraic spaces over a field-valued point of the
  target *is* represented, by the fibre product formed in the site, and its representing scheme
  is the fibre product of the representing schemes:
  `AlgebraicGeometry.Space.fibreRepresentedIso` and
  `AlgebraicGeometry.Space.isPullback_toScheme_fibre` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedFibreScheme.lean`. Over the residue field of
  a point of the target scheme that fibre product is the scheme-theoretic fibre
  `AlgebraicGeometry.Scheme.Hom.fiber`, which is
  `AlgebraicGeometry.Space.isPullback_toScheme_fibre_schemePointRepresentative`;
* the passage from a field-valued point of the target to the residue field of its image is
  `AlgebraicGeometry.isWeaklyAssociatedPoint_fiber_of_fieldValuedFibre` of
  `StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints/FieldValuedFibreDescent.lean`: a
  field-valued point of a scheme factors through the residue field of its image, so the fibre
  over it is a field base change of the scheme-theoretic fibre and the descent is Stacks 0CUC.

With those, the comparison is proved for an arbitrary morphism of the site and a quasi-coherent
module, as
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints`
of `StacksFrontier/AlgebraicGeometry/Divisors/MorphismWeaklyAssociated/`
`StacksFrontier/AlgebraicGeometry/Divisors/MorphismWeaklyAssociated/RepresentedFibreComparison.lean`: neither affineness of the source scheme nor local finiteness
of the type of the morphism is required, the quasi-coherence of the restriction of the module to
a fibre being Stacks 03GA along an arbitrary morphism of algebraic spaces.

So the source's statement — base a scheme — is proved unconditionally, as
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase` of
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/PuritySchemeBase.lean`, by choosing an *affine* étale
chart through the point of `|X_s|`, exactly as the source does.

`ChartPurityCriterion`, which carries flatness of the morphism rather than of the module, is
not Stacks 05L3 transported at all: the two flatness conditions are incomparable in general,
as the section above records, so the comparison above discharges
`ChartPurityCriterionFlatOver` and not it.

The target of the criteria below is an arbitrary algebraic space `Y`, whereas the base of
Stacks 0CW1 is a scheme `S`. So the two statements below are the generalization of the source to
an algebraic-space base, and they keep the chart criterion as a hypothesis; the source's own
case is the unconditional theorem named above. Carrying that case to an arbitrary `Y` is a
further descent through an étale chart of `Y`, which the source does not perform: the relative
weak assassin transfers along such a base change by Stacks 0CV2, proved as
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_of_baseChange` and
`AlgebraicGeometry.Space.exists_isRelativeWeaklyAssociatedPoint_baseChange`, but the second of
those reads its witness at a prescribed field-valued representative, so it consumes the descent
above for an arbitrary target, where the fibre is not represented.

The hypotheses of the source which enter only through that criterion — local finiteness of the
type of `f`, finiteness of the type and quasi-coherence of `F`, and flatness of `F` over `Y`
along the fibre — are hypotheses of `ChartPurityCriterion` itself, so they appear in the
statement below exactly as the source carries them. Decency of `X` is used directly, for the
lifting of the specialization to the chart.

The target of `f` is an arbitrary algebraic space rather than the representable space of the
source's base scheme, as it is for the relative weak assassin of Stacks 0CV0 itself; taking it
to be `h_S` gives the source's statement verbatim.

The set `|X_s|` is read as the set of points of `|X|` whose image under `|f|` is `s`, and the
closure of `{x'}` meeting it as the existence of a specialization of `x'` in it; that is the
reading of Stacks 0AC8 recorded in
`AlgebraicGeometry.Space.exists_mem_closure_mem_range_fibre_iff`. The conclusion is stated with
the specialization witness, which is what the schemes-level statement of Stacks 05L3 gives and
is stronger than the mere meeting of the closure.

## References

* [Stacks Project, Lemma 77.6.1 (Tag 0CW1)](https://stacks.math.columbia.edu/tag/0CW1)
* [Stacks Project, Tag 05L3](https://stacks.math.columbia.edu/tag/05L3)
* [Stacks Project, Tag 03IL](https://stacks.math.columbia.edu/tag/03IL)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 05AV](https://stacks.math.columbia.edu/tag/05AV)
* [Stacks Project, Tag 05F2](https://stacks.math.columbia.edu/tag/05F2)
* [Stacks Project, Tag 0CUC](https://stacks.math.columbia.edu/tag/0CUC)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The criterion for purity of Stacks 05L3 on an étale scheme chart.** For every algebraic
space `V` represented by a scheme of the site and every étale `φ : V ⟶ X`, a point of the
relative weak assassin `WeakAss_{V/Y}(φ^*F)` which specializes to a point of `V` lying over `s`
specializes to a point of `WeakAss_{V/Y}(φ^*F)` lying over `s`.

This is the schemes-level statement of Stacks 05L3 read through the relative weak assassin of
Stacks 0CV0; see the implementation notes of this file. -/
def ChartPurityCriterion (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] [SheafOfModules.IsFiniteTypeOnSite F]
    (s : points B S hS Y.1) : Prop :=
  IsLocallyOfFiniteType B S hS f.hom →
    (∀ t : points B S hS X.1, pointsMap B S hS X.1 f.hom t = s → IsFlatAt B S hS f.hom t) →
      ∀ V : AlgebraicSpaces B S hS, (∃ T : BigFppfOver B S hS, Nonempty (yoneda.obj T ≅ V.1)) →
        ∀ φ : V ⟶ X, IsEtale B S hS φ.hom →
          ∀ u' w : points B S hS V.1,
            IsRelativeWeaklyAssociatedPoint B S hS (φ ≫ f)
              ((modulePullback B S hS φ).obj F) u' →
            u' ⤳ w → pointsMap B S hS V.1 (φ ≫ f).hom w = s →
              ∃ v : points B S hS V.1, u' ⤳ v ∧
                pointsMap B S hS V.1 (φ ≫ f).hom v = s ∧
                IsRelativeWeaklyAssociatedPoint B S hS (φ ≫ f)
                  ((modulePullback B S hS φ).obj F) v

/-- **The conclusion of the criterion for purity of Stacks 05L3 on an étale scheme chart.**
This is `AlgebraicGeometry.Space.ChartPurityCriterion` with its hypotheses stripped off, and it
is all that the descent of the criterion from the chart to the algebraic space consumes. -/
def ChartPuritySpecialization (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] [SheafOfModules.IsFiniteTypeOnSite F]
    (s : points B S hS Y.1) : Prop :=
  ∀ V : AlgebraicSpaces B S hS, (∃ T : BigFppfOver B S hS, Nonempty (yoneda.obj T ≅ V.1)) →
    ∀ φ : V ⟶ X, IsEtale B S hS φ.hom →
      ∀ u' w : points B S hS V.1,
        IsRelativeWeaklyAssociatedPoint B S hS (φ ≫ f)
          ((modulePullback B S hS φ).obj F) u' →
        u' ⤳ w → pointsMap B S hS V.1 (φ ≫ f).hom w = s →
          ∃ v : points B S hS V.1, u' ⤳ v ∧
            pointsMap B S hS V.1 (φ ≫ f).hom v = s ∧
            IsRelativeWeaklyAssociatedPoint B S hS (φ ≫ f)
              ((modulePullback B S hS φ).obj F) v

/-- **The criterion for purity of Stacks 05L3 on an étale scheme chart, with the source's own
flatness hypothesis.** This is `AlgebraicGeometry.Space.ChartPurityCriterion` with flatness of
the morphism `f` along the fibre replaced by flatness of the module `F` over `Y` along the
fibre, which is what the source of Stacks 0CW1 — and the schemes-level statement of
Stacks 05L3 it rests on — assumes.

See the section of the module docstring on the two flatness conditions. -/
def ChartPurityCriterionFlatOver (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] [SheafOfModules.IsFiniteTypeOnSite F]
    (s : points B S hS Y.1) : Prop :=
  IsLocallyOfFiniteType B S hS f.hom →
    (∀ t : points B S hS X.1, pointsMap B S hS X.1 f.hom t = s →
        IsFlatOverAtPoint B S hS X.2 f.hom F t) →
      ChartPuritySpecialization B S hS f F s

/-- **The descent of the criterion for purity from an étale scheme chart to the algebraic
space.** Granted the conclusion of the criterion on the charts of `X`, a point `x'` of the
relative weak assassin `WeakAss_{X/Y}(F)` which specializes to a point of `X_s` specializes to
a point of `WeakAss_{X/Y}(F)` lying over `s`.

This is the whole proof of Stacks 0CW1 after the criterion has been applied, and it is shared
by the two forms of that lemma below: the flatness hypothesis of either form enters only by
being handed to the criterion, so neither of them is used here. Choose a chart `φ : V → X` by a
scheme through a point `t` of `|X_s|` in the closure of `x'`, with `u` above `t`; decency lifts
the specialization `x' ⤳ t` to a specialization `u' ⤳ u` in `|V|` with `u'` above `x'`
(Stacks 03IL); the relative weak assassin is the preimage of the relative weak assassin along
an étale morphism (Stacks 0CUZ), so `u'` lies in `WeakAss_{V/Y}(φ^*F)`; the granted conclusion
produces a specialization `u' ⤳ v` with `v` in `WeakAss_{V/Y}(φ^*F)` over `s`, and its image
`φ(v)` is the required point, the map on points being continuous. -/
theorem exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_chart
    (f : X ⟶ Y) (hXdec : IsDecentSpace B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteTypeOnSite F] (s : points B S hS Y.1)
    (htail : ChartPuritySpecialization B S hS f F s)
    {x' : points B S hS X.1} (hx' : IsRelativeWeaklyAssociatedPoint B S hS f F x')
    (hmeets : ∃ t : points B S hS X.1, x' ⤳ t ∧ pointsMap B S hS X.1 f.hom t = s) :
    ∃ x : points B S hS X.1, x' ⤳ x ∧ pointsMap B S hS X.1 f.hom x = s ∧
      IsRelativeWeaklyAssociatedPoint B S hS f F x := by
  obtain ⟨t, hspec, hts⟩ := hmeets
  obtain ⟨U, a, u, ha, hau, -, -⟩ := exists_etale_scheme_chart_through_point B S hS X.2
    (𝟙 X.1) (isEtale_id B S hS X.1) t
  set V : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  set φ : V ⟶ X := ObjectProperty.homMk a
  have hφhom : φ.hom = a := rfl
  have hφ : IsEtale B S hS φ.hom := hφhom ▸ ha
  -- Lift the specialization `x' ⤳ t` to the chart, by decency.
  obtain ⟨u', hu'spec, hu'x⟩ := exists_specialization_lift_of_isDecentSpace B S hS X.1 X.2
    hXdec t x' hspec U a ((isEtale_iff_presheaf_of_yoneda B S hS a).1 ha) u hau
  -- The relative weak assassin is the preimage of the relative weak assassin on the chart.
  have hu' : IsRelativeWeaklyAssociatedPoint B S hS (φ ≫ f)
      ((modulePullback B S hS φ).obj F) u' :=
    (isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS φ hφ f F u').2 (by
      rw [hφhom, hu'x]; exact hx')
  have hcomp : ∀ w : points B S hS V.1, pointsMap B S hS V.1 (φ ≫ f).hom w =
      pointsMap B S hS X.1 f.hom (pointsMap B S hS V.1 φ.hom w) := by
    intro w
    rw [show (φ ≫ f).hom = φ.hom ≫ f.hom from rfl, pointsMap_comp]
    rfl
  have hus : pointsMap B S hS V.1 (φ ≫ f).hom u = s := by
    rw [hcomp u, hφhom, hau]; exact hts
  obtain ⟨v, hv1, hv2, hv3⟩ := htail V ⟨U, ⟨Iso.refl _⟩⟩ φ hφ u' u hu' hu'spec hus
  refine ⟨pointsMap B S hS V.1 φ.hom v, ?_, ?_, ?_⟩
  · have := hv1.map (continuous_pointsMap B S hS φ.hom)
    rwa [hφhom, hu'x] at this
  · rw [← hcomp v]; exact hv2
  · exact (isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS φ hφ f F v).1 hv3

/-- **The generalization of Stacks 0CW1 to an arbitrary algebraic-space base.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` with `X` decent and `f` locally
of finite type, let `F` be a finite type quasi-coherent `𝒪_X`-module, and let `s` be a point of
`Y` such that `f` is flat at every point of the fibre `X_s`. If a point `x'` of the relative
weak assassin `WeakAss_{X/Y}(F)` specializes to a point of `X_s` — that is, if the closure of
`{x'}` in `|X|` meets `|X_s|` — then it specializes to a point of `WeakAss_{X/Y}(F)` lying over
`s`, so the closure meets `WeakAss_{X/Y}(F) ∩ |X_s|`.

The source's `Ass_{X/S}(F)` is the relative weak assassin of Stacks 0CV0, which it writes that
way because a morphism locally of finite type has locally Noetherian fibres (Stacks 0CUY).

This statement differs from the source in two respects. Its base is an arbitrary algebraic
space `Y` rather than a scheme `S`, and its flatness hypothesis is flatness of the *morphism*
along the fibre, `AlgebraicGeometry.Space.IsFlatAt` of Stacks 03ML part (2), rather than
flatness of the *module* which the source asks for; the two flatness conditions are
incomparable in general, so this is not Stacks 05L3 transported either. See the section on the
two flatness conditions above.

It carries `AlgebraicGeometry.Space.ChartPurityCriterion` as the hypothesis `hchart` — the
criterion for purity of Stacks 05L3 on an étale scheme chart of `X`, at flatness of the
morphism — and therefore does **not** carry the tag 0CW1. The criterion is not proved for an
arbitrary algebraic-space base: it would need the field-valued descent for a non-represented
target, Stacks 0CUS, which the source never performs and which is available here only as
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_fieldBaseChange`, itself carrying the
represented case as a hypothesis. What is proved here is the descent of the criterion's
conclusion from the chart to the algebraic space,
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_chart`.

Stacks 0CW1 is registered on
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase`
of `StacksFrontier/AlgebraicGeometry/Spaces/Flat/PuritySchemeBase.lean`, which is the source's own
statement — base a scheme of the site, flatness on the module — and is unconditional. -/
theorem exists_specializes_isRelativeWeaklyAssociatedPoint_fibre (f : X ⟶ Y)
    (hXdec : IsDecentSpace B S hS X.1) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteTypeOnSite F] (s : points B S hS Y.1)
    (hflat : ∀ t : points B S hS X.1, pointsMap B S hS X.1 f.hom t = s →
      IsFlatAt B S hS f.hom t)
    (hchart : ChartPurityCriterion B S hS f F s)
    {x' : points B S hS X.1} (hx' : IsRelativeWeaklyAssociatedPoint B S hS f F x')
    (hmeets : ∃ t : points B S hS X.1, x' ⤳ t ∧ pointsMap B S hS X.1 f.hom t = s) :
    ∃ x : points B S hS X.1, x' ⤳ x ∧ pointsMap B S hS X.1 f.hom x = s ∧
      IsRelativeWeaklyAssociatedPoint B S hS f F x :=
  exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_chart B S hS f
    hXdec F s (hchart hf hflat) hx' hmeets

/-- **The generalization of Stacks 0CW1 to an arbitrary algebraic-space base, with the source's
own flatness hypothesis.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`
with `X` decent and `f` locally of finite type, let `F` be a finite type quasi-coherent
`𝒪_X`-module, and let `s` be a point of `Y` such that `F` is flat over `Y` at every point of
the fibre `X_s`. If a point `x'` of the relative weak assassin `WeakAss_{X/Y}(F)` specializes
to a point of `X_s` — that is, if the closure of `{x'}` in `|X|` meets `|X_s|` — then it
specializes to a point of `WeakAss_{X/Y}(F)` lying over `s`, so the closure meets
`WeakAss_{X/Y}(F) ∩ |X_s|`.

The flatness hypothesis here is the source's own: "`F` is flat over `S` at all points of
`X_s`" is flatness of the *module* over the target at the points of the fibre, which is
`AlgebraicGeometry.Space.IsFlatOverAtPoint`, Stacks 05VV at a point.  What is more general than
the source is the base: `Y` is an arbitrary algebraic space, where the source takes a scheme.
The companion `AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre`
assumes instead that the *morphism* is flat along the fibre, Stacks 03ML part (2).

It carries `AlgebraicGeometry.Space.ChartPurityCriterionFlatOver` as the hypothesis `hchart` —
the criterion for purity of Stacks 05L3 read on an étale scheme chart of `X`, at the same
module flatness — and therefore does **not** carry the tag 0CW1. The criterion is not proved
for an arbitrary algebraic-space base: it would need the field-valued descent for a
non-represented target, Stacks 0CUS, which the source never performs and which is available
here only as `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_fieldBaseChange`, itself
carrying the represented case as a hypothesis. What is proved here is the descent of the
criterion's conclusion from the chart to the algebraic space,
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_chart`.

Stacks 0CW1 is registered on
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase`
of `StacksFrontier/AlgebraicGeometry/Spaces/Flat/PuritySchemeBase.lean`, which is the source's own
statement — base a scheme of the site — and is unconditional; there the criterion is discharged,
because an affine étale chart over a represented base makes the comparison of the two relative
weak assassins provable. -/
theorem exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_isFlatOver (f : X ⟶ Y)
    (hXdec : IsDecentSpace B S hS X.1) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteTypeOnSite F] (s : points B S hS Y.1)
    (hflat : ∀ t : points B S hS X.1, pointsMap B S hS X.1 f.hom t = s →
      IsFlatOverAtPoint B S hS X.2 f.hom F t)
    (hchart : ChartPurityCriterionFlatOver B S hS f F s)
    {x' : points B S hS X.1} (hx' : IsRelativeWeaklyAssociatedPoint B S hS f F x')
    (hmeets : ∃ t : points B S hS X.1, x' ⤳ t ∧ pointsMap B S hS X.1 f.hom t = s) :
    ∃ x : points B S hS X.1, x' ⤳ x ∧ pointsMap B S hS X.1 f.hom x = s ∧
      IsRelativeWeaklyAssociatedPoint B S hS f F x :=
  exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_chart B S hS f
    hXdec F s (hchart hf hflat) hx' hmeets

end AlgebraicGeometry.Space

end
