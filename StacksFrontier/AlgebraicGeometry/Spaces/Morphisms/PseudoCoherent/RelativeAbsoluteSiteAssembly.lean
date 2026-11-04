module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsPseudoCoherentAtTop
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPseudoCoherentTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeAbsolute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands

/-!
# The site-level form of Stacks 0DII, assembled over the covering sieve of affine chart diagrams

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is flat and locally of
finite presentation, and let `E` be an object of `D_QCoh(𝒪_X)`.  The source's statement of
Stacks 0DII compares relative pseudo-coherence of `E` over `Y` with pseudo-coherence of `E` on
`X`, the latter being `AlgebraicGeometry.RingedSite.IsPseudoCoherent` on the small étale ringed
site of `X`.  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/
RelativeAbsolute.lean` proves the comparison with the right-hand side read *on the charts* — the
absolute condition on the complexes `RΓ(U, E)` of `𝒪_X(U)`-modules — and its module
documentation records what the site-level right-hand side still owes.

This file pays the half of that which is bookkeeping, and isolates the half which is not.  What
is paid here is the passage between the chartwise condition and the site-level one *over the
covering sieve of affine chart diagrams*: both directions, in a fixed degree and in all degrees.
What is isolated is the pointwise dictionary at a single affine chart,
`AlgebraicGeometry.Space.ChartPseudoCoherenceDictionaryFrom`, which is the only remaining
mathematical input and is a statement about one chart with no quantification over coverings left
in it.

## Main definitions

* `AlgebraicGeometry.Space.ChartPseudoCoherenceDictionaryFrom`: at an affine étale scheme chart
  `U` of `X`, that `m`-pseudo-coherence of the complex `RΓ(U, E)` of `𝒪_X(U)`-modules is
  `m`-pseudo-coherence of the restriction of `E` to the localization `X_étale/U`.  This is item
  (iii) of the display in the module documentation of `RelativeAbsolute.lean`, stated at the
  `AlgebraicGeometry.RingedSite.C` spelling of the chart and with the slice written
  `X.over U`, which is the shape the locality criterion of Stacks 08FU (3) consumes.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_of_forall_affineChart`: **the assembly.**  If the
  dictionary holds and `RΓ(U, E)` is `m`-pseudo-coherent on every commuting square of affine
  étale charts over `f`, then `E` is `m`-pseudo-coherent on the small étale ringed site of `X`.
* `AlgebraicGeometry.Space.chartPseudoCoherenceDictionaryFrom_of_chartTransport`: the dictionary
  reduced to a statement about the derived chart transport, the restriction of scalars that
  comparison (i) carries being absorbed by
  `AlgebraicGeometry.Space.isPseudoCoherentFrom_chartDerivedSections_iff_chartTransportTop`.  The
  reduced hypothesis mentions neither a chart nor an algebraic space once its right-hand side is
  carried to the small étale site of the chart's scheme.
* `AlgebraicGeometry.Space`
  `.isRelativelyPseudoCoherentFrom_iff_isPseudoCoherentFrom_of_chartDictionary`: the site-level
  form of Stacks 0DII in a fixed degree, granted the dictionary.
* `AlgebraicGeometry.Space.isRelativelyPseudoCoherent_iff_isPseudoCoherent_of_chartDictionary`:
  the same in all degrees at once, which is the shape of the source statement.

## What is proved and what is assumed

No `@[stacks 0DII]` attribute is placed here.  The two statements above are the tag's own
statement granted `ChartPseudoCoherenceDictionaryFrom`, and that hypothesis is not discharged in
this development; the two registrations of the tag in `RelativeAbsolute.lean` keep their clause
strings, and the bare attribute still belongs on the unconditional site-level statement, which is
one application of the theorems below away from the dictionary.

The dictionary is a hypothesis in each degree separately.  That is what the chain of comparisons
which would prove it delivers — see the display in the module documentation of
`RelativeAbsolute.lean`, items (i), (ii) and (iii) — and it is also what the all-degrees result
below needs: the quantifier swap that turns a family of degreewise statements into the single
complex that the all-degrees clause of Stacks 08FT (3) asks for happens on the *site* side, by
`AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom`, and not on the
chart side.

## How the assembly goes, and why it is one application

Both sides of Stacks 0DII are étale-local by construction, so the only thing between the
chartwise condition and the site-level one is a covering.

* In the direction which *builds* the site-level condition, the input is
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general` (Stacks 08FU, part (3)),
  whose hypothesis is the right-hand side of the dictionary quantified over a covering sieve of
  every object of the site.  The covering sieve to supply is
  `AlgebraicGeometry.Space.generate_affineChartDiagram_mem_topology` (Stacks 03G2): for any étale
  chart `U` of `X` the charts `Z ⟶ U` which are affine *and* are the chart of `X` of a commuting
  square over `f` whose chart of `Y` is affine generate a covering sieve of `U`.  Its free
  predicate on the chart of `Y` is taken to be the trivial one.  A member of that presieve
  carries both the affineness the dictionary needs and the square the chartwise hypothesis is
  indexed by, so the two meet with nothing in between; the square's commutation is the symmetric
  spelling of the one the definition of relative pseudo-coherence quantifies over, and the two
  differ by `Eq.symm` only.
* In the direction which *consumes* it, the input is
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction_general` (Stacks 08FU,
  part (3), in the restricting direction), which needs no covering at all: it restricts the single
  complex that pseudo-coherence of `E` already provides.

So neither direction is an induction, and neither needs the covering to be indexed by the affine
charts of `X` — which it is not, an affine chart of `X` not having to map into a single affine
chart of `Y`.

## Implementation notes

The chart is bound at the `AlgebraicGeometry.RingedSite.C` spelling throughout, because that is
the spelling at which `X.over U` and `Presieve U` are written, and the statements of
`RelativeAbsolute.lean` bind it at `AlgebraicGeometry.Space.SmallEtale`.  The two types are
definitionally equal — a projection of a structure literal — so a declaration stated at either
spelling applies at the other with no transport; what the spellings restrict is only what may be
*written*, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartTransportDerivedChartSections.lean` record.  Nothing
below writes `CategoryTheory.Over U`, so nothing below needs the other spelling.

Every typeclass hypothesis is discharged rather than carried.  The sheafification data of the
small étale ringed site of an algebraic space, of its slices and of the iterated slices of a
slice, and the two derived-category models, are the declarations of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean`,
`StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean` and
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`, whose declarations
are public and whose `instance` attribute is file-local; they are re-enabled here rather than
restated.  The one thing that has to be said again is the derived-category model at the
`(X.over U).ringSheaf` spelling of the localized sheaf of rings: it is the same category as at
the `X.ringSheaf.over U` spelling, by `rfl`, and instance search does not cross between the two.

The two ambient-universe instances answering `Abelian` and `IsGrothendieckAbelian` for sheaves of
modules are removed for this file for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean`: they fix the module
universe to the join of the universes of the site and of the rings, and a search reaching one of
them first ends in a universe constraint with no solution rather than in a recoverable failure.

## References

* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 0CSY](https://stacks.math.columbia.edu/tag/0CSY)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

-- The sheafification data of the small étale ringed site of an algebraic space, of its slices
-- and of the iterated slices of a slice, together with the two standard derived-category models;
-- all of them in the library, their declarations public and their `instance` attribute file-local, so
-- they are re-enabled here rather than restated.
attribute [local instance] smallEtaleRingedSite_essentiallySmall
  hasSheafifyAddCommGrp_smallEtaleRingedSite
  wEqualsLocallyBijectiveAddCommGrp_smallEtaleRingedSite
  hasRightDerivedFunctor_chartSections
  isGrothendieckAbelian_modules
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.iterHasSheafify RingedSite.iterWEq RingedSite.iterHasSheafifyAll
  RingedSite.iterWEqAll
  hasDerivedCategory_modules hasDerivedCategory_modules_over
  hasDerivedCategory_sections
  hasDerivedCategoryStandard_chartModules
  hasDerivedCategoryStandard_representedSchemeModules
  hasDerivedCategoryStandard_representedSchemeSections
  additive_chartSliceReindex isEquivalence_chartSliceReindex
  preservesFiniteLimits_chartSliceReindex preservesFiniteColimits_chartSliceReindex
  additive_chartSchemeSections additive_chartTransportSections
  additive_chartSectionsCrossed
  hasSheafify_chartLocalization wEqualsLocallyBijective_chartLocalization
  hasSheafify_over_chartLocalization wEqualsLocallyBijective_over_chartLocalization
  hasWeakSheafify_over_chartLocalization
  abelian_chartLocalizationModules abelian_chartModules
  additive_chartLocalizationReindex additive_representedSchemeReindex

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The standard derived category of the `𝒪_X|_U`-modules on the localization of the small étale
ringed site of `X` at a chart, at the `AlgebraicGeometry.RingedSite.ringSheaf` spelling of the
localized sheaf of rings.

It is the same category as at the `X.ringSheaf.over U` spelling, by `rfl`, and instance search
does not cross between the two; `AlgebraicGeometry.Space.hasDerivedCategory_modules_over` is the
model at that other spelling. -/
local instance hasDerivedCategory_over_ringSheaf
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)) :=
  inferInstanceAs (HasDerivedCategory.{u + 1}
    (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over U)))

/-! ### The dictionary at one affine chart -/

/-- **The derived-sections dictionary at an affine étale chart, in a fixed degree.**  For an
object `E` of `D_QCoh(𝒪_X)` and an integer `m`, this says that at every *affine* étale scheme
chart `U` of `X` the complex `RΓ(U, E)` of `𝒪_X(U)`-modules is `m`-pseudo-coherent exactly when
the restriction of `E` to the localization `X_étale/U` is `m`-pseudo-coherent there.

This is item (iii) of the display in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsolute.lean`, and it is
the one remaining input of the site-level form of Stacks 0DII; the theorems below take it as a
hypothesis and the development does not discharge it. -/
def ChartPseudoCoherenceDictionaryFrom
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ) : Prop :=
  ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C, IsAffine (chartScheme U) →
    (@StacksDraft.PseudoCoherence.IsPseudoCoherentFrom _ _ (_)
        (chartDerivedSections B S hS X.1 X.2 U E) m ↔
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).IsPseudoCoherentFrom
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
            U).mapDerivedCategory.obj E.obj) m)

/-! ### The assembly over the covering sieve of affine chart diagrams -/

/-- **The assembly of Stacks 0DII over the covering sieve of affine chart diagrams.**  Let
`f : X ⟶ Y` be a morphism of algebraic spaces, let `E` be an object of `D_QCoh(𝒪_X)` and let `m`
be an integer.  Granted the dictionary at the affine charts, if the complex `RΓ(U, E)` of
`𝒪_X(U)`-modules is `m`-pseudo-coherent on every commuting square of affine étale scheme charts
over `f`, then `E` is `m`-pseudo-coherent on the small étale ringed site of `X`.

This is `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general` — Stacks 08FU,
part (3) — at the covering sieve of Stacks 03G2,
`AlgebraicGeometry.Space.generate_affineChartDiagram_mem_topology`, whose free predicate on the
chart of `Y` is taken to be the trivial one.  A member of that presieve carries the affineness
the dictionary needs together with the square the hypothesis is indexed by, and the square's
commutation is the hypothesis' one read backwards. -/
theorem isPseudoCoherentFrom_of_forall_affineChart (f : X ⟶ Y)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ)
    (hdict : ChartPseudoCoherenceDictionaryFrom B S hS E m)
    (h : ∀ (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
        (g : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V),
        yoneda.map g ≫ V.obj.hom = U.obj.hom ≫ f.hom →
        IsAffine (chartScheme U) → IsAffine (chartScheme V) →
      @StacksDraft.PseudoCoherence.IsPseudoCoherentFrom _ _ (_)
        (chartDerivedSections B S hS X.1 X.2 U E) m) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E.obj m :=
  RingedSite.isPseudoCoherentFrom_of_locally_general
    (smallEtaleRingedSite B S hS X.1 X.2) E.obj m fun U =>
      ⟨_, generate_affineChartDiagram_mem_topology B S hS f (fun _ => True)
        (fun _ _ => trivial) U, by
          rintro Z g ⟨haff, d, rfl, haffV, -⟩
          exact (hdict _ haff).1 (h _ _ d.g d.comm.symm haff haffV)⟩

/-- **The dictionary is a statement about the derived chart transport.**  Granted that, at every
affine étale scheme chart `U` of `X`, `m`-pseudo-coherence of the derived chart transport of `E`
at the whole of the chart's scheme is `m`-pseudo-coherence of the restriction of `E` to
`X_étale/U`, the dictionary `AlgebraicGeometry.Space.ChartPseudoCoherenceDictionaryFrom` holds.

This is `AlgebraicGeometry.Space.isPseudoCoherentFrom_chartDerivedSections_iff_chartTransportTop`
composed with the hypothesis: the only difference between the two statements is the restriction of
scalars along the isomorphism of rings of sections induced by
`AlgebraicGeometry.Space.openChartOfComparisonTopIso`, and that is absorbed there.

The hypothesis is what is left of Stacks 0DII in this development.  Its left-hand side is derived
sections at the final object of the small étale site of the chart's *scheme*, so — after
`AlgebraicGeometry.Space.isPseudoCoherentFrom_chartSchemeReindex_iff` has carried its right-hand
side to that same site — it mentions no chart and no algebraic space: it is Stacks 08HE followed
by `AlgebraicGeometry.Scheme.isPseudoCoherent_zariskiRingedSite_iff` and Stacks 08E7 on one
affine scheme, with Stacks 071Q supplying the object on the Zariski side.  See "1. The
derived-sections dictionary at an affine chart" in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsolute.lean`. -/
theorem chartPseudoCoherenceDictionaryFrom_of_chartTransport
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ)
    (h : ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C, IsAffine (chartScheme U) →
      (StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
          ((chartTransportDerived B S hS X U (chartSchemeTopObject B S hS X U)).obj E.obj) m ↔
        ((smallEtaleRingedSite B S hS X.1 X.2).over U).IsPseudoCoherentFrom
          ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
              U).mapDerivedCategory.obj E.obj) m)) :
    ChartPseudoCoherenceDictionaryFrom B S hS E m := fun U hU =>
  (isPseudoCoherentFrom_chartDerivedSections_iff_chartTransportTop B S hS X U E m).trans (h U hU)

/-! ### The site-level form of Stacks 0DII, granted the dictionary -/

/-- **The site-level form of Stacks 0DII in a fixed degree, granted the dictionary at the affine
charts.**  Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over `S` which is locally of
finite presentation, let `E` be an object of `D_QCoh(𝒪_X)` and let `m` be an integer.  Then `E`
is `m`-pseudo-coherent relative to `Y` if and only if `E` is `m`-pseudo-coherent on the small
étale ringed site of `X`.

The relative condition is the chartwise one by
`AlgebraicGeometry.Space.isRelativelyPseudoCoherentFrom_iff_forall_chart`, which is Stacks 0DHQ
on each square of affine charts; the chartwise condition is the site-level one by
`AlgebraicGeometry.Space.isPseudoCoherentFrom_of_forall_affineChart` in one direction and by
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction_general` in the other. -/
theorem isRelativelyPseudoCoherentFrom_iff_isPseudoCoherentFrom_of_chartDictionary
    (f : X ⟶ Y) (hflat : IsFlat B S hS f.hom)
    (hfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ)
    (hdict : ChartPseudoCoherenceDictionaryFrom B S hS E m) :
    IsRelativelyPseudoCoherentFrom B S hS X.1 X.2 f.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp) E m ↔
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E.obj m :=
  (isRelativelyPseudoCoherentFrom_iff_forall_chart B S hS X.1 X.2 f.hom hflat hfp E m).trans
    ⟨isPseudoCoherentFrom_of_forall_affineChart B S hS f E m hdict,
      fun h U _V _g _hc hU _hV => (hdict U hU).2
        (RingedSite.isPseudoCoherentFrom_derivedRestriction_general
          (smallEtaleRingedSite B S hS X.1 X.2) E.obj m h U)⟩

/-- **The site-level form of Stacks 0DII, granted the dictionary at the affine charts in every
degree.**  Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over `S` which is locally of
finite presentation and let `E` be an object of `D_QCoh(𝒪_X)`.  Then `E` is pseudo-coherent
relative to `Y` if and only if `E` is pseudo-coherent on the small étale ringed site of `X`.
This is the shape of the source statement.

It is not the fixed-degree statement read degree by degree: the all-degrees clause of Stacks
08FT (3) asks for **one** complex which is `m`-pseudo-coherent for every `m`, so the site-level
side is an `∃ K, ∀ m, …` while the fixed-degree statements give only `∀ m, ∃ K, …`.  The swap is
the forward direction of Stacks 08FU (2),
`AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom`, applied on the
site side; the relative side is the conjunction over all degrees by definition, which is
`AlgebraicGeometry.Space.isRelativelyPseudoCoherent_iff_forall`. -/
theorem isRelativelyPseudoCoherent_iff_isPseudoCoherent_of_chartDictionary
    (f : X ⟶ Y) (hflat : IsFlat B S hS f.hom)
    (hfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hdict : ∀ m : ℤ, ChartPseudoCoherenceDictionaryFrom B S hS E m) :
    IsRelativelyPseudoCoherent B S hS X.1 X.2 f.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp) E ↔
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E.obj :=
  (isRelativelyPseudoCoherent_iff_forall B S hS X.1 X.2 f.hom _ E).trans
    ((forall_congr' fun m =>
        isRelativelyPseudoCoherentFrom_iff_isPseudoCoherentFrom_of_chartDictionary
          B S hS f hflat hfp E m (hdict m)).trans
      (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom
        (smallEtaleRingedSite B S hS X.1 X.2) E.obj).symm)

end AlgebraicGeometry.Space

end
