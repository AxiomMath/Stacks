module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSmallEtaleTopSectionsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeAbsoluteSiteAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent

/-!
# Stacks 0DII: relative and absolute pseudo-coherence on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is flat and locally of
finite presentation, and let `E` be an object of `D_QCoh(𝒪_X)`.  Then `E` is pseudo-coherent
relative to `Y` if and only if `E` is pseudo-coherent on the small étale ringed site of `X`.

`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsoluteSiteAssembly.lean`
proves this granted one hypothesis, `AlgebraicGeometry.Space.ChartPseudoCoherenceDictionaryFrom`,
and reduces that hypothesis — by
`AlgebraicGeometry.Space.chartPseudoCoherenceDictionaryFrom_of_chartTransport` — to a statement
about the derived chart transport at the whole of an affine chart's scheme.  This file discharges
that statement and registers the tag.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_chartLocalizationReindex_iff` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSchemeReindex_iff`: quasi-coherence of
  a module crosses each of the two chart comparisons, in both directions.  Each is
  `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` — Stacks 03DM for clause (6) of
  Stacks 03DL — at the comparison in question.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_chartSchemeTransport`: the same at the
  derived level and along the whole transport, restriction to the slice included: the cohomology
  sheaves of the object the small étale site of an affine chart's scheme carries are quasi-coherent
  as soon as those of `E` are.
* `AlgebraicGeometry.Space.derivedChartSliceIsoTotalRightDerived`: restriction to the slice at a
  chart, read on derived categories, is its own unbounded right derived functor.
* `AlgebraicGeometry.Space.chartPseudoCoherenceDictionaryFrom_holds`: **the dictionary**, with no
  hypothesis left.
* `AlgebraicGeometry.Space.isRelativelyPseudoCoherentFrom_iff_isPseudoCoherentFrom`: Stacks 0DII in
  a fixed degree.
* `AlgebraicGeometry.Space.isRelativelyPseudoCoherent_iff_isPseudoCoherent`: **Stacks 0DII.**

## How the dictionary is discharged

What `chartPseudoCoherenceDictionaryFrom_of_chartTransport` leaves is, at an affine étale scheme
chart `U` of `X`, that `m`-pseudo-coherence of the derived chart transport of `E` at the whole of
the chart's scheme is `m`-pseudo-coherence of the restriction of `E` to the localization
`X_étale/U`.  Three things stand between that and what is proved.

* **The right-hand side crosses to the chart's scheme.**  This is
  `AlgebraicGeometry.Space.isPseudoCoherentFrom_chartSchemeReindex_iff`, which carries
  pseudo-coherence on `X_étale/U` to pseudo-coherence on the small étale site of the chart's scheme
  along the reindexings of Stacks 04M0 and of the comparison of a representable algebraic space
  with its scheme.  Proved, and a biconditional.
* **The left-hand side is derived sections at the final object of that site.**  So the comparison
  needed on the scheme is
  `AlgebraicGeometry.isPseudoCoherentFrom_derivedSectionsOverTop_iff`, which is where the
  mathematics of this step sits: Stacks 08HE, Stacks 08E7, Stacks 09VA and the module-valued clause
  of Stacks 0D6H at `ε` composed, with Stacks 071Q supplying the object on the Zariski side.  It
  asks for quasi-coherence of the object the chart's scheme carries, and nothing else;
  `AlgebraicGeometry.Space.representedSchemeRingedSite` is a reducible abbreviation for the small
  étale ringed site of the chart's scheme, so it applies at the chart with no transport.
* **The two sides restrict `E` to the slice by different functors.**  The dictionary's right-hand
  side uses `CategoryTheory.Functor.mapDerivedCategory` of
  `SheafOfModules.overFunctor`; the derived chart transport begins with that functor's *unbounded
  right derived functor*.  Restriction to a slice is exact, so the two agree, by
  `Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived` — which despite its namespace is
  a statement about an arbitrary exact functor between abelian categories, proved by uniqueness of
  right derived functors.  The comparison is then pushed along the two reindexings and through
  derived sections, and absorbed by
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_iso`.

The quasi-coherence hypothesis is the one thing the chain needs which is not already in the shape
`RelativeAbsoluteSiteAssembly.lean` hands over.  It is carried along the three functors one at a
time, each step being the module-level statement for that functor read through
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`: the cohomology sheaves of the image are the
images of the cohomology sheaves, all three functors being exact.  For restriction to the slice the
module-level statement is `Stacks.SheafOfModules.isQuasicoherent_over`, and for the two
reindexings it is the first two results above.

## Implementation notes

The chart is bound at two spellings, in two sections which meet by application and never inside one
statement.  `AlgebraicGeometry.Space.isQuasicoherentOnSite_chartLocalizationReindex_iff` has to be
stated with `U : AlgebraicGeometry.Space.SmallEtale B S hS X.1`: its proof passes the slice
topology `(AlgebraicGeometry.Space.SmallEtale.topology B S hS X.1).over U` explicitly, which needs
`CategoryTheory.Category (CategoryTheory.Over U)` *synthesized*, and at the
`(smallEtaleRingedSite B S hS X.1 X.2).C` spelling of the chart that instance is not found —
the error is `failed to synthesize Category.{u, u + 1} (Over U)`.  Everything downstream is stated
at the `(smallEtaleRingedSite B S hS X.1 X.2).C` spelling, which is the one the dictionary uses,
and applies that result at the other with no transport: the two types are definitionally equal.

Everything is stated on objects rather than on functors.  The chart transport is left spelled as
the composite it is defined to be, and the comparison with it is built by `mapIso` of the inner
crossing rather than asserted head-on.

The derived-category model of the `𝒪_X|_U`-modules on the slice at the chart is the `local
instance` of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeAbsoluteSiteAssembly`,
re-enabled here rather than restated: its declaration is public and its `instance` attribute is
file-local, and restating it collides with it by name.

The derived-category model of the modules on the chart's scheme is needed at two spellings — the
`AlgebraicGeometry.RingedSite.ringSheaf` one and the
`AlgebraicGeometry.SmallEtale.structureSheaf` one that `AlgebraicGeometry.SmallEtale.qcohOnSite`
is stated at — and instance search does not cross between them, so the second is supplied here from
the first.  The two ambient-universe instances answering `CategoryTheory.Abelian` and
`CategoryTheory.IsGrothendieckAbelian` for sheaves of modules are removed for this file, for the
reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean`: the site-level
pseudo-coherence expression does not elaborate with them in scope, the search ending in
`stuck at solving universe constraint u + 1 =?= max (u + 1) ?u`.

## References

* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-coherence across the two chart comparisons -/

section Reindex

variable (X : AlgebraicSpaces B S hS)

/-- **Quasi-coherence crosses the comparison of Stacks 04M0, in both directions.**  An
`𝒪_X|_U`-module on the localization of the small étale site of `X` at an étale scheme chart `U` is
quasi-coherent there exactly when its reindexing along the comparison of Stacks 04M0 is
quasi-coherent on the small étale site of the algebraic space represented by `U`.

This is `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` — Stacks 03DM for clause (6) of
Stacks 03DL — at the equivalence of sites of Stacks 04M0, the reindexing being
`SheafOfModules.pushforward` of the identity structure map by construction.  The chart is bound at
the `AlgebraicGeometry.Space.SmallEtale` spelling; see the implementation notes. -/
public theorem isQuasicoherentOnSite_chartLocalizationReindex_iff (U : SmallEtale B S hS X.1)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)) :
    ((chartLocalizationReindex B S hS X U).obj M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  @Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff _ _ _ _
    ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U)
    M

end Reindex

/-- **Quasi-coherence crosses the comparison of a representable algebraic space with its scheme, in
both directions.**  An `𝒪`-module on the small étale site of the algebraic space represented by an
object `V` of the big fppf site over `S` is quasi-coherent exactly when its reindexing is
quasi-coherent on the small étale site of the scheme underlying `V`.

This is `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` at the *symmetric* orientation of
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`: the reindexing is the inverse of
`AlgebraicGeometry.Space.representedSchemeModulesEquivalence`, and both structure maps of that
equivalence are the identity, so the inverse is `SheafOfModules.pushforward` of the identity for
the symmetric orientation. -/
public theorem isQuasicoherentOnSite_representedSchemeReindex_iff (V : BigFppfOver B S hS)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (representedRingedSite B S hS V).O)) :
    ((representedSchemeReindex B S hS V).obj N).IsQuasicoherentOnSite ↔
      N.IsQuasicoherentOnSite :=
  @Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff _ _ _ _
    (SmallEtale.topology B S hS (yoneda.obj V))
    (representedSchemeSmallEtaleTopology B S hS V)
    (representedSmallEtaleEquivalence B S hS V).symm
    (isContinuous_representedSmallEtaleInverse_ringedSite B S hS V)
    (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O)
    (isDenseSubsite_representedSmallEtaleEquivalence_functor B S hS V)
    N

/-! ### The dictionary, and Stacks 0DII -/

section Dictionary

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
  abelian_representedModules abelian_representedSchemeModules
  additive_chartLocalizationReindex additive_representedSchemeReindex
  hasDerivedCategory_over_ringSheaf

variable {X Y : AlgebraicSpaces B S hS}

/-- The standard derived category of the modules on the small étale site of a chart's scheme, at
the `AlgebraicGeometry.SmallEtale.structureSheaf` spelling that
`AlgebraicGeometry.SmallEtale.qcohOnSite` is stated at; it is the same category as at the
`AlgebraicGeometry.RingedSite.ringSheaf` spelling, and instance search does not cross between the
two. -/
local instance hasDerivedCategoryStandard_chartSchemeStructureSheaf (X : AlgebraicSpaces B S hS)
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (SmallEtale.structureSheaf (associatedBigEtaleSite B) (chartScheme U)
        ((SmallEtale.toOver B S hS X.1).obj U).left.property)) :=
  inferInstanceAs (HasDerivedCategory.{u + 1} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (representedSchemeRingedSite B S hS ((SmallEtale.toOver B S hS X.1).obj U)).O)))

/-- **Quasi-coherence survives the whole chart transport, at the derived level.**  If every
cohomology sheaf of an object `E` of the derived category of `𝒪_X`-modules is quasi-coherent, then
so is every cohomology sheaf of the object which the small étale site of a chart's scheme carries:
the restriction of `E` to the slice at the chart, reindexed along the comparison of Stacks 04M0 and
then along the comparison of the represented algebraic space with its scheme.

Each of the three functors is exact, so its effect on a cohomology sheaf of `E` is
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, and quasi-coherence of the image of a
quasi-coherent module is `Stacks.SheafOfModules.isQuasicoherent_over` for the first and the two
results above for the other two. -/
public theorem isQuasicoherentOnSite_homology_chartSchemeTransport
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) n).obj
        E).IsQuasicoherentOnSite)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite
        B S hS ((SmallEtale.toOver B S hS X.1).obj U)).O)) n).obj
      ((representedSchemeReindex B S hS
          ((SmallEtale.toOver B S hS X.1).obj U)).mapDerivedCategory.obj
        ((chartSliceReindex B S hS X U).mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
              U).mapDerivedCategory.obj
              E)))).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((Functor.mapDerivedCategoryHomologyIso (representedSchemeReindex B S hS
        ((SmallEtale.toOver B S hS X.1).obj U)) n).app _).symm
    ((isQuasicoherentOnSite_representedSchemeReindex_iff B S hS
          ((SmallEtale.toOver B S hS X.1).obj U) _).2
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
          ((Functor.mapDerivedCategoryHomologyIso (chartSliceReindex B S hS X U) n).app _).symm
        ((isQuasicoherentOnSite_chartLocalizationReindex_iff B S hS X U _).2
          (SheafOfModules.IsQuasicoherentOnSite.of_iso
              ((Functor.mapDerivedCategoryHomologyIso (SheafOfModules.overFunctor.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
                  U) n).app E).symm
            (Stacks.SheafOfModules.isQuasicoherent_over _ (hE n) U)))))

/-- **Restriction to the slice at a chart is its own unbounded right derived functor.**
`SheafOfModules.overFunctor` is exact, so the functor it induces on derived categories is
canonically its total right derived functor; this is
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`, read at one object.

The two sides are what the dictionary and the derived chart transport respectively begin with. -/
public def derivedChartSliceIsoTotalRightDerived (X : AlgebraicSpaces B S hS)
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :
    (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
            U).mapDerivedCategory.obj E ≅
      (Stacks.DerivedFunctor.totalRightDerived (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          U)).obj E :=
  (Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U)).app E

/-- **The derived-sections dictionary at an affine étale chart, in a fixed degree.**  For an object
`E` of `D_QCoh(𝒪_X)` and an integer `m`, at every affine étale scheme chart `U` of `X` the complex
`RΓ(U, E)` of `𝒪_X(U)`-modules is `m`-pseudo-coherent exactly when the restriction of `E` to the
localization `X_étale/U` is `m`-pseudo-coherent there.

This discharges the one hypothesis of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeAbsoluteSiteAssembly`.
See "How the dictionary is discharged" in the module documentation. -/
public theorem chartPseudoCoherenceDictionaryFrom_holds
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ) :
    ChartPseudoCoherenceDictionaryFrom B S hS E m := by
  refine chartPseudoCoherenceDictionaryFrom_of_chartTransport B S hS E m fun U hU => ?_
  have hc := (Stacks.DerivedFunctor.totalRightDerived
      (SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS
          ((SmallEtale.toOver B S hS X.1).obj U)).O)
        (op (chartSchemeTopObject B S hS X U)))).mapIso
    ((representedSchemeReindex B S hS
        ((SmallEtale.toOver B S hS X.1).obj U)).mapDerivedCategory.mapIso
      ((chartSliceReindex B S hS X U).mapDerivedCategory.mapIso
        (derivedChartSliceIsoTotalRightDerived B S hS X U E.obj)))
  refine Iff.trans ?_
    ((isPseudoCoherentFrom_derivedSectionsOverTop_iff (associatedBigEtaleSite B) (chartScheme U)
        ((SmallEtale.toOver B S hS X.1).obj U).left.property _
        (isQuasicoherentOnSite_homology_chartSchemeTransport B S hS U E.obj E.property) m).trans
      (isPseudoCoherentFrom_chartSchemeReindex_iff B S hS X U _ m))
  exact ⟨fun h => StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso h hc.symm,
    fun h => StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso h hc⟩

/-- **Stacks 0DII in a fixed degree.**  Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over
a scheme `S` which is locally of finite presentation, let `E` be an object of `D_QCoh(𝒪_X)` and let
`m` be an integer.  Then `E` is `m`-pseudo-coherent relative to `Y` if and only if `E` is
`m`-pseudo-coherent on the small étale ringed site of `X`. -/
public theorem isRelativelyPseudoCoherentFrom_iff_isPseudoCoherentFrom (f : X ⟶ Y)
    (hflat : IsFlat B S hS f.hom) (hfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ) :
    IsRelativelyPseudoCoherentFrom B S hS X.1 X.2 f.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp) E m ↔
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E.obj m :=
  isRelativelyPseudoCoherentFrom_iff_isPseudoCoherentFrom_of_chartDictionary B S hS f hflat hfp E m
    (chartPseudoCoherenceDictionaryFrom_holds B S hS E m)

/-- Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
flat and locally of finite presentation.  Let `E` be an object of `D_QCoh(𝒪_X)`.  Then `E` is
pseudo-coherent relative to `Y` if and only if `E` is pseudo-coherent on `X`, the latter read on
the small étale ringed site of `X`.

This is
`AlgebraicGeometry.Space.isRelativelyPseudoCoherent_iff_isPseudoCoherent_of_chartDictionary` at
`AlgebraicGeometry.Space.chartPseudoCoherenceDictionaryFrom_holds` in every degree.  It is not the
fixed-degree statement above read degree by degree: the all-degrees clause of Stacks 08FT (3) asks
for one complex which is `m`-pseudo-coherent for every `m`, and the quantifier swap happens on the
site side, inside that theorem. -/
@[stacks 0DII]
public theorem isRelativelyPseudoCoherent_iff_isPseudoCoherent (f : X ⟶ Y)
    (hflat : IsFlat B S hS f.hom) (hfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    IsRelativelyPseudoCoherent B S hS X.1 X.2 f.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp) E ↔
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E.obj :=
  isRelativelyPseudoCoherent_iff_isPseudoCoherent_of_chartDictionary B S hS f hflat hfp E
    fun m => chartPseudoCoherenceDictionaryFrom_holds B S hS E m

end Dictionary

end AlgebraicGeometry.Space

end
