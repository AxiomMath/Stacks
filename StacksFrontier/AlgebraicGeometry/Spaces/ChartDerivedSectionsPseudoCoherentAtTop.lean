module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsTransportAtTop
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings

/-!
# `RΓ(U, E)` is pseudo-coherent exactly when the derived chart transport is

Let `X` be an algebraic space over a scheme `S`, let `U` be an étale scheme chart of `X` and let
`E` be an object of `D_QCoh(𝒪_X)`.
`StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsTransportAtTop.lean` identifies the
complex `RΓ(U, E)` of `𝒪_X(U)`-modules with the derived chart transport of `E` at the whole of
the chart's scheme, *read over `𝒪_X(U)` along the isomorphism of rings of sections* that the
comparison of charts induces; that restriction of scalars is not removable, the two rings being
isomorphic and not equal.

This file absorbs it on the `Prop` side: pseudo-coherence of `RΓ(U, E)` over `𝒪_X(U)` is
pseudo-coherence of the derived chart transport over the ring of sections of `𝒪` at the object of
the small étale site of the chart's scheme that the transport is taken at.  Both clauses of
Stacks 064Q are covered — the fixed-degree one and the all-degrees one.

## Main results

* `AlgebraicGeometry.Space.bijective_structureSheafMap_of_iso`: the restriction map of `𝒪_X`
  along an isomorphism of étale charts is a bijection of rings.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_derivedChartSections_iff_chartTransportDerived`
  and `AlgebraicGeometry.Space.isPseudoCoherent_derivedChartSections_iff_chartTransportDerived`:
  the absorption at an arbitrary object `Z` of the small étale site of the chart's scheme and an
  arbitrary isomorphism between the chart the comparisons attach to `Z` and `U`.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_chartDerivedSections_iff_chartTransportTop` and
  `AlgebraicGeometry.Space.isPseudoCoherent_chartDerivedSections_iff_chartTransportTop`: the same
  at `Z = ⊤` and stated through `AlgebraicGeometry.Space.chartDerivedSections`, which is the
  complex both sides of Stacks 0DII are about.

## How the restriction of scalars is absorbed, and what it costs

The ring map to be absorbed is `(𝒪_X.ringSheaf.obj.map e.hom.op).hom` for an isomorphism
`e : V ≅ U` of étale charts, and it is an isomorphism of rings.  The transport of
pseudo-coherence along an isomorphism of coefficient rings is proved in both clauses at once, in
every universe, as `StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv`; what it wants
is a `RingEquiv`, and the one to hand it is `RingEquiv.ofBijective` of the ring map itself, whose
`RingEquiv.toRingHom` is that map with no unification to do.

Reaching the `RingEquiv` as `CategoryTheory.Iso.ringCatIsoToRingEquiv` of
`CategoryTheory.asIso` of that map exceeds 200,000 heartbeats at `whnf`.  Through
`RingEquiv.ofBijective` the whole of this file checks in under a second at the default heartbeat
ceiling, which nothing here raises: the bijectivity is
`CategoryTheory.ConcreteCategory.bijective_of_isIso`, and the `IsIso` it needs is supplied as
`CategoryTheory.Iso.isIso_hom` of `𝒪_X.ringSheaf.obj.mapIso (CategoryTheory.Iso.op e)` rather
than by instance search — search reaching `CategoryTheory.Functor.map_isIso` instead re-derives
`IsIso e.hom.op` at a `CategoryTheory.Category` instance for the chart's type which is not the
one carried, and fails.

## References

* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
* [Stacks Project, Tag 064T](https://stacks.math.columbia.edu/tag/064T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

-- The data of the small étale ringed site of an algebraic space, of its slices, and the
-- derived-category models of the chart transport, all declared with their `instance` attribute
-- file-local; they are re-enabled here rather than restated, exactly as
-- `StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsTransportAtTop.lean` does.
attribute [local instance] smallEtaleRingedSite_essentiallySmall
  hasSheafifyAddCommGrp_smallEtaleRingedSite
  wEqualsLocallyBijectiveAddCommGrp_smallEtaleRingedSite
  hasRightDerivedFunctor_chartSections
  isGrothendieckAbelian_modules
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
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
  abelian_chartLocalizationModules abelian_chartModules
  additive_chartLocalizationReindex additive_representedSchemeReindex
  hasDerivedCategoryStandard_spaceChartSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)

/-- **The restriction map of `𝒪_X` along an isomorphism of étale charts is a bijection.**  For an
isomorphism `e : U' ≅ U` of étale scheme charts of `X`, the induced map
`𝒪_X(U) ⟶ 𝒪_X(U')` of rings of sections is bijective.

The `CategoryTheory.IsIso` it is read off is supplied as `CategoryTheory.Iso.isIso_hom` of the
image of `CategoryTheory.Iso.op e` under the structure sheaf rather than by instance search; see
"How the restriction of scalars is absorbed" in the module documentation. -/
theorem bijective_structureSheafMap_of_iso {U' : SmallEtale B S hS X.1} (e : U' ≅ U) :
    Function.Bijective
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map e.hom.op).hom) := by
  have : IsIso ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map e.hom.op) :=
    Iso.isIso_hom ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.mapIso (Iso.op e))
  exact ConcreteCategory.bijective_of_isIso _

/-- **Derived sections over an étale chart are `m`-pseudo-coherent exactly when the derived chart
transport is.**  Let `Z` be an object of the small étale site of the chart's scheme and let `e` be
an isomorphism between the étale chart that the comparisons of Stacks 04M0 and Stacks 03ED attach
to `Z` and `U` itself.  Then for an object `E` of `D_QCoh(𝒪_X)` the complex of `𝒪_X(U)`-modules
`RΓ(U, E)` is `m`-pseudo-coherent if and only if the derived chart transport of `E` at `Z` is
`m`-pseudo-coherent over the ring of sections of `𝒪` at `Z`.

This is `AlgebraicGeometry.Space.derivedChartSectionsTransportAppIso` with its restriction of
scalars absorbed by `StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv` at
`RingEquiv.ofBijective` of `AlgebraicGeometry.Space.bijective_structureSheafMap_of_iso`. -/
theorem isPseudoCoherentFrom_derivedChartSections_iff_chartTransportDerived
    (Z : (representedSchemeRingedSite B S hS ((SmallEtale.toOver B S hS X.1).obj U)).C)
    (e : chartOfComparison B S hS X U Z ≅ U)
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
    (m : ℤ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((Stacks.Cohomology.HypercohomologyEdge.derivedSections
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
            U).obj E) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((chartTransportDerived B S hS X U Z).obj E) m :=
  Iff.trans
    ⟨fun hk => StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso hk
        (derivedChartSectionsTransportAppIso B S hS X U Z e E),
      fun hk => StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso hk
        (derivedChartSectionsTransportAppIso B S hS X U Z e E).symm⟩
    ((@StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv.{u, u, u} _ _ _ _ (_) (_)
      (RingEquiv.ofBijective _ (bijective_structureSheafMap_of_iso B S hS X U e))
      ((chartTransportDerived B S hS X U Z).obj E)).1 m).symm

/-- **The all-degrees companion of
`AlgebraicGeometry.Space.isPseudoCoherentFrom_derivedChartSections_iff_chartTransportDerived`.**
`RΓ(U, E)` is pseudo-coherent over `𝒪_X(U)` if and only if the derived chart transport of `E` at
`Z` is pseudo-coherent over the ring of sections of `𝒪` at `Z`.

It is not the fixed-degree statement read degree by degree: pseudo-coherence of Stacks 064Q (2)
asks for **one** bounded-above complex of finite free modules, and
`StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv` supplies that clause itself, beside
the fixed-degree one. -/
theorem isPseudoCoherent_derivedChartSections_iff_chartTransportDerived
    (Z : (representedSchemeRingedSite B S hS ((SmallEtale.toOver B S hS X.1).obj U)).C)
    (e : chartOfComparison B S hS X U Z ≅ U)
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((Stacks.Cohomology.HypercohomologyEdge.derivedSections
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
            U).obj E) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((chartTransportDerived B S hS X U Z).obj E) :=
  Iff.trans
    ⟨fun hk => StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso hk
        (derivedChartSectionsTransportAppIso B S hS X U Z e E),
      fun hk => StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso hk
        (derivedChartSectionsTransportAppIso B S hS X U Z e E).symm⟩
    ((@StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv.{u, u, u} _ _ _ _ (_) (_)
      (RingEquiv.ofBijective _ (bijective_structureSheafMap_of_iso B S hS X U e))
      ((chartTransportDerived B S hS X U Z).obj E)).2).symm

/-- **`RΓ(U, E)` is `m`-pseudo-coherent exactly when the derived chart transport at the whole of
the chart's scheme is.**  Stated through `AlgebraicGeometry.Space.chartDerivedSections`, which is
the complex of `𝒪_X(U)`-modules that both sides of Stacks 0DII are about.

This is `AlgebraicGeometry.Space`
`.isPseudoCoherentFrom_derivedChartSections_iff_chartTransportDerived`
at `Z = AlgebraicGeometry.Space.chartSchemeTopObject` and at
`AlgebraicGeometry.Space.openChartOfComparisonTopIso`, applied and not re-elaborated. -/
theorem isPseudoCoherentFrom_chartDerivedSections_iff_chartTransportTop
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ) :
    @StacksDraft.PseudoCoherence.IsPseudoCoherentFrom _ _ (_)
        (chartDerivedSections B S hS X.1 X.2 U E) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((chartTransportDerived B S hS X U (chartSchemeTopObject B S hS X U)).obj E.obj) m :=
  isPseudoCoherentFrom_derivedChartSections_iff_chartTransportDerived B S hS X U
    (chartSchemeTopObject B S hS X U) (openChartOfComparisonTopIso B S hS X U) E.obj m

/-- **The all-degrees companion of
`AlgebraicGeometry.Space.isPseudoCoherentFrom_chartDerivedSections_iff_chartTransportTop`.** -/
theorem isPseudoCoherent_chartDerivedSections_iff_chartTransportTop
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    @StacksDraft.PseudoCoherence.IsPseudoCoherent _ _ (_)
        (chartDerivedSections B S hS X.1 X.2 U E) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((chartTransportDerived B S hS X U (chartSchemeTopObject B S hS X U)).obj E.obj) :=
  isPseudoCoherent_derivedChartSections_iff_chartTransportDerived B S hS X U
    (chartSchemeTopObject B S hS X U) (openChartOfComparisonTopIso B S hS X U) E.obj

end AlgebraicGeometry.Space

end
