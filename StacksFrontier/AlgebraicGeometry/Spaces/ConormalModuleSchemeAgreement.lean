module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CartierConormal.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushSelfChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedChartZariskiIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# **Stacks 04G2, part (1)**: the conormal sheaf of an immersion of schemes

Let `j : R ⟶ V` be a morphism of the big fppf category over a scheme `S` whose underlying
morphism of schemes is a closed immersion.  Two conormal sheaves are attached to it.

* The **spaces** one.  `AlgebraicGeometry.Space.closedSubspaceRange` is the closed subspace
  which `j` cuts out of the algebraic space `yoneda.obj V`, and
  `AlgebraicGeometry.Space.conormalModule` of [Stacks Project, Tag 04CN] is its conormal module:
  a sheaf of modules on the small étale site of that subspace.
* The **schemes** one.  `Stacks.Conormal.conormalSheaf` of [Stacks Project, Tag 01R2] is the
  conormal sheaf of the underlying morphism of schemes: a sheaf of modules on the Zariski site
  of the scheme underlying `R`.

Part (1) of [Stacks Project, Tag 04G2] asserts that the two agree.  They are modules on
different sites, so the statement is that the first is what the second becomes on the small étale
site: the associated-module functor of [Stacks Project, Tag 03DU] (4) carries the schemes
conormal sheaf onto the small étale site of the scheme underlying `R`, and
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` reads that as a module on the
small étale site of `yoneda.obj R`.  The subspace which `j` cuts out and `yoneda.obj R` are
identified by `AlgebraicGeometry.Space.rangeSpaceIso`, `j` being a monomorphism, and the
comparison is stated across that identification.

## Main results

* `AlgebraicGeometry.Space.conormalModuleClosedSubspaceRangeIso`: **part (1) of [Stacks Project,
  Tag 04G2]** in the closed case — the conormal module of the closed subspace cut out by `j`,
  read on `yoneda.obj R`, is the associated module of the schemes conormal sheaf of the
  underlying morphism.
* `AlgebraicGeometry.Space.representedDefiningIdealPullbackConormalSheafIso`: the same comparison
  with the closed subspace eliminated from the statement — the inverse image along the represented
  morphism of the defining ideal sheaf of its range is the associated module of the schemes
  conormal sheaf.  This is the form the general immersion case reuses, applied to the
  factorisation of an immersion through its ambient open.

## Route

Everything used is already available, and the proof is the composition of five identifications.
Write
`𝓘` for the defining ideal sheaf of [Stacks Project, Tag 03MB] of the closed subspace, `i` for
the inclusion of that subspace and `e` for the identification `yoneda.obj R ≅` that subspace.

* `AlgebraicGeometry.Space.modulePullbackCompIso` of [Stacks Project, Tag 03LU] splits the
  inverse image along `e ≫ i`, which is the represented morphism by
  `AlgebraicGeometry.Space.rangeSpaceIso_hom_comp_subspaceInclusion`, into the inverse image
  along `i` — that is the conormal module, by definition — followed by the one along `e`.
* `AlgebraicGeometry.Space.representedAssociatedModuleChartZariskiIdealSheafIso` exhibits `𝓘`
  as the associated module of its Zariski restriction, `𝓘` being quasi-coherent on the site by
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf`.  This is the step the
  comparison turns on: it is the essential surjectivity of the associated-module functor of
  [Stacks Project, Tag 03DX] (2) at `τ = étale`, which this tree proves unconditionally.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` carries the inverse image
  along the represented morphism across, turning it into the Zariski pullback along the
  underlying morphism of schemes.  It assumes no quasi-coherence and no étaleness, which is what
  makes it applicable at a closed immersion.
* `AlgebraicGeometry.Space.chartZariskiIdealSheafSelfChartIsoIdealSheaf` identifies that Zariski
  restriction with `Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of schemes.
* `Stacks.CartierConormal.conormalSheafIsoPullbackSelf` is the schemes conormal sheaf as the
  pullback of that ideal sheaf along the morphism itself, rather than along
  `AlgebraicGeometry.Scheme.Hom.liftCoborder`, which is the shape the previous step produces.
  The two spellings of the pullback of modules on a scheme meet here and are the same functor on
  the nose, by `Stacks.ToposBridge.scheme_modules_pullback_eq`.

## Implementation notes

`AlgebraicGeometry.Space.modulePullback` and
`AlgebraicGeometry.Space.modulePullbackCompIso` are made locally irreducible, as they are in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleComposition.lean`: unfolding the inverse
image to its construction by sheafification, or the comparison to
`CategoryTheory.Adjunction.leftAdjointUniq`, does not terminate, and nothing below needs it.
Reducing `AlgebraicGeometry.Space.conormalModule` to the inverse image of the defining ideal
sheaf is a comparison of *objects* and is cheap.

The replacement of `e ≫ i` by the represented morphism is taken on the whole functor rather than
inside a component: `AlgebraicGeometry.Space.modulePullback` depends on the morphism only through
a `CategoryTheory.Functor`, whose source and target categories are the same for the two
spellings, so `congrArg` transports the equation and no dependent rewrite is needed.

## The general immersion case

What is proved in this file is the **closed** case.  The source states part (1) for an arbitrary
**immersion** of schemes, and that generality is proved — in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreementImmersion.lean`, as
`AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`, by applying
`AlgebraicGeometry.Space.representedDefiningIdealPullbackConormalSheafIso` over the ambient open
of [Stacks Project, Tag 04CE] and transporting back along [Stacks Project, Tag 04CO].  The
registration there is the one against the tag's own statement; this one is the closed case it
rests on.

The reason the general case cannot be made at `j` itself, which is a fact about the route and not
a missing lemma, is worth recording here.  Four of the five steps above are available at
immersion generality: `AlgebraicGeometry.Space.immersionConormalModule` is the conormal module
of an arbitrary immersion of algebraic spaces and
`AlgebraicGeometry.Space.conormalModuleOfImmersionKernelPullbackIso` presents it as the inverse
image of `AlgebraicGeometry.Space.kernelIdealSheaf` of the immersion itself;
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf` presents `Stacks.Conormal.conormalSheaf` as
the pullback of `Stacks.ClosedImmersion.idealSheaf` along the morphism itself for *any*
immersion; `AlgebraicGeometry.Space.chartZariskiKernelIdealSheafSelfChartIsoIdealSheaf` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedChartZariskiIdeal.lean` carries no hypothesis on
`j`, because `AlgebraicGeometry.Space.ker_structureSharp_eq` asks only for relative
representability; and `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` assumes
nothing either.

The remaining step is where the closedness is genuinely needed.
`AlgebraicGeometry.Space.representedAssociatedModuleChartZariskiIdealSheafIso` exhibits the ideal
sheaf as the associated module of its Zariski restriction only when the ideal sheaf is
**quasi-coherent on the site**; in the closed case that is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf`.  For
`AlgebraicGeometry.Space.kernelIdealSheaf` the tree has it only for a *quasi-compact* morphism,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernelIdealSheaf` of [Stacks Project, Tag 082Z]
(1), and that restriction is real rather than an artefact: the kernel is the ideal of the
scheme-theoretic image, whose quasi-coherence is what Morphisms, Lemma [Stacks Project, Tag 01R8]
derives from quasi-compactness.  Hence the general case is routed through the ambient open of
[Stacks Project, Tag 04CE], on which the kernel ideal sheaf *is* a defining ideal sheaf:
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedImmersionCoborderLift.lean` supplies that
ambient
as an object of the site, `AlgebraicGeometry.Space.immersionCoborderObj`, with the factorisation
`AlgebraicGeometry.Space.immersionCoborderLift` of `j` through it whose morphism of schemes is
`AlgebraicGeometry.Scheme.Hom.liftCoborder` on the nose
(`AlgebraicGeometry.Space.toScheme_map_immersionCoborderLift`) and hence a closed immersion
(`AlgebraicGeometry.Space.isClosedImmersion_toScheme_map_immersionCoborderLift`), and the
cartesian square with the identity along the top
(`AlgebraicGeometry.Space.isPullback_representedSpaceMap_immersionCoborderLift`) which Stacks 04CO
consumes.

## What is not proved

Part (2) of the tag — the agreement of the canonical map of [Stacks Project, Tag 04CP] with the
schemes map of [Stacks Project, Tag 01R4] — is not stated here and no attribute for it is
claimed.  It is the naturality of the comparison above in a square of represented closed
subspaces, and it reduces, but only to one further identification.

The reduction is the one `AlgebraicGeometry.Space.idealSheafMap_comp` uses.  Both maps of ideal
sheaves are determined by their composite with the inclusion into the structure sheaf, which is a
monomorphism: spaces-side that composite is
`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι`, the inverse image of the
inclusion followed by the comparison `g^*𝒪_{V'} ⟶ 𝒪_V` of
`AlgebraicGeometry.Space.structureModulePullbackMap`, and schemes-side it is the same statement
for `Stacks.ClosedImmersion.idealSheaf`.  The comparison of this file is already compatible with
the two inclusions, by
`AlgebraicGeometry.Space.chartZariskiIdealSheafSelfChartIsoIdealSheaf_hom_comp_ι`.  So what part
(2) still needs at the level of ideal sheaves is the compatibility of
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` at the **unit** module with the
two structure-sheaf comparisons: that it carries
`AlgebraicGeometry.Space.structureModulePullbackMap` of the represented morphism to the
schemes-side comparison `g^♯`.  The passage from there to the conormal maps is then the inverse
image along the inclusion of `R` together with
`AlgebraicGeometry.Space.conormalPullbackComparison`, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleCompositionLaw.lean`, and the final match
with `Stacks.Immersion.immersionConormalSheafMap` is its affine characterisation
`Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap` together with the
uniqueness `Stacks.Immersion.immersionConormalSheafMap_unique`.

`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` is the composite of two
comparisons, and the unit-module compatibility of the **second** of them is now available.
`StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModulePullbackUnit.lean` proves it, together
with the general fact it is an instance of: by
`SheafOfModules.pullbackSquareIso_hom_app_unit` the comparison of the two composite pullbacks of
modules round any square of ringed sites is compatible with the canonical maps
`SheafOfModules.pullbackObjUnitToUnit` out of the pullback of the unit module, and
`AlgebraicGeometry.SmallEtale.pullbackObjUnitToUnit_associatedModuleBaseChangeIso` reads that at
the square of [Stacks Project, Tag 03LC] (1) — which is the square
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso`, the second factor of the
comparison, is built from.  That file also records the handle the argument turns on,
`CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp`: a comparison of two left adjoints of
one right adjoint cannot describe its own values, but a composite whose first factor is the
comparison has a computable transpose, so the comparison cancels.

The **first** factor is `AlgebraicGeometry.Space.representedModuleObjPullbackIso`, which is
`AlgebraicGeometry.Space.representedModulePullbackIso` read at one module and corrected by the
unit and the counit of `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`.  It is
not an instance of `SheafOfModules.pullbackSquareIso`, because one of its four pullbacks is
`AlgebraicGeometry.Space.modulePullback` rather than a `SheafOfModules.pullback`, and the two are
compared by `AlgebraicGeometry.Space.modulePullbackChartIso`.

**The square itself is now proved.**
`AlgebraicGeometry.Space.structureModulePullbackMap_representedModulePullbackIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackUnit.lean` is the unit-module
compatibility of `AlgebraicGeometry.Space.representedModulePullbackIso`: that comparison carries
`AlgebraicGeometry.Space.structureModulePullbackMap` of the represented morphism to
`SheafOfModules.pullbackObjUnitToUnit` of
`AlgebraicGeometry.Space.representedSchemeStructureMapRing`, the structure map of the morphism of
small étale ringed sites of [Stacks Project, Tag 070R] (2) of the underlying morphism of schemes.
No value of the comparison is computed: the two sides are morphisms out of an inverse image of
the unit module, and `CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp` reduces the
claim to the equality of the two transposes, which is
`AlgebraicGeometry.Space.representedStructureMapRing_square` read at the unit module —
`AlgebraicGeometry.Space.homEquiv_structureModulePullbackMap_comp_eq` there.  Its inputs are
`AlgebraicGeometry.Space.modulePushforwardChartIso_structureModuleFMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/StructureModulePullbackChart.lean` for the fourth factor of
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` and the three
`SheafOfModules.unitToPushforwardObjUnit_*` lemmas of
`StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModulePullbackUnit.lean` for the other three.

So what the ideal-sheaf level still needs is **three further steps**.  Two of them are now done
and the third is named precisely.

* The **obj form** — carrying the compatibility just proved from
  `AlgebraicGeometry.Space.representedModulePullbackIso` to
  `AlgebraicGeometry.Space.representedModuleObjPullbackIso` — **is proved**:
  `AlgebraicGeometry.Space.structureModulePullbackMap_representedModuleObjPullbackIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleObjPullbackUnit.lean`.  At the unit
  module the equivalence's unit correction is `CategoryTheory.Iso.refl` by `rfl` and its counit
  correction cancels, by naturality together with
  `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence_counitIso_app_unit` — the
  counit *at the unit module* is the identity, which is not true of the counit at the inverse
  image of that module, where the corresponding equation is not even type-correct.  Its
  composition with the second factor
  `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso`, whose own unit-module
  compatibility is
  `AlgebraicGeometry.SmallEtale.pullbackObjUnitToUnit_associatedModuleBaseChangeIso`,
  **is also proved**:
  `AlgebraicGeometry.Space.structureModulePullbackMap_representedAssociatedModulePullbackIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModulePullbackUnit.lean` is the
  unit-module compatibility of
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` itself.
* The **naturality in the module** of
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` — **proved**, as
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_naturality` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModulePullbackNaturality.lean`.
  Nothing in the tree stated it, and the functor-level
  `AlgebraicGeometry.Space.schemePullbackRepresentedAssociatedModuleSquareIso` does not supply it —
  it is built from `AlgebraicGeometry.Space.representedModulePullbackFunctorIso`, the *forward*
  direction, whereas the obj form comes from
  `AlgebraicGeometry.Space.representedModulePullbackIso`, the *inverse* direction corrected by
  unit and counit.  But the naturality is **formal**: the obj form is a composite of components
  of natural transformations, and `Stacks.Equivalence.conjugateObjIso_naturality` of
  `StacksFrontier/CategoryTheory/Equivalence/ConjugateObjIsoNaturality.lean` proves it for any
  family given by that formula, the formula being discharged at the instantiation by `rfl` as an
  equation of isomorphisms.  The second factor was better off in any case:
  `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso` *is* by definition a component
  of the functor isomorphism `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`, so
  its naturality is that isomorphism's own.
* The **compatibility of the Zariski reading with the inclusion into the structure sheaf**,
  which this development has in transposed and in sections form but not as a morphism-level
  `… ≫ ι = …`.  The section "The compatibility of the étale-site reading with the inclusions,
  which is now proved" of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiDefiningIdeal.lean` is the
  authoritative account: the compatibility is
  `Space.associatedModuleChartZariskiIdealSheafSelfChartIso_transpose_val_app_apply`
  of `StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModuleChartPushTranspose.lean`, resting on
  the right triangle identity
  `AlgebraicGeometry.SmallEtale.unit_comp_restrictModule_map_associatedModuleRestrictModuleIso_hom`
  there.  **None** of the behaviour of
  `AlgebraicGeometry.SmallEtale.associatedModule` on a submodule inclusion,
  `AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit`, or the counit's compatibility with
  it is used.  The morphism-level form that the `cancel_mono` on `(definingIdealSheaf …).ι` needs
  is **proved too**:
  `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso_hom_comp_ι` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedIdealSheafInclusion.lean`.

All three are therefore available, and **the ideal-sheaf level of part (2) is proved**:
`AlgebraicGeometry.Space.kernelIdealSquareMap_representedAssociatedModuleKernelIdealZPowIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedKernelIdealSquareMapAgreement.lean` says that
`AlgebraicGeometry.Space.kernelIdealSquareMap` in degree one is the associated module of
`Stacks.ClosedImmersion.idealSheafMap`.  It is stated at
`AlgebraicGeometry.Space.kernelIdealSheafZPow` rather than at the defining ideal sheaf, that
being the spelling `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap`, and hence part (2)'s
registration, uses; the passage between the two is
`AlgebraicGeometry.Space.kernelIdealSheafZPow_one_representedSpaceMap`.

**What part (2) owes after that is one further comparison, and it is genuinely absent.**  Each of
the two canonical maps of conormal modules is the square comparison followed by the inverse image
along the upper morphism of the map of ideal sheaves just identified, so what remains is the
agreement of the two **square comparisons read at the ideal sheaf** — not at the structure sheaf,
where both are described.  The description at the structure sheaf does not determine the one at
the ideal sheaf: the inverse image along the upper morphism of the inclusion of a sheaf of ideals
is not a monomorphism, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionFunctorial.lean` record.  Since both
square comparisons are built from the composition comparison of [Stacks Project, Tag 03LU] on
each side, that agreement is the compatibility of
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` with **composition** of
represented morphisms.  That single statement is what part (2)'s closed case now reduces to, and
it is itself reduced, exactly and with nothing left over, to the same compatibility for
`AlgebraicGeometry.Space.representedModuleObjPullbackIso` by
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_of_objComp` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModulePullbackComposition.lean` —
the composition law of [Stacks Project, Tag 03LC] (1) which that reduction consumes being
proved as `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_comp`.  The residue
after that reduction, and the route to it, are set out in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionFunctorial.lean`.

## The square-comparison level of part (2) is proved on both sides

The other half of part (2) — the agreement of the two **square comparisons** — now has both of
its halves.  Ringed-space side it is
`Stacks.ClosedImmersion.pullbackCompIso_hom_comp_modulePullbackUnitToUnit` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonUnit.lean`; spaces-side it is
`AlgebraicGeometry.Space.squarePullbackCompIso_hom_comp_structureModulePullbackMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonSpacesUnit.lean`.  The second
exists at `AlgebraicGeometry.Space.squarePullbackCompIso` rather than at
`AlgebraicGeometry.Space.conormalPullbackCompIso`, which is where part (2) needs it:
`AlgebraicGeometry.Space.conormalMapOfImmersions` is built from
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap`, whose middle factor is the former.  Part
(2) does not need the comparison at `AlgebraicGeometry.Space.conormalPullbackCompIso`, so no
reshaping of the `AlgebraicGeometry.Space.subspaceInclusion` signatures across the library is
called for; `ConormalSquareComparisonUnit.lean` records why.

Both canonical maps are now also written in one and the same two-factor shape — the square
comparison followed by the inverse image along `i` of a single map of ideal sheaves — with the
same characterising lemma on each side:
`Stacks.ClosedImmersion.conormalSheafMap` with `Stacks.ClosedImmersion.idealSheafMap_comp_ι`,
and `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_eq_comp` with
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι` of
`StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMap.lean`.  The spaces-side map read
inside `i^*𝒪_X` is `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_comp_map_ι` and, with
the square comparison moved to the unit module,
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_comp_map_ι_unit`; the ringed-space mirror
is `Stacks.ClosedImmersion.conormalSheafMap_comp_pullback_ι`.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

-- See the implementation notes: these keep the elaborator from unfolding the inverse image and
-- the composition comparison to their constructions, which does not terminate.
attribute [local irreducible] modulePullback modulePullbackCompIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R V : BigFppfOver B S hS} (j : R ⟶ V)
    [hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]

/-- The Zariski restriction, to the identity chart of `yoneda.obj V`, of the defining ideal
sheaf of the closed subspace which `j` cuts out. -/
noncomputable abbrev selfChartZariskiDefiningIdeal :
    SheafOfModules.{u} (chartScheme (selfChart B S hS V)).ringCatSheaf :=
  (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
    (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
      (closedSubspaceRange B S hS j hj)) (selfChart B S hS V)).toSheafOfModules

/-- The inverse image along the identification of `yoneda.obj R` with the closed subspace cut
out by `j`, of the inverse image along the inclusion of that subspace, is the inverse image
along the represented morphism, read at the defining ideal sheaf.

`AlgebraicGeometry.Space.modulePullback` depends on the morphism only as a functor between two
categories which the two spellings share, so the replacement is a `congrArg`; see the
implementation notes. -/
noncomputable def modulePullbackRepresentedSpaceMapIso :
    (modulePullback B S hS (rangeSpaceIso B S hS j hj).hom).obj
        (conormalModule B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)) ≅
      (modulePullback B S hS (representedSpaceMap B S hS j)).obj
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)).toSheafOfModules :=
  (modulePullbackCompIso B S hS (rangeSpaceIso B S hS j hj).hom
        (subspaceInclusion B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj))).app
      (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj)).toSheafOfModules ≪≫
    eqToIso (congrArg (fun m ↦ (modulePullback B S hS m).obj
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)).toSheafOfModules)
      (rangeSpaceIso_hom_comp_subspaceInclusion B S hS j hj))

/-- **The inverse image along a represented closed immersion of the defining ideal sheaf of its
range is the associated module of the schemes conormal sheaf.**

This is the part of the comparison below which does not mention the closed subspace at all, and
it is stated separately because it is what the immersion case reuses: applied to the
factorisation `AlgebraicGeometry.Space.immersionCoborderLift` of an arbitrary represented
immersion through its ambient open, it is the last leg of
`AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`.

The four steps are the last four of the route in the module documentation. -/
noncomputable def representedDefiningIdealPullbackConormalSheafIso :
    (modulePullback B S hS (representedSpaceMap B S hS j)).obj
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)).toSheafOfModules ≅
      (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
          (Stacks.Conormal.conormalSheaf ((BigFppfOver.toScheme B S hS).map j))) :=
  (modulePullback B S hS (representedSpaceMap B S hS j)).mapIso
      (representedAssociatedModuleChartZariskiIdealSheafIso B S hS V
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj))
        (isQuasicoherentOnSite_definingIdealSheaf B S hS
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj))).symm ≪≫
    representedAssociatedModulePullbackIso B S hS j
        (relativelyRepresentable_yoneda_map B S hS j) (selfChartZariskiDefiningIdeal B S hS j) ≪≫
      (representedSmallEtaleModuleEquivalence B S hS R).functor.mapIso
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj R) R.left.property).mapIso
          ((Scheme.Modules.pullback (B.inclusion.map j.left)).mapIso
              (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj) ≪≫
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
              ((BigFppfOver.toScheme B S hS).map j)).symm))

/-- **Stacks 04G2, part (1).**  For a morphism `j` of the big fppf category over `S` whose
underlying morphism of schemes is a closed immersion, the conormal module of [Stacks Project,
Tag 04CN] of the closed subspace which `j` cuts out of `yoneda.obj V` — read on `yoneda.obj R`
along the identification `AlgebraicGeometry.Space.rangeSpaceIso` of that subspace with it — is
the module which the conormal sheaf of [Stacks Project, Tag 01R2] of the underlying morphism of
schemes becomes on the small étale site.

This is the closed case.  The clause at the immersion generality the source states it at is
`AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`, which is this comparison
applied to the factorisation of the immersion through its ambient open. -/
@[stacks 04G2 "part (1): the conormal sheaf of a closed immersion of schemes of the site is the \
associated module of the conormal sheaf of Morphisms, Definition 01R2"]
noncomputable def conormalModuleClosedSubspaceRangeIso :
    (modulePullback B S hS (rangeSpaceIso B S hS j hj).hom).obj
        (conormalModule B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)) ≅
      (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
          (Stacks.Conormal.conormalSheaf ((BigFppfOver.toScheme B S hS).map j))) :=
  modulePullbackRepresentedSpaceMapIso B S hS j ≪≫
    representedDefiningIdealPullbackConormalSheafIso B S hS j

end AlgebraicGeometry.Space

end
