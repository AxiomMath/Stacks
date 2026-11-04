module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedIdealModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure

/-!
# The conormal module read on the chart of a subspace cut out by a chart of the ambient space

Let `Z ⊆ X` be a closed subspace of an algebraic space over a scheme `S` contained in a big fppf
site `B`, and let `U` be an étale scheme chart of `X`.  The inclusion `i : Z ⟶ X` is relatively
representable, so the base change `Z ×_X U` is an object of the big fppf category, the projection
`Z ×_X U ⟶ U` is a closed immersion of **schemes**
(`AlgebraicGeometry.Space.chartBaseChangeHom`), and the other projection is a morphism of
algebraic spaces

`AlgebraicGeometry.Space.chartBaseChangeToSubspaceHom : h_{Z ×_X U} ⟶ Z`

out of a *represented* algebraic space.  This file reads the conormal module `𝒞_{Z/X}` of
[Stacks Project, Tag 04CN] and the canonical map of [Stacks Project, Tag 04CP] along that
morphism, and identifies them with data living on the ambient chart `U`.

## Why the chart of the subspace is taken this way

The module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeComparison.lean` records, accurately,
that the conormal module of a closed subspace **cannot** be compared with its scheme-level avatar
by re-anchoring the subspace: for a represented closed subspace `Z.1` is
`CategoryTheory.Subfunctor.range (yoneda.map j)` and not `yoneda.obj R`, and transporting
`AlgebraicGeometry.Space.conormalModule` along that isomorphism of presheaves makes an inverse
image of modules unfold to its construction by sheafification and not terminate.

Nothing below transports anything along an isomorphism of presheaves.  The chart of the subspace
is not chosen independently and then compared with `Z.1`: it is the morphism
`CategoryTheory.Functor.relativelyRepresentable.fst` of the representability datum carried by the
closed immersion `Z ⟶ X`, whose target *is* `Z.1.toFunctor` on the nose.  So the inverse image of
modules along it is formed at the subspace as it stands, and the composite with the inclusion of
`Z` is, again on the nose, the composite of the closed immersion of schemes with the ambient
chart — which is the equation that moves every statement onto the ambient chart.  This is the
same manoeuvre as in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFactorizationVanishing.lean`, where the
vanishing of the composite of two conormal maps is proved on the sections of the defining ideal
sheaf over a chart of the **ambient** space and no chart of the subspace appears at all.

## Main definitions

* `AlgebraicGeometry.Space.chartToSchemeSpace`: the structure morphism of an étale scheme chart,
  with its source written as `AlgebraicGeometry.schemeSpace`; see the implementation notes for
  why that spelling and not `AlgebraicGeometry.Space.chartToSpace`, to which it is equal by
  `AlgebraicGeometry.Space.chartToSchemeSpace_eq_chartToSpace`.
* `AlgebraicGeometry.Space.chartBaseChangeToSubspaceHom`: the projection `Z ×_X U ⟶ Z`, the chart
  of the subspace that a chart of the ambient space cuts out.
* `AlgebraicGeometry.Space.subspaceChartBaseChange`: that same chart as an **object of the small
  étale site of the subspace**, so that it can be fed to anything asking for a chart of `Z`.
* `AlgebraicGeometry.Space.repPullbackCompIso`: **transitivity of representable base change**,
  `F ×_G (G ×_H V) ≅ F ×_H V`, and
  `AlgebraicGeometry.Space.subspaceChartBaseChangeCompIso`, its instance
  `Z ×_Y (Y ×_{X'} V) ≅ Z ×_{X'} V` at a closed subspace of a closed subspace.
* `AlgebraicGeometry.Space.conormalModuleChartCompIso`: the comparison of the two composite
  inverse images around the base change square, by [Stacks Project, Tag 03LU].
* `AlgebraicGeometry.Space.modulePullbackConormalModuleChartIso`: **the inverse image of the
  conormal module along that chart**, identified with the inverse image along the closed
  immersion of schemes `Z ×_X U ⟶ U` of the restriction of the defining ideal sheaf to the
  ambient chart.
* `AlgebraicGeometry.Space.modulePullbackConormalModuleChartZariskiIso`: the same, carried on to
  `ε^*` of a single **Zariski** sheaf of ideals of the scheme `Z ×_X U`.

## Main results

* `AlgebraicGeometry.Space.isPullback_chartBaseChangeToSubspace` and
  `AlgebraicGeometry.Space.chartBaseChangeToSubspace_comp_subspaceInclusion`: the base change
  square of a closed subspace along an étale chart of the ambient space, read in algebraic
  spaces.  The square is the one the representability datum of the inclusion supplies; it occurs
  inline, as a `have hpb`, in the proof of
  `AlgebraicGeometry.Space.preimage_chartPointsMap_range_eq_zeroLocus_definingIdealAt`
  (`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/StalkTorsionOfSupportedComplex.lean`) and is
  named here.
* `AlgebraicGeometry.Space.isEtale_chartBaseChangeToSubspaceHom`: that chart of the subspace is an
  étale morphism of algebraic spaces, by base change of the étale chart of the ambient space.
* `AlgebraicGeometry.Space.isPullback_repPullbackComp` and
  `AlgebraicGeometry.Space.isPullback_chartBaseChangeToSubspace_comp`: the Cartesian square
  exhibiting an iterated representable base change as a base change along the composite, in
  general and at a closed subspace of a closed subspace.
* `AlgebraicGeometry.Space.modulePullback_conormalMap_chartBaseChange`: **the chart reading of
  the canonical map of conormal modules.**  Through
  `AlgebraicGeometry.Space.conormalModuleChartCompIso`, the inverse image of
  `AlgebraicGeometry.Space.conormalMap` along the chart of the subspace is the inverse image,
  along the closed immersion of schemes `Z ×_X U ⟶ U`, of the restriction to the ambient chart of
  the map `g^*𝓘' ⟶ 𝓘` of defining ideal sheaves of
  `AlgebraicGeometry.Space.idealSheafMap`.

  So the conormal map on a chart of the subspace is determined by the map of ideal sheaves on a
  chart of the **ambient** space, which is where
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedIdealSheafMapComparison.lean` works.

## What is not proved

* **The identification with the scheme-level `Stacks.Immersion.immersionConormalSheafMap` is not
  proved**, and no declaration below should be read as asserting it.  What is reduced is the
  *object* side, all the way to a Zariski sheaf of ideals: the right-hand side of
  `AlgebraicGeometry.Space.modulePullbackConormalModuleChartZariskiIso` is `ε^*` of the Zariski
  pullback, along the closed immersion `Z ×_X U ⟶ U`, of the sheaf of ideals that the
  inverse-image subspace cuts out on the chart scheme.  **That object side is joined to the
  scheme-level conormal sheaf**: the right-hand side *is* `ε^*` of
  `Stacks.ClosedImmersion.conormalSheaf` of the closed immersion `Z ×_X U ⟶ U`, by
  `AlgebraicGeometry.Space.modulePullbackConormalModuleChartConormalSheafIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleChartConormalSheaf.lean`.  What is left is
  the **map**, and the last paragraph of this entry says what that needs.  The two inputs of that
  assembly:
  * the sheaf of ideals of `AlgebraicGeometry.Space.schemeSpaceIdeal` is an
    `AlgebraicGeometry.Scheme.IdealSheafData`, read as a submodule of the structure sheaf by
    `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule`, while
    `Stacks.ClosedImmersion.conormalSheaf` is the inverse image of the ringed-space ideal sheaf
    `Stacks.ClosedImmersion.idealSheaf`, the kernel of the comorphism.  **The two are
    identified**, and the identification needs no new mathematics:
    `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule` *is* the sectionwise kernel of the
    very morphism whose categorical kernel is `Stacks.ClosedImmersion.idealSheaf`, so
    `Stacks.ClosedSubscheme.unitSubmoduleIsoKernel` is already that identification in a
    spelling which does not name it.  It is stated, characterised against the inclusion into
    the structure sheaf, and carried to an arbitrary closed immersion of schemes and on to the
    conormal sheaf, in
    `StacksFrontier/AlgebraicGeometry/Conormal/IdealSheafDataComparison.lean`:
    `AlgebraicGeometry.Scheme.IdealSheafData.kerUnitSubmoduleIsoIdealSheaf` and
    `AlgebraicGeometry.Scheme.IdealSheafData.modulePullbackKerUnitSubmoduleIsoConormalSheaf`
    apply directly to the closed immersion of schemes `Z ×_X U ⟶ U`, whose kernel
    `AlgebraicGeometry.Space.ker_chartBaseChangeHom` computes.  The passage across the
    isomorphism `AlgebraicGeometry.Scheme.Hom.toImage` is
    `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSourceOfCompEq` of
    `StacksFrontier/AlgebraicGeometry/ConormalSourceTransport/Basic.lean`, an isomorphism of
    sheaves of modules — and not the *target*-slot transport
    `Stacks.Conormal.AffineCotangent.Transport.idealSheafIsoOfIsoTarget`, which is for an
    isomorphism of the ambient scheme and does not apply.
  * on the map side, the compatibility of
    `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso` with
    `AlgebraicGeometry.Space.idealSheafMap` is proved in
    `StacksFrontier/AlgebraicGeometry/Spaces/ChartIdealSheafMapComparison.lean`:
    `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso_hom_eq_idealSheafMap` says
    that the chart isomorphism *is* the map `φ^*𝓘_Z ⟶ 𝓘_{φ^{-1}Z}` of [Stacks Project, Tag 04CP],
    transported along `AlgebraicGeometry.Space.representedDefiningIdealSheafIso`, and
    `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso_hom_comp_comparison` is the
    equation against the inclusion into the structure sheaf that
    `AlgebraicGeometry.Space.eq_idealSheafMap_comp_representedDefiningIdealSheafIso_inv` of
    `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedIdealSheafMapComparison.lean` asks for.
    That file states its reduction for a closed subspace of the *chart* and a square whose upper
    ambient space is the chart, which is no restriction here: taking the subspace to be
    `φ^{-1}Z` and the square to be the one over `Z ⊆ X` is exactly the instantiation that
    applies, so nothing has to be restated for a general `X`.

    **How the connection is made.**  Composing
    `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso` with
    `AlgebraicGeometry.Space.representedIdealComparison` and cancelling
    `AlgebraicGeometry.Space.representedDefiningIdealSheafIso_inv_comp_representedIdealComparison`
    leaves exactly one equation to prove, between morphisms
    `φ^*𝓘_Z ⟶ 𝒪_{h_V}`: that the first two factors of that isomorphism — the étale restriction
    comparison `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback` of Equation 03LW
    and `AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso` of 04CO — followed by the
    inclusion `𝓘_{φ^{-1}Z} ⊆ 𝒪_{h_V}`, are `φ^*` of the inclusion `𝓘_Z ⊆ 𝒪_X` followed by
    `AlgebraicGeometry.Space.structureModulePullbackMap`.  The 04CO factor is the identity on
    underlying regular functions by `rfl`
    (`AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso_hom_apply_coe`), so the content is
    the structure-sheaf case alone: **that along an étale morphism the canonical comparison
    `φ^*𝒪_X ⟶ 𝒪_{h_V}` is the Equation 03LW identification.**

    **That structure-sheaf lemma is now proved.**  It is
    `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_unit_eq` of
    `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStructureSheaf.lean`, together
    with the invertibility `AlgebraicGeometry.Space.isIso_structureModulePullbackMap_of_isEtale`
    and the injectivity `AlgebraicGeometry.Space.mono_structureModulePullbackMap_of_isEtale` of
    `StacksFrontier/AlgebraicGeometry/Spaces/EtaleStructureModulePullbackMap.lean` that follow from
    it.  It is proved there through the corepresentability comparison
    `AlgebraicGeometry.Space.modulePullbackUnitIso` of Stacks 03LU: the map
    `AlgebraicGeometry.Space.structureModulePullbackMap` is that comparison, by
    `AlgebraicGeometry.Space.structureModulePullbackMap_eq_modulePullbackUnitIso_hom_of_unit`, and
    so is the Equation 03LW component, by
    `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_unit`.  The
    assembly of the equation out of the three factors is
    `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso_hom_comp_comparison`, and
    needed only naturality of Equation 03LW at the inclusion `𝓘_Z ⊆ 𝒪_X` on top of that
    structure-sheaf case.
  **What the map still needs.**
  `AlgebraicGeometry.Space.modulePullback_conormalMap_chartBaseChange` below puts the chart
  inverse image of `conormalMap`, for a square `Z ⊆ X` over `Z' ⊆ X'`, as the
  inverse image along `Z ×_X U ⟶ U` of the restriction of
  `AlgebraicGeometry.Space.idealSheafMap` to the ambient chart of `X`.  The **target** of that
  restriction, `φ^*𝓘_Z`, is identified with `ε^*` of
  `Stacks.ClosedImmersion.idealSheaf` by
  `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIsoIdealSheaf`.  Its **source** is
  `φ^*g^*𝓘_{Z'}`, the inverse image along `g ∘ φ : h_U ⟶ X'`, and `g ∘ φ` is not étale — for the
  sequences of [Stacks Project, Tag 06BD] and [Stacks Project, Tag 06BF] the morphism `g` is a
  closed immersion — so `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso` does
  not apply at the source.  What is needed is a chart `V` of `X'` with a factorisation of
  `g ∘ φ` through `h_V`, and for `g` the inclusion of a closed subspace `Y ⊆ X'` that
  factorisation is `AlgebraicGeometry.Space.chartBaseChangeToSubspace_comp_subspaceInclusion`
  below, with `U` taken to be `Y ×_{X'} V`; the identification of the source is then
  `AlgebraicGeometry.Space.conormalModuleChartCompIso` evaluated at `𝓘_{Z'}`.

  **Both packaging steps that route asks for are below.**  The chart `Y ×_{X'} V ⟶ Y` is an
  object of `AlgebraicGeometry.Space.SmallEtale` of `Y` by
  `AlgebraicGeometry.Space.subspaceChartBaseChange`, whose structure morphism is
  `AlgebraicGeometry.Space.chartBaseChangeToSubspaceHom` by
  `AlgebraicGeometry.Space.chartToSchemeSpace_subspaceChartBaseChange`; the functor doing the work
  is `AlgebraicGeometry.Space.smallBaseChange` of [Stacks Project, Tag 03G2], part (4), and the
  étaleness `AlgebraicGeometry.Space.isEtale_chartBaseChangeToSubspaceHom` is base change of
  étale morphisms.
  And the iterated base change `Z ×_Y (Y ×_{X'} V)` is `Z ×_{X'} V` by
  `AlgebraicGeometry.Space.subspaceChartBaseChangeCompIso`, an instance of the transitivity of
  representable base change `AlgebraicGeometry.Space.repPullbackCompIso`, with the Cartesian
  square over `X'` itself recorded as
  `AlgebraicGeometry.Space.isPullback_chartBaseChangeToSubspace_comp`.

  **What is still open is the map identification itself**: assembling those two with
  `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIsoIdealSheaf` at the target and
  `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso` at the source into a single
  equation against the scheme-level `Stacks.Immersion.immersionConormalSheafMap`.
* **No tag is registered.**  Nothing here is a statement of the Stacks Project: the conormal
  module is [Stacks Project, Tag 04CN] and its canonical map [Stacks Project, Tag 04CP], both
  already registered where they are constructed, and what is added is a reading of them along one
  morphism, which is a proof step and not a clause.  In particular the middle exactness of
  [Stacks Project, Tag 06BD], the middle of clause (2) of [Stacks Project, Tag 06BF], the
  hypothesis `hmid` of
  `AlgebraicGeometry.Space.universalThickeningCompConormalSequence_shortExact'` and the
  invertibility clause of [Stacks Project, Tag 05ZX] all remain open.  Each is an exactness
  statement, so transferring it with the descent machinery of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSchemeChartExactness.lean` requires the
  short complexes to be identified, and that is a statement about maps: the object
  identification above does not reach it.

## Implementation notes

**Every spelling below uses the plain `def`s `AlgebraicGeometry.schemeSpace` and
`AlgebraicGeometry.schemeSpaceMap`, and not the reducible `abbrev`s
`AlgebraicGeometry.Space.representedAlgebraicSpace` and
`AlgebraicGeometry.Space.representedSpaceMap`.**  This is a requirement and not a
preference.  With the represented algebraic space of `Z ×_X U` and the morphism
`Z ×_X U ⟶ U` written at the `abbrev` spellings, the proof of
`AlgebraicGeometry.Space.modulePullback_conormalMap_chartBaseChange` exhausts the heartbeat
budget — `(deterministic) timeout at isDefEq, maximum number of heartbeats (200000)`, on the
final congruence, and `timeout at whnf` on the type ascription of the naturality square.  At the
`def` spellings the whole file is checked in about a second.  The reason is that `abbrev` is
reducible, so the unifier unfolds the chart objects and morphisms inside every
`AlgebraicGeometry.Space.modulePullback` it has to compare, while an opaque `def` blocks that.
`AlgebraicGeometry.Space.chartToSpace` is reducible for the same reason — it is an `abbrev`
through `AlgebraicGeometry.Space.chartOver` — which is why
`AlgebraicGeometry.Space.chartToSchemeSpace` is introduced rather than used;
`AlgebraicGeometry.Space.chartToSchemeSpace_eq_chartToSpace` records that the two are the same
morphism, so this is a second spelling and not a second notion.

**The map reading is proved by term congruences and not by `rw`.**  The right-hand factor of
`AlgebraicGeometry.Space.conormalMap_eq` carries a type ascription onto
`AlgebraicGeometry.Space.conormalModule`, and `rw` type-checks its result under `implicit`
transparency: `rw [conormalMap_eq …]` followed by `rw [Functor.map_comp]` fails with *the target
expression is not type-correct under the `implicit` transparency level*, reporting an application
of `AlgebraicGeometry.IsClosedImmersion` where a `CategoryTheory.MorphismProperty` is expected.
Each step is therefore a `congrArg` against an explicitly written motive, and the naturality
square is given its type by ascription so that no composite functor has to be unfolded during
unification.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module.
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), its canonical map.
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO), the étale restriction of
  the defining ideal sheaf.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal
  sheaf.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the inverse image of
  modules and its composition comparison.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (4), base change
  of étale scheme charts along a representable morphism.
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU), base change of an étale
  morphism of algebraic spaces.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the comparison `ε`.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), part (4), the associated
  module.
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4), the scheme-level map of
  conormal sheaves this is to be compared with.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The ambient chart, at the `schemeSpace` spelling -/

/-- **The structure morphism of an étale scheme chart, as a morphism of algebraic spaces whose
source is written `AlgebraicGeometry.schemeSpace`.**  This is
`AlgebraicGeometry.Space.chartToSpace`; the two are equal by
`AlgebraicGeometry.Space.chartToSchemeSpace_eq_chartToSpace`.

The reason for a second spelling is recorded in the implementation notes of this file: the source
of `chartToSpace` is a reducible `abbrev`, and at that spelling the unifier unfolds the chart
inside every inverse image of modules and the map reading below exhausts the heartbeat budget. -/
def chartToSchemeSpace (Y : AlgebraicSpaces B S hS) (W : SmallEtale B S hS Y.1) :
    schemeSpace W.1.left ⟶ Y :=
  ObjectProperty.homMk W.1.hom

/-- `AlgebraicGeometry.Space.chartToSchemeSpace` is `AlgebraicGeometry.Space.chartToSpace`: the
two differ only in how the represented algebraic space of the chart scheme is written. -/
theorem chartToSchemeSpace_eq_chartToSpace (Y : AlgebraicSpaces B S hS)
    (W : SmallEtale B S hS Y.1) :
    chartToSchemeSpace B S hS Y W = chartToSpace B S hS Y W :=
  rfl

/-- **An étale scheme chart is an étale morphism of algebraic spaces**, read at
`AlgebraicGeometry.Space.chartToSchemeSpace`.  This is
`AlgebraicGeometry.Space.isEtale_chartToSpace`, étaleness being a property of the underlying
morphism of presheaves, which the two spellings share. -/
theorem isEtale_chartToSchemeSpace (Y : AlgebraicSpaces B S hS) (W : SmallEtale B S hS Y.1) :
    IsEtale B S hS (chartToSchemeSpace B S hS Y W).hom :=
  isEtale_chartToSpace B S hS Y W

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (U : SmallEtale B S hS X.1)

/-! ### The chart of a closed subspace cut out by a chart of the ambient space -/

/-- **The projection `Z ×_X U ⟶ Z` of the base change of a closed subspace along an étale chart
of the ambient space**, as a morphism of algebraic spaces out of a *represented* one.

It is `CategoryTheory.Functor.relativelyRepresentable.fst` of the representability datum carried
by the closed immersion `Z ⟶ X`, whose target is `Z.1.toFunctor` itself; so this is a chart of
the subspace which needs no transport along an isomorphism of presheaves.  Its companion, the
closed immersion of schemes `Z ×_X U ⟶ U`, is
`AlgebraicGeometry.Space.chartBaseChangeHom`. -/
def chartBaseChangeToSubspaceHom :
    schemeSpace (Z.2.2.rep.pullback U.1.hom) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (Z.2.2.rep.fst U.1.hom)

/-- **The base change square of a closed subspace along an étale chart of the ambient space is
cartesian in algebraic spaces.**  It is the pullback square of the representability datum of the
inclusion, and the inclusion of the algebraic spaces into the presheaves is faithful and
reflects pullbacks it has. -/
theorem isPullback_chartBaseChangeToSubspace :
    IsPullback (chartBaseChangeToSubspaceHom B S hS Z U)
      (schemeSpaceMap (Z.2.2.rep.snd U.1.hom))
      (subspaceInclusion B S hS X Z) (chartToSchemeSpace B S hS X U) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) (Z.2.2.rep.isPullback U.1.hom)

/-- **The commutativity of the base change square**: the chart of the subspace followed by the
inclusion of the subspace is the closed immersion of schemes followed by the chart of the ambient
space.

This one equation is what moves every statement below onto the ambient chart. -/
theorem chartBaseChangeToSubspace_comp_subspaceInclusion :
    chartBaseChangeToSubspaceHom B S hS Z U ≫ subspaceInclusion B S hS X Z =
      schemeSpaceMap (Z.2.2.rep.snd U.1.hom) ≫ chartToSchemeSpace B S hS X U :=
  (isPullback_chartBaseChangeToSubspace B S hS Z U).w

/-! ### The two composite inverse images around the square -/

/-- **The comparison of the two ways around the base change square**, as an isomorphism of
functors: the inverse image along the inclusion of `Z` followed by the inverse image along the
chart of the subspace is the inverse image along the chart of the ambient space followed by the
inverse image along the closed immersion of schemes.

It is the composition comparison of [Stacks Project, Tag 03LU] on each side with the
commutativity of the square in the middle, the same three-step body as
`AlgebraicGeometry.Space.conormalPullbackCompIso`. -/
def conormalModuleChartCompIso :
    modulePullback B S hS (subspaceInclusion B S hS X Z) ⋙
        modulePullback B S hS (chartBaseChangeToSubspaceHom B S hS Z U) ≅
      modulePullback B S hS (chartToSchemeSpace B S hS X U) ⋙
        modulePullback B S hS (schemeSpaceMap (Z.2.2.rep.snd U.1.hom)) :=
  modulePullbackCompIso B S hS (chartBaseChangeToSubspaceHom B S hS Z U)
      (subspaceInclusion B S hS X Z) ≪≫
    eqToIso (congrArg
      (fun h : schemeSpace (Z.2.2.rep.pullback U.1.hom) ⟶ X => modulePullback B S hS h)
      (chartBaseChangeToSubspace_comp_subspaceInclusion B S hS Z U)) ≪≫
    (modulePullbackCompIso B S hS (schemeSpaceMap (Z.2.2.rep.snd U.1.hom))
      (chartToSchemeSpace B S hS X U)).symm

/-- **The inverse image of the conormal module along the chart of the subspace cut out by a
chart of the ambient space.**  It is the inverse image, along the closed immersion of schemes
`Z ×_X U ⟶ U`, of the restriction of the defining ideal sheaf of `Z` to the ambient chart.

The conormal module is by definition the inverse image of the defining ideal sheaf along the
inclusion (`AlgebraicGeometry.Space.conormalModule_eq`), so this is
`AlgebraicGeometry.Space.conormalModuleChartCompIso` evaluated at that ideal sheaf. -/
def modulePullbackConormalModuleChartIso :
    (modulePullback B S hS (chartBaseChangeToSubspaceHom B S hS Z U)).obj
        (conormalModule B S hS X Z) ≅
      (modulePullback B S hS (schemeSpaceMap (Z.2.2.rep.snd U.1.hom))).obj
        ((modulePullback B S hS (chartToSchemeSpace B S hS X U)).obj
          (definingIdealSheaf B S hS X Z).toSheafOfModules) :=
  (conormalModuleChartCompIso B S hS Z U).app
    (definingIdealSheaf B S hS X Z).toSheafOfModules

/-! ### The chart reading of the conormal map -/

/-- **The inverse image of the canonical map of conormal modules along the chart of the subspace
is the inverse image, along the closed immersion of schemes `Z ×_X U ⟶ U`, of the restriction to
the ambient chart of the map of defining ideal sheaves.**

By `AlgebraicGeometry.Space.conormalMap_eq` the canonical map of [Stacks Project, Tag 04CP] is
the comparison `AlgebraicGeometry.Space.conormalPullbackComparison`, an isomorphism, followed by
the inverse image along the inclusion of `Z` of `AlgebraicGeometry.Space.idealSheafMap`; and the
naturality of `AlgebraicGeometry.Space.conormalModuleChartCompIso` at `idealSheafMap` carries
that second factor onto the ambient chart.  The isomorphism identifying the two targets is
`AlgebraicGeometry.Space.modulePullbackConormalModuleChartIso`, written out here as the component
of the comparison of functors so that one elaboration of it serves both sides.

**This is not the comparison with `Stacks.Immersion.immersionConormalSheafMap`**; the "What is
not proved" section of this file says what still separates the two. -/
theorem modulePullback_conormalMap_chartBaseChange (Z' : ClosedSubspaces B S hS X'.1)
    (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    (modulePullback B S hS (chartBaseChangeToSubspaceHom B S hS Z U)).map
        (conormalMap B S hS Z Z' g f hsq) ≫
          (conormalModuleChartCompIso B S hS Z U).hom.app
            (definingIdealSheaf B S hS X Z).toSheafOfModules =
      (modulePullback B S hS (chartBaseChangeToSubspaceHom B S hS Z U)).map
          (conormalPullbackComparison B S hS Z Z' g f hsq) ≫
        (conormalModuleChartCompIso B S hS Z U).hom.app
          ((modulePullback B S hS g).obj
            (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
        (modulePullback B S hS (schemeSpaceMap (Z.2.2.rep.snd U.1.hom))).map
          ((modulePullback B S hS (chartToSchemeSpace B S hS X U)).map
            (idealSheafMap B S hS Z Z' g f hsq)) := by
  have hnat : (modulePullback B S hS (chartBaseChangeToSubspaceHom B S hS Z U)).map
          ((modulePullback B S hS (subspaceInclusion B S hS X Z)).map
            (idealSheafMap B S hS Z Z' g f hsq)) ≫
        (conormalModuleChartCompIso B S hS Z U).hom.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules =
      (conormalModuleChartCompIso B S hS Z U).hom.app
          ((modulePullback B S hS g).obj
            (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
        (modulePullback B S hS (schemeSpaceMap (Z.2.2.rep.snd U.1.hom))).map
          ((modulePullback B S hS (chartToSchemeSpace B S hS X U)).map
            (idealSheafMap B S hS Z Z' g f hsq)) :=
    (conormalModuleChartCompIso B S hS Z U).hom.naturality
      (idealSheafMap B S hS Z Z' g f hsq)
  refine (congrArg (fun m =>
    (modulePullback B S hS (chartBaseChangeToSubspaceHom B S hS Z U)).map m ≫
      (conormalModuleChartCompIso B S hS Z U).hom.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules)
    (conormalMap_eq B S hS Z Z' g f hsq)).trans ?_
  exact (congrArg (· ≫ (conormalModuleChartCompIso B S hS Z U).hom.app
      (definingIdealSheaf B S hS X Z).toSheafOfModules)
    ((modulePullback B S hS (chartBaseChangeToSubspaceHom B S hS Z U)).map_comp _ _)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hnat))

/-! ### The chart of the subspace as an object of its own small étale site -/

/-- **The base change `Z ×_X U ⟶ Z` of a closed subspace along an étale chart of the ambient
space, packaged as an étale scheme chart of the subspace.**

The inclusion of a closed subspace is relatively representable, so base change along it acts on
small étale sites by `AlgebraicGeometry.Space.smallBaseChange` of [Stacks Project, Tag 03G2],
part (4); this is that functor applied to `U`.  Its structure morphism is
`AlgebraicGeometry.Space.chartBaseChangeToSubspaceHom`, by
`AlgebraicGeometry.Space.chartToSchemeSpace_subspaceChartBaseChange`. -/
def subspaceChartBaseChange :
    SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1 :=
  (smallBaseChange B S hS (subspaceInclusion B S hS X Z) Z.2.2.rep).obj U

/-- The structure morphism of `AlgebraicGeometry.Space.subspaceChartBaseChange` is
`AlgebraicGeometry.Space.chartBaseChangeToSubspaceHom`: the chart of the subspace which a chart of
the ambient space cuts out is an object of the small étale site of the subspace, and nothing in
the two spellings differs. -/
theorem chartToSchemeSpace_subspaceChartBaseChange :
    chartToSchemeSpace B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)
        (subspaceChartBaseChange B S hS Z U) =
      chartBaseChangeToSubspaceHom B S hS Z U :=
  rfl

/-- **The base change of a closed subspace along an étale chart of the ambient space is étale
over the subspace.**  It is the base change of the étale chart `U ⟶ X` along the inclusion of
`Z`, and étaleness of morphisms of algebraic spaces is stable under base change by
[Stacks Project, Tag 03FU]. -/
theorem isEtale_chartBaseChangeToSubspaceHom :
    IsEtale B S hS (chartBaseChangeToSubspaceHom B S hS Z U).hom :=
  isEtale_of_isPullback B S hS _ _ _ _
    (isPullback_chartBaseChangeToSubspace B S hS Z U).flip
    (isEtale_chartToSchemeSpace B S hS X U)

/-! ### Transitivity of base change along a composite of representable morphisms -/

/-- **The iterated base change along a composite of relatively representable morphisms is a
fibre product over the outermost target.**  For `κ : F ⟶ G` and `m : G ⟶ H` relatively
representable and a chart `v : h_V ⟶ H`, the scheme `F ×_G (G ×_H V)` sits in a Cartesian
square over the cospan of `κ ≫ m` and `v`.

It is the vertical pasting of the two representability squares. -/
theorem isPullback_repPullbackComp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {κ : F ⟶ G} (hκ : yoneda.relativelyRepresentable κ)
    {m : G ⟶ H} (hm : yoneda.relativelyRepresentable m)
    {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ H) :
    IsPullback (hκ.fst (hm.fst v))
      (yoneda.map (hκ.snd (hm.fst v)) ≫ yoneda.map (hm.snd v)) (κ ≫ m) v :=
  (hκ.isPullback (hm.fst v)).paste_vert (hm.isPullback v)

/-- **The iterated base change `F ×_G (G ×_H V)` is the base change `F ×_H V`.**  Both are
apexes of Cartesian squares over the cospan of `κ ≫ m` and `v`
(`AlgebraicGeometry.Space.isPullback_repPullbackComp` and the representability square of the
composite), so they are isomorphic in the big fppf category: the comparison of fibre products
is an isomorphism of presheaves, and it descends to the site because Yoneda is fully
faithful. -/
def repPullbackCompIso {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {κ : F ⟶ G} (hκ : yoneda.relativelyRepresentable κ)
    {m : G ⟶ H} (hm : yoneda.relativelyRepresentable m)
    (hc : yoneda.relativelyRepresentable (κ ≫ m))
    {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ H) :
    hκ.pullback (hm.fst v) ≅ hc.pullback v :=
  yoneda.preimageIso
    ((isPullback_repPullbackComp B S hS hκ hm v).isoIsPullback _ _ (hc.isPullback v))

/-- The presheaf morphism underlying `AlgebraicGeometry.Space.repPullbackCompIso` is the
comparison of the two Cartesian squares. -/
theorem yoneda_map_repPullbackCompIso_hom {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {κ : F ⟶ G} (hκ : yoneda.relativelyRepresentable κ)
    {m : G ⟶ H} (hm : yoneda.relativelyRepresentable m)
    (hc : yoneda.relativelyRepresentable (κ ≫ m))
    {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ H) :
    yoneda.map (repPullbackCompIso B S hS hκ hm hc v).hom =
      ((isPullback_repPullbackComp B S hS hκ hm v).isoIsPullback _ _ (hc.isPullback v)).hom :=
  yoneda.map_preimage _

/-- `AlgebraicGeometry.Space.repPullbackCompIso` is compatible with the projections to the
chart: on the chart `V` it is the composite of the two projections. -/
theorem repPullbackCompIso_hom_snd {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {κ : F ⟶ G} (hκ : yoneda.relativelyRepresentable κ)
    {m : G ⟶ H} (hm : yoneda.relativelyRepresentable m)
    (hc : yoneda.relativelyRepresentable (κ ≫ m))
    {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ H) :
    (repPullbackCompIso B S hS hκ hm hc v).hom ≫ hc.snd v =
      hκ.snd (hm.fst v) ≫ hm.snd v := by
  apply yoneda.map_injective
  rw [yoneda.map_comp, yoneda.map_comp, yoneda_map_repPullbackCompIso_hom]
  exact (isPullback_repPullbackComp B S hS hκ hm v).isoIsPullback_hom_snd _ _
    (hc.isPullback v)

/-- `AlgebraicGeometry.Space.repPullbackCompIso` is compatible with the projections to the
source of the composite. -/
theorem repPullbackCompIso_hom_fst {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {κ : F ⟶ G} (hκ : yoneda.relativelyRepresentable κ)
    {m : G ⟶ H} (hm : yoneda.relativelyRepresentable m)
    (hc : yoneda.relativelyRepresentable (κ ≫ m))
    {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ H) :
    yoneda.map (repPullbackCompIso B S hS hκ hm hc v).hom ≫ hc.fst v =
      hκ.fst (hm.fst v) := by
  rw [yoneda_map_repPullbackCompIso_hom]
  exact (isPullback_repPullbackComp B S hS hκ hm v).isoIsPullback_hom_fst _ _
    (hc.isPullback v)

/-! ### The chart of a closed subspace of a closed subspace -/

/-- The inclusion of a closed subspace of a closed subspace is relatively representable: it is
a composite of two relatively representable morphisms. -/
theorem relativelyRepresentable_subspaceInclusion_comp (Y : ClosedSubspaces B S hS X'.1)
    (T : ClosedSubspaces B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1) :
    yoneda.relativelyRepresentable
      (subspaceInclusion B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) T ≫
        subspaceInclusion B S hS X' Y).hom :=
  yoneda.relativelyRepresentable.comp_mem _ _ T.2.2.rep Y.2.2.rep

/-- **The chart of `T` cut out by the chart `Y ×_{X'} V` of `Y` is a fibre product of `T` and
`V` over `X'`.**  Let `Y ⊆ X'` be a closed subspace, `T ⊆ Y` a closed subspace of it and `V` an
étale chart of `X'`.  Taking `U := Y ×_{X'} V`, which is a chart of `Y` by
`AlgebraicGeometry.Space.subspaceChartBaseChange`, the base change `T ×_Y U` is a base change of
`T` along `V ⟶ X'` directly.

It is the vertical pasting of the two base-change squares
`AlgebraicGeometry.Space.isPullback_chartBaseChangeToSubspace`. -/
theorem isPullback_chartBaseChangeToSubspace_comp (Y : ClosedSubspaces B S hS X'.1)
    (T : ClosedSubspaces B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1)
    (V : SmallEtale B S hS X'.1) :
    IsPullback
      (chartBaseChangeToSubspaceHom B S hS T (subspaceChartBaseChange B S hS Y V))
      (schemeSpaceMap (T.2.2.rep.snd (subspaceChartBaseChange B S hS Y V).1.hom) ≫
        schemeSpaceMap (Y.2.2.rep.snd V.1.hom))
      (subspaceInclusion B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) T ≫
        subspaceInclusion B S hS X' Y)
      (chartToSchemeSpace B S hS X' V) :=
  (isPullback_chartBaseChangeToSubspace B S hS T
      (subspaceChartBaseChange B S hS Y V)).paste_vert
    (isPullback_chartBaseChangeToSubspace B S hS Y V)

/-- **`T ×_Y (Y ×_{X'} V)` is `T ×_{X'} V`.**  The scheme on which the chart of
`AlgebraicGeometry.Space.subspaceChartBaseChange` cuts out `T` is the base change of `T` along
the chart `V` of the outermost ambient space, by
`AlgebraicGeometry.Space.repPullbackCompIso`. -/
def subspaceChartBaseChangeCompIso (Y : ClosedSubspaces B S hS X'.1)
    (T : ClosedSubspaces B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1)
    (V : SmallEtale B S hS X'.1) :
    T.2.2.rep.pullback (subspaceChartBaseChange B S hS Y V).1.hom ≅
      (relativelyRepresentable_subspaceInclusion_comp B S hS Y T).pullback V.1.hom :=
  repPullbackCompIso B S hS T.2.2.rep Y.2.2.rep
    (relativelyRepresentable_subspaceInclusion_comp B S hS Y T) V.1.hom

/-! ### All the way to a Zariski sheaf of ideals of the base-changed scheme -/

/-- **The inverse image of the conormal module along the chart of the subspace is `ε^*` of a
single Zariski sheaf of ideals of the scheme `Z ×_X U`.**

Three steps.  The chart reading
`AlgebraicGeometry.Space.modulePullbackConormalModuleChartIso` puts it as the inverse image along
the closed immersion of schemes of the restriction of the defining ideal sheaf to the ambient
chart; `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso` identifies that
restriction with `ε^*` of the Zariski sheaf of ideals which the inverse-image subspace cuts out
on the chart scheme; and
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` — the base change of the
associated-module functor of [Stacks Project, Tag 03DU], part (4), along a morphism of
representable algebraic spaces — exchanges the inverse image with `ε^*`.

The right-hand side is the Zariski pullback along `Z ×_X U ⟶ U` of a sheaf of ideals of `𝒪_U`.
It is *not* `Stacks.ClosedImmersion.conormalSheaf` of that closed immersion; see the "What is not
proved" section of this file. -/
def modulePullbackConormalModuleChartZariskiIso :
    (modulePullback B S hS (chartBaseChangeToSubspaceHom B S hS Z U)).obj
        (conormalModule B S hS X Z) ≅
      (representedAssociatedModule B S hS (Z.2.2.rep.pullback U.1.hom)
          (isAlgebraicSpace_yoneda B S hS (Z.2.2.rep.pullback U.1.hom))).obj
        ((Scheme.Modules.pullback (B.inclusion.map (Z.2.2.rep.snd U.1.hom).left)).obj
          (schemeSpaceIdeal B S hS U.1.left
            ⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
              isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
                (isAlgebraicSpace_yoneda B S hS U.1.left)
                Z.2⟩).unitSubmodule.toSheafOfModules) :=
  modulePullbackConormalModuleChartIso B S hS Z U ≪≫
    (modulePullback B S hS (schemeSpaceMap (Z.2.2.rep.snd U.1.hom))).mapIso
      (chartModulePullbackDefiningIdealSheafIso B S hS Z U.1.left
        (isAlgebraicSpace_yoneda B S hS U.1.left) (chartToSchemeSpace B S hS X U)
        (isEtale_chartToSchemeSpace B S hS X U)) ≪≫
    representedAssociatedModulePullbackIso B S hS (Z.2.2.rep.snd U.1.hom)
      (relativelyRepresentable_yoneda_map B S hS (Z.2.2.rep.snd U.1.hom)) _

end AlgebraicGeometry.Space

end
