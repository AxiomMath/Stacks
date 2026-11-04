module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison

/-!
# Modules on an algebraic space and modules on its affine étale charts

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`.  An étale scheme chart
`W` of `X` with underlying scheme `T` gives two categories of modules which nothing in this
development compares: the `𝒪_X`-modules of `AlgebraicGeometry.Space.Modules`, on the small étale
site of `X`, and the `𝒪_T`-modules of `AlgebraicGeometry.Scheme.Modules`, on the Zariski site of
`T`.  This file builds the comparison **for an affine chart**, and it is unconditional.

The comparison in the direction scheme `→` space already exists:
`AlgebraicGeometry.Space.representedAssociatedModule` carries an `𝒪_T`-module to a module on the
small étale site of the algebraic space `yoneda.obj U` represented by the chart.  What this file
adds is that the comparison *hits* the restriction of a quasi-coherent `𝒪_X`-module to an affine
chart: for such a chart there is a quasi-coherent `𝒪_T`-module `𝓕` whose associated module is
that restriction.  So on affine charts a quasi-coherent module on an algebraic space *is* a
quasi-coherent module on a scheme, and results about the latter may be read on the former.

## Main definitions

* `AlgebraicGeometry.Space.representedModuleEquivalence` is the equivalence between the modules
  on the small étale site of the scheme underlying an object `U` of the big fppf site and the
  modules on the small étale site of the algebraic space `yoneda.obj U`.  Its functor is
  `AlgebraicGeometry.Space.representedModulePushforward` and its inverse is
  `AlgebraicGeometry.Space.representedModuleRestriction`.
* `AlgebraicGeometry.Space.representedAssociatedModuleQcoh` is the comparison
  `AlgebraicGeometry.Space.representedAssociatedModule` restricted to the quasi-coherent modules
  of the representing scheme, and
  `AlgebraicGeometry.Space.fullyFaithfulRepresentedAssociatedModuleQcoh` is its full
  faithfulness.
* `AlgebraicGeometry.Space.isoOfRepresentedAssociatedModuleIso` is the resulting uniqueness: two
  quasi-coherent modules on the representing scheme with isomorphic readings on the algebraic
  space are isomorphic.

## Main results

* `AlgebraicGeometry.Space.hasGlobalPresentation_representedModuleRestriction`: a global
  presentation of a module on the small étale site of `yoneda.obj U` is carried to a global
  presentation of its reading on the small étale site of the representing scheme.
* `AlgebraicGeometry.Space.exists_isQuasicoherent_iso_representedAssociatedModule`: **a globally
  presented module on the small étale site of a represented algebraic space is the associated
  module of a quasi-coherent module on the representing scheme**, with no hypothesis.
* `AlgebraicGeometry.Space.exists_isQuasicoherent_iso_etaleModulePullback_of_isAffine`: **the
  comparison at an affine étale chart.**  The restriction of a quasi-coherent `𝒪_X`-module to an
  étale chart with affine underlying scheme `T` is the associated module of a quasi-coherent
  `𝒪_T`-module.
* `AlgebraicGeometry.Space.exists_isQuasicoherent_iso_over_of_isAffine`: the same statement read
  on the slice of the small étale site of `X` at the chart, which is the shape in which the
  restriction of a module to a chart usually appears.

Together, full faithfulness and the two existence statements say that on an affine étale chart
the quasi-coherent modules of the chart scheme and the restrictions of the quasi-coherent modules
of the algebraic space are the same thing: the comparison is injective on isomorphism classes, is
bijective on morphisms, and hits every such restriction.

## Implementation notes

The chain has three links, and each of the three is already available.

*From the space to the chart space.*  Restriction of a quasi-coherent `𝒪_X`-module to an affine
étale chart has a global presentation on the slice at the chart —
`AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isAffine`, which is Stacks 03DX for the
small étale ringed site of an algebraic space — and the comparison of Stacks 04M0 carries that
to a global presentation of the étale pullback on the whole small étale site of the chart space,
which is `AlgebraicGeometry.Space.hasGlobalPresentation_etaleModulePullback_chartToSpace`.

*From the chart space to the scheme.*  The chart space is the algebraic space represented by the
chart, and its small étale site is the small étale site of the underlying scheme, taken in the
big étale site carried by the same category of schemes:
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`.  That equivalence of sites matches
the two structure sheaves *on the nose*, both being the global regular functions on the same
scheme, so the induced comparison of module categories is an equivalence of categories, built
here as `SheafOfModules.pushforwardPushforwardEquivalence` from the two identity comparisons
`AlgebraicGeometry.Space.representedStructureMap` and
`AlgebraicGeometry.Space.representedStructureMapInverse`.  Its two coherence hypotheses hold by
`rfl`.  Being half of an equivalence, the transport preserves colimits and zero morphisms, which
is what `Stacks.SheafOfModules.hasGlobalPresentation_map` asks of it; as there, the transport is
taken twice, at the module universe and one above it, a global presentation living in the larger
one.

*From the scheme's small étale site to its Zariski site.*  A module on the small étale site of a
scheme with a global presentation is the associated module of a quasi-coherent module on the
Zariski site, and this is **unconditional**:
`AlgebraicGeometry.SmallEtale.exists_isQuasicoherent_iso_associatedModule_of_presentation`.  It
is the local step of the essential surjectivity half of Stacks 03DX (2) at `τ = étale`, and it is
unconditional precisely because the small étale site is essentially small, so that a global
presentation in the sense of Stacks 03DE (6) is a `SheafOfModules.Presentation`.

## Universes

Everything is at the module universe `u` of the structure rings, which is the universe of the
schemes.  That is forced from both ends and not a choice: the modules of Stacks 03LU, hence
`AlgebraicGeometry.Space.etaleModulePullback`, exist only at `u`, and
`AlgebraicGeometry.SmallEtale.associatedModule` is likewise a functor into
`SheafOfModules.{u}`.  The two small étale sites both have their objects in `Type (u + 1)` and
their morphisms in `Type u`, which is what lets one presentation be transported to the other:
`Stacks.SheafOfModules.hasGlobalPresentation_map` takes two sites in the same pair of universes,
and the auxiliary transport therefore runs at `max (u + 1) u u u = u + 1`.  Nothing here touches
the universe `u + 1` of an abelian category of sheaves, so the obstruction that blocks the route
through Stacks 04E5 does not arise.

## What is not proved

This is *not* Descent, Proposition 03DX (2).  That clause asserts an equivalence of categories
`QCoh(𝒪_T) ≌ QCoh(T_étale, 𝒪)`, and its essential surjectivity is still owed; see
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleEssSurjReduction.lean`.  What
is proved here is the comparison at a *globally presented* module, which on an **affine** chart
is every quasi-coherent one.  Nothing below carries a `stacks` attribute.

Neither is this a comparison with `AlgebraicGeometry.Space.restrictToChartScheme`, the restriction
of an `𝒪_X`-module to the *Zariski* site of the chart scheme.  Identifying the quasi-coherent
`𝒪_T`-module produced below with that restriction is a separate statement and is not made: the
restriction is a Zariski sheafification of the sections over the Zariski opens of the chart, and
nothing in the tree computes its sections.  Consequently the comparison here does not yet
discharge the quasi-coherence gap recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestriction.lean`, nor the one recorded in the
"What this does not give" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionQuasicoherent.lean`.

The chart is affine because that is where Stacks 03DX supplies a *global* presentation.  On a
general étale chart the restriction is only locally presented, and globalising it over a covering
of the chart is the globalization step
`AlgebraicGeometry.SmallEtale.EssImageAssociatedModuleGlue`, equivalent to the essential
surjectivity that is owed.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u t

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The equivalence of module categories of a represented algebraic space -/

section Represented

variable (U : BigFppfOver B S hS)

/-- The first coherence identity of the two structure-sheaf comparisons of
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`.  Both comparisons are identities and
the counit of the equivalence does not move the underlying scheme of an object, so both sides are
the identity. -/
theorem representedStructureMap_counit_whiskerRight :
    Functor.whiskerRight (NatTrans.op (representedSmallEtaleEquivalence B S hS U).counit)
        (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj =
      (representedStructureMapInverse B S hS U).hom ≫
        (representedSmallEtaleEquivalence B S hS U).inverse.op.whiskerLeft
          (representedStructureMap B S hS U).hom := by
  ext : 2
  exact rfl

/-- The second coherence identity of the two structure-sheaf comparisons of
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`. -/
theorem representedStructureMap_unit_whiskerRight :
    (representedStructureMap B S hS U).hom ≫
        (representedSmallEtaleEquivalence B S hS U).functor.op.whiskerLeft
          (representedStructureMapInverse B S hS U).hom ≫
        Functor.whiskerRight (NatTrans.op (representedSmallEtaleEquivalence B S hS U).unit)
          (ringStructureSheaf B S hS (yoneda.obj U)).obj =
      𝟙 (ringStructureSheaf B S hS (yoneda.obj U)).obj := by
  ext : 2
  exact rfl

/-- **The modules on the small étale site of a represented algebraic space are the modules on the
small étale site of the representing scheme.**  The equivalence of sites of
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` matches the two structure sheaves on
the nose, so the two transports of modules along it,
`AlgebraicGeometry.Space.representedModulePushforward` and
`AlgebraicGeometry.Space.representedModuleRestriction`, are mutually inverse. -/
noncomputable def representedModuleEquivalence :
    SheafOfModules.{t} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ≌
      SheafOfModules.{t} (ringStructureSheaf B S hS (yoneda.obj U)) :=
  SheafOfModules.pushforwardPushforwardEquivalence
    (representedSmallEtaleEquivalence B S hS U)
    (representedStructureMap B S hS U) (representedStructureMapInverse B S hS U)
    (representedStructureMap_counit_whiskerRight B S hS U)
    (representedStructureMap_unit_whiskerRight B S hS U)

/-- The functor of `AlgebraicGeometry.Space.representedModuleEquivalence` is
`AlgebraicGeometry.Space.representedModulePushforward`. -/
theorem representedModuleEquivalence_functor :
    (representedModuleEquivalence.{u, u} B S hS U).functor =
      representedModulePushforward B S hS U :=
  rfl

/-- The inverse of `AlgebraicGeometry.Space.representedModuleEquivalence` is
`AlgebraicGeometry.Space.representedModuleRestriction`. -/
theorem representedModuleEquivalence_inverse :
    (representedModuleEquivalence.{u, u} B S hS U).inverse =
      representedModuleRestriction B S hS U :=
  rfl

/-- **A global presentation is carried to the small étale site of the representing scheme.**  If a
module on the small étale site of `yoneda.obj U` has a global presentation, so does its reading on
the small étale site of the scheme underlying `U`.

The reading is half of the equivalence
`AlgebraicGeometry.Space.representedModuleEquivalence`, hence a left adjoint, hence preserves the
coproducts and the cokernel of a presentation; it is zero-preserving on sections by construction,
and it commutes with raising the universe of the sections because both sides have the same
sections over every object. -/
theorem hasGlobalPresentation_representedModuleRestriction
    (N : SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U)))
    (h : N.HasGlobalPresentation) :
    ((representedModuleRestriction B S hS U).obj N).HasGlobalPresentation := by
  let ψ := representedStructureMapInverse B S hS U
  let F₀ := SheafOfModules.pushforward.{u} ψ
  let F := SheafOfModules.pushforward.{u + 1} ψ
  have hFadj : F.IsLeftAdjoint :=
    (representedModuleEquivalence.{u, u + 1} B S hS U).symm.isLeftAdjoint_functor
  exact Stacks.SheafOfModules.hasGlobalPresentation_map (F₀ := F₀) (F := F) _
    (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} ψ
      (SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U))))
    (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} ψ N) h

/-- **A globally presented module on a represented algebraic space comes from a quasi-coherent
module on the representing scheme**, with no hypothesis.

Transport the presentation to the small étale site of the representing scheme along
`AlgebraicGeometry.Space.representedModuleEquivalence`, where a globally presented module is the
associated module of a quasi-coherent module on the Zariski site —
`AlgebraicGeometry.SmallEtale.exists_isQuasicoherent_iso_associatedModule_of_presentation`, the
unconditional local step of Stacks 03DX (2) at `τ = étale` — and transport the resulting
isomorphism back. -/
theorem exists_isQuasicoherent_iso_representedAssociatedModule
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (N : Modules.{u, u} B S hS (yoneda.obj U) hU) (h : N.HasGlobalPresentation) :
    ∃ G : ((BigFppfOver.toScheme B S hS).obj U).Modules, G.IsQuasicoherent ∧
      Nonempty ((representedAssociatedModule B S hS U hU).obj G ≅ N) := by
  obtain ⟨G, hG, ⟨e⟩⟩ :=
    _root_.AlgebraicGeometry.SmallEtale.exists_isQuasicoherent_iso_associatedModule_of_presentation
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
      (Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation
        (hasGlobalPresentation_representedModuleRestriction B S hS U N h)).some
  exact ⟨G, hG, ⟨(representedModulePushforward B S hS U).mapIso e ≪≫
    (representedModuleEquivalence.{u, u} B S hS U).counitIso.app N⟩⟩

/-! ### Full faithfulness of the comparison -/

/-- The comparison `AlgebraicGeometry.Space.representedAssociatedModule` restricted to the
quasi-coherent modules of the representing scheme: the functor
`QCoh(𝒪_T) ⥤ Mod(yoneda.obj U, 𝒪)` of Stacks 06VE at `τ = étale`, followed by the transport of
modules along the equivalence of small étale sites. -/
noncomputable def representedAssociatedModuleQcoh :
    (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U)) :=
  _root_.AlgebraicGeometry.SmallEtale.associatedModuleQcoh (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    representedModulePushforward B S hS U

/-- The corestricted comparison agrees with
`AlgebraicGeometry.Space.representedAssociatedModule` on objects. -/
theorem representedAssociatedModuleQcoh_obj (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (G : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hG : G.IsQuasicoherent) :
    (representedAssociatedModuleQcoh B S hS U).obj ⟨G, hG⟩ =
      (representedAssociatedModule B S hS U hU).obj G :=
  rfl

/-- **The comparison is fully faithful on quasi-coherent modules**, with no hypothesis.

This is what makes the comparison a transport of theorems and not merely a construction: a
morphism between the readings on the algebraic space of two quasi-coherent `𝒪_T`-modules is the
reading of a unique morphism of `𝒪_T`-modules.  Its two factors are fully faithful for
independent reasons — the first is
`AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'`, the small-site half of
Stacks 0GN7 at `τ = étale`, and the second is half of the equivalence
`AlgebraicGeometry.Space.representedModuleEquivalence`. -/
noncomputable def fullyFaithfulRepresentedAssociatedModuleQcoh :
    (representedAssociatedModuleQcoh B S hS U).FullyFaithful :=
  (_root_.AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property).comp
    (representedModuleEquivalence.{u, u} B S hS U).fullyFaithfulFunctor

/-- **The quasi-coherent module on the representing scheme is unique up to isomorphism.**  Two
quasi-coherent `𝒪_T`-modules whose readings on the small étale site of `yoneda.obj U` are
isomorphic are themselves isomorphic.

Together with
`AlgebraicGeometry.Space.exists_isQuasicoherent_iso_representedAssociatedModule` this makes the
passage from a globally presented module on a represented algebraic space to a quasi-coherent
module on the representing scheme well defined up to isomorphism. -/
noncomputable def isoOfRepresentedAssociatedModuleIso
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    {G G' : ((BigFppfOver.toScheme B S hS).obj U).Modules}
    (hG : G.IsQuasicoherent) (hG' : G'.IsQuasicoherent)
    (e : (representedAssociatedModule B S hS U hU).obj G ≅
      (representedAssociatedModule B S hS U hU).obj G') :
    G ≅ G' :=
  (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).ι.mapIso
    ((fullyFaithfulRepresentedAssociatedModuleQcoh B S hS U).preimageIso
      (X := ⟨G, hG⟩) (Y := ⟨G', hG'⟩) e)

end Represented

/-! ### The comparison at an affine étale chart -/

section Chart

variable (X : AlgebraicSpaces B S hS)

/-- **The comparison of modules at an affine étale chart.**  Let `M` be a quasi-coherent
`𝒪_X`-module and let `W` be an étale chart of `X` whose underlying scheme `T` is affine.  Then
there is a quasi-coherent `𝒪_T`-module `𝓕` whose associated module on the small étale site of the
chart space is the pullback of `M` to that chart space.

This is the comparison the development was missing: `AlgebraicGeometry.Scheme.Modules` of the
chart and `AlgebraicGeometry.Space.Modules` of the algebraic space are matched up at the
restriction of a quasi-coherent module, with no hypothesis.  Stacks 03DX for the small étale
ringed site of `X` presents `M` globally on an affine chart, and a globally presented module on a
represented algebraic space comes from a quasi-coherent module on the representing scheme. -/
theorem exists_isQuasicoherent_iso_etaleModulePullback_of_isAffine
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W))) :
    ∃ G : ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj W)).Modules, G.IsQuasicoherent ∧
      Nonempty ((representedAssociatedModule B S hS
          ((SmallEtale.toOver B S hS X.1).obj W) (chartSpace B S hS X W).2).obj G ≅
        (etaleModulePullback B S hS (chartToSpace B S hS X W)
          (isEtale_chartToSpace B S hS X W)).obj M) :=
  exists_isQuasicoherent_iso_representedAssociatedModule B S hS
    ((SmallEtale.toOver B S hS X.1).obj W) (chartSpace B S hS X W).2 _
    (hasGlobalPresentation_etaleModulePullback_chartToSpace B S hS X M W
      (hasGlobalPresentation_over_of_isAffine B S hS X M hM W hW))

/-- **The comparison of modules at an affine étale chart, read on the slice.**  The restriction of
a quasi-coherent `𝒪_X`-module to the slice of the small étale site of `X` at an étale chart with
affine underlying scheme `T` is, through the comparison of Stacks 04M0, the associated module of a
quasi-coherent `𝒪_T`-module.

This is `AlgebraicGeometry.Space.exists_isQuasicoherent_iso_etaleModulePullback_of_isAffine` with
the pullback to the chart space replaced by the restriction to the slice; the two agree by
`AlgebraicGeometry.Space.chartSmallEtaleRestriction`, which is the pullback on the nose. -/
theorem exists_isQuasicoherent_iso_over_of_isAffine
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W))) :
    ∃ G : ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj W)).Modules, G.IsQuasicoherent ∧
      Nonempty ((representedAssociatedModule B S hS
          ((SmallEtale.toOver B S hS X.1).obj W) (chartSpace B S hS X W).2).obj G ≅
        chartSmallEtaleRestriction B S hS X M W) :=
  exists_isQuasicoherent_iso_etaleModulePullback_of_isAffine B S hS X M hM W hW

end Chart

end AlgebraicGeometry.Space

end
