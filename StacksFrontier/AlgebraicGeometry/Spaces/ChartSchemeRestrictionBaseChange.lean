module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.RingedTopos
public import StacksFrontier.AlgebraicGeometry.AmpleLocallyClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorQuasicoherent

/-!
# Base change of the Zariski restriction of a module to a chart scheme

Let `B` be a big fppf site containing a scheme `S` and let `U` be an object of the big fppf
category over `S`, with underlying scheme `T`.  The identity of `yoneda.obj U` is an étale chart
of that algebraic space whose underlying scheme is `T`, and
`AlgebraicGeometry.Space.restrictToChartScheme` at that chart carries an `𝒪`-module on the small
étale site of `yoneda.obj U` to a module on the Zariski site of `T`.

This file identifies that restriction with the right adjoint of the associated-module functor of
the small étale site of `T`, read across the identification of the small étale site of
`yoneda.obj U` with the small étale site of `T`, and deduces that for a quasi-coherent module the
restriction commutes with base change along a morphism of the big fppf category.  Applied to the
inverse image of an invertible module it gives the compatibility of
`AlgebraicGeometry.Space.baseChangeModule`, the module Stacks 0D31 is phrased with, under base
change of the chart.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeRestrictionSheafHom` is the morphism of sheaves of rings
  along which the restriction to a chart scheme extends scalars, read on sheaves rather than on
  presheaves, and `AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` presents the
  restriction as the direct image along it.
* `AlgebraicGeometry.Space.selfOpensFunctor` reads a Zariski open of `T` as an étale chart of
  `yoneda.obj U` through the identification of the two small étale sites, and
  `AlgebraicGeometry.Space.selfOpensStructureMap` is its structure map.
* `AlgebraicGeometry.Space.associatedModuleRestrictModuleIsoSelf` and
  `AlgebraicGeometry.Space.restrictModuleAssociatedModuleIsoSelf` are the counit and the unit of
  the associated-module adjunction of Stacks 03DU at a quasi-coherent module, as isomorphisms:
  a quasi-coherent module on the small étale site of `T` is the associated module of its own
  Zariski restriction, and a quasi-coherent Zariski module on `T` is the Zariski restriction of
  its own associated module.
* `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIsoHead` is every factor of
  `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso` except the last — the last being
  the only one which is an image of the Zariski pullback functor.

## Main results

* `AlgebraicGeometry.Space.selfOpensFunctor_obj`: the two readings of a Zariski open of `T` as an
  étale chart of `yoneda.obj U` — through the identification of the two small étale sites and
  directly, by `AlgebraicGeometry.Space.openChart` — agree.
* `AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`: **the restriction of an
  `𝒪`-module on `yoneda.obj U` to the Zariski site of `T` along the identity chart is its
  restriction along the inclusion of the small Zariski site of `T` into the small étale site of
  `T`**, that is, the right adjoint of the associated-module functor of Stacks 03DU applied to the
  module read on the small étale site of `T`.
* `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`: **for a quasi-coherent module the
  restriction commutes with base change.**  For `r : U' ⟶ U` the restriction to `T'` of the
  inverse image of Stacks 03LU is the Zariski pullback along the underlying morphism of schemes
  of the restriction to `T`.  This is the isomorphism itself, as data;
  `AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent` is its
  existence statement, kept because most consumers need no more than that.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isInvertible`: the inverse
  image of Stacks 03LU of an invertible module is quasi-coherent.
* `AlgebraicGeometry.Space.nonempty_baseChangeModule_baseChange_of_isInvertible`: **the
  chart-scheme reading of an invertible module commutes with base change of the chart.**  For an
  invertible `𝒪_X`-module `L`, a morphism `p : yoneda.obj U ⟶ X` and a morphism `r : U' ⟶ U` of
  schemes over the base, the reading of `L` on `U'` along `yoneda.map r ≫ p` is the pullback along
  `r` of its reading on `U`.

## Implementation notes

**The restriction to a chart scheme is a direct image.**  By construction it is the Zariski
sheafification of the restriction of sections along `AlgebraicGeometry.Space.openChartFunctor`,
with scalars extended along `AlgebraicGeometry.Space.chartSchemeRestrictionRingHom`.  Once that
index functor is known to be continuous the restricted presheaf is already a sheaf, so the
sheafification is the counit of `CategoryTheory.PresheafOfModules.sheafificationAdjunction`, which
is an isomorphism; the universe lift of the sections is undone by
`SheafOfModules.uliftForPresentationSelfIso`, the module universe being the universe of the
schemes.  That is
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward`, and it holds at any étale chart
whose index functor is continuous.

**Continuity of the index functor at the identity chart** comes from the identification of
`AlgebraicGeometry.Space.openChartFunctor` with
`AlgebraicGeometry.Space.selfOpensFunctor`, which is continuous as a composite.  The two agree on
objects — `AlgebraicGeometry.Space.selfOpensFunctor_obj`, where the sole discrepancy is that
`AlgebraicGeometry.Space.openSub` takes the open immersion into the size-bounded category of
schemes with `CategoryTheory.Functor.preimage` while
`AlgebraicGeometry.BigEtaleOver.opensObj` takes it with `CategoryTheory.ObjectProperty.homMk` —
and the naturality of the resulting isomorphism needs no computation: a morphism of the small
étale site into the chart cut out by a Zariski open is unique, the structure morphism of such a
chart being a monomorphism.

**The comparison of the two direct images is assembled from
`CategoryTheory.SheafOfModules.pushforwardCongr₂`**, whose compatibility of structure maps reduces
over a Zariski open to the statement that the two comparison maps of structure sheaves which
belong to the identification of the sites carry no information: the counit of the identification
at a Zariski open is the identity, again by uniqueness of morphisms into it, and the component of
the identification of the index functors is a map of global regular functions on one and the same
scheme.  The structure map of the identity chart's restriction is then the structure map of the
morphism of small étale ringed sites of Stacks 03DU on the nose.

**The continuity instances are passed positionally.**  The small étale topology of `T` admits two
definitionally equal spellings — `AlgebraicGeometry.Space.chartScheme` of the identity chart and
the scheme underlying `U` — and instance resolution runs at reducible transparency, so a
composite mixing the two has continuity instances that no statement of them can be found by; the
composite of this file is therefore given its instance by passing the two component instances to
`CategoryTheory.Functor.isContinuous_comp`.  For the same reason
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` takes the continuity of its index
functor as an instance argument of its section rather than finding it: the functor is implicit in
the type of `CategoryTheory.SheafOfModules.pushforward`, so a global instance is sought before it
is known.

**The factors of the base-change isomorphism are named declarations.**  The two adjunction maps
the construction passes through used to be `have`-bound `asIso`s inside it, which made the
composite unpeelable: an adjunct of a composite is taken factor by factor, and a factor with no
name cannot be mentioned in the statement of what its adjunct is.  They are now
`AlgebraicGeometry.Space.associatedModuleRestrictModuleIsoSelf` and
`AlgebraicGeometry.Space.restrictModuleAssociatedModuleIsoSelf`, the quasi-coherence facts
feeding them are
`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleModuleInverse` and
`AlgebraicGeometry.Space.isQuasicoherent_restrictModule_representedSmallEtaleModuleInverse`, and
the composite is grouped as
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIsoHead` followed by its one
pullback-image factor.  The grouping is at the level of isomorphisms, where `≪≫` is
right-nested and the regrouping of a head and a single trailing factor costs nothing; writing a
factor out with `≫` instead exhausts the recursion depth, the middle object having to be unified
at two spellings of the scheme underlying `U`.

**Quasi-coherence of the inverse image of an invertible module** comes from invertibility of the
inverse image, Stacks 0B8P in the ringed-topos form
`Stacks.SheafOfModules.isInvertible_pullbackModules_obj`, together with
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isInvertible`; the two invertibility predicates
of the development are matched by `Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry`.  This
needs nothing about the morphism along which the inverse image is taken.

No declaration here carries a `stacks` tag: the results are inputs to Stacks 0D32, not assertions
of a tag, and the clauses of Stacks 03DU, 03DX and 03LU used are already covered in the tree.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The restriction to a chart scheme as a direct image -/

section Chart

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (A : SmallEtale B S hS F)
    [(openChartFunctor B S hS F A).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme A)) (SmallEtale.topology B S hS F)]

/-- The morphism of sheaves of rings along which the restriction of an `𝒪_F`-module to the scheme
of an étale chart `A` extends scalars: over a Zariski open of `chartScheme A` it is pullback of
regular functions along the inclusion of that open, read as a chart of `F`.

This is `AlgebraicGeometry.Space.chartSchemeRestrictionRingHom`, which the restriction is built
from, read as a morphism of sheaves over the continuous index functor. -/
def chartSchemeRestrictionSheafHom :
    (chartScheme A).ringCatSheaf ⟶
      ((openChartFunctor B S hS F A).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(chartScheme A)) (SmallEtale.topology B S hS F)).obj
        (smallEtaleRingSheaf B S hS F hF) :=
  ⟨chartSchemeRestrictionRingHom B S hS F A⟩

/-- **The restriction of an `𝒪_F`-module to the scheme of an étale chart is a direct image.**  For
a chart whose index functor is continuous, the restriction is the direct image of the module along
that functor and `AlgebraicGeometry.Space.chartSchemeRestrictionSheafHom`.

The restriction raises the universe of the sections, restricts them along the index functor,
extends scalars and sheafifies for the Zariski topology.  The universe lift is undone by
`SheafOfModules.uliftForPresentationSelfIso`, the module universe being the universe of the
schemes, and the restricted presheaf is already a sheaf, so the sheafification is the counit of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction`. -/
def restrictToChartSchemeIsoPushforward (N : Modules.{u, u} B S hS F hF) :
    restrictToChartScheme B S hS F hF N A ≅
      (SheafOfModules.pushforward.{u} (chartSchemeRestrictionSheafHom B S hS hF A)).obj N :=
  (PresheafOfModules.sheafification (𝟙 (chartScheme A).ringCatSheaf.obj)).mapIso
      ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F A)).mapIso
        ((SheafOfModules.forget _).mapIso (SheafOfModules.uliftForPresentationSelfIso N))) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (chartScheme A).ringCatSheaf.obj)).counit).app
      ((SheafOfModules.pushforward.{u} (chartSchemeRestrictionSheafHom B S hS hF A)).obj N)

end Chart

/-! ### The identity chart of a represented algebraic space -/

section Represented

variable (U : BigFppfOver B S hS)

/-- A Zariski open of the scheme underlying `U`, read as an étale chart of `yoneda.obj U` through
the identification of the small étale site of `yoneda.obj U` with the small étale site of that
scheme. -/
abbrev selfOpensFunctor :
    (chartScheme (idEtaleChart B S hS U)).Opens ⥤ SmallEtale B S hS (yoneda.obj U) :=
  _root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    (representedSmallEtaleEquivalence B S hS U).inverse

/-- **The two readings of a Zariski open of the scheme underlying `U` as an étale chart of
`yoneda.obj U` agree**: the one through the identification of the two small étale sites and the
direct one, `AlgebraicGeometry.Space.openChart` at the identity chart.

The two differ only in how the open immersion is taken into the size-bounded category of schemes:
`AlgebraicGeometry.Space.openSub` uses `CategoryTheory.Functor.preimage` and
`AlgebraicGeometry.BigEtaleOver.opensObj` uses `CategoryTheory.ObjectProperty.homMk`.  They agree
because the inclusion is faithful. -/
theorem selfOpensFunctor_obj (O : (chartScheme (idEtaleChart B S hS U)).Opens) :
    (selfOpensFunctor B S hS U).obj O =
      (openChartFunctor B S hS (yoneda.obj U) (idEtaleChart B S hS U)).obj O :=
  Stacks.CategoryTheory.fullSubcategory_eq_of_obj_eq
    (congrArg (fun g => CostructuredArrow.mk
        (yoneda.map (Over.homMk (V := U) (U := Over.mk (g ≫ U.hom)) g (w := rfl)) ≫
          𝟙 (yoneda.obj U)))
      (B.inclusion.map_injective (B.inclusion.map_preimage _).symm))

/-- A morphism of the small étale site of `yoneda.obj U` into the chart cut out by a Zariski open
of the scheme underlying `U` is unique: morphisms into such a chart correspond, across the
identification of the two small étale sites, to morphisms into an open of that scheme, whose
structure morphism is a monomorphism. -/
instance subsingleton_hom_selfOpensFunctor (P : SmallEtale B S hS (yoneda.obj U))
    (O : (chartScheme (idEtaleChart B S hS U)).Opens) :
    Subsingleton (P ⟶ (selfOpensFunctor B S hS U).obj O) :=
  haveI : Subsingleton ((representedSmallEtaleEquivalence B S hS U).functor.obj P ⟶
      _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property O) :=
    _root_.AlgebraicGeometry.SmallEtale.subsingleton_hom_opensToSmallEtale
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property _ O
  (((representedSmallEtaleEquivalence B S hS U).toAdjunction.homEquiv P
    (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property O)).symm).subsingleton

/-- The identification of the two readings of a Zariski open of the scheme underlying `U` as an
étale chart of `yoneda.obj U`, as an isomorphism of functors.  Its naturality needs no
computation: morphisms into the chart cut out by a Zariski open are unique. -/
def selfOpensFunctorIso :
    openChartFunctor B S hS (yoneda.obj U) (idEtaleChart B S hS U) ≅ selfOpensFunctor B S hS U :=
  NatIso.ofComponents (fun O => eqToIso (selfOpensFunctor_obj B S hS U O).symm)
    (fun _ => @Subsingleton.elim _ (subsingleton_hom_selfOpensFunctor B S hS U _ _) _ _)

/-- Reading a Zariski open of the scheme underlying `U` as an étale chart of `yoneda.obj U`
through the identification of the two small étale sites is continuous: it is the composite of the
inclusion of the small Zariski site into the small étale site of the scheme with the inverse of
the identification. -/
instance isContinuous_selfOpensFunctor :
    (selfOpensFunctor B S hS U).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS U)))
      (SmallEtale.topology B S hS (yoneda.obj U)) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
    (_root_.AlgebraicGeometry.SmallEtale.isContinuous_opensToSmallEtale
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (isContinuous_representedSmallEtaleEquivalence_inverse B S hS U)

/-- The index functor of the restriction to the scheme of the identity chart of `yoneda.obj U` is
continuous: it is isomorphic to `AlgebraicGeometry.Space.selfOpensFunctor`. -/
instance isContinuous_openChartFunctor_idEtaleChart :
    (openChartFunctor B S hS (yoneda.obj U) (idEtaleChart B S hS U)).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS U)))
      (SmallEtale.topology B S hS (yoneda.obj U)) :=
  Functor.isContinuous_of_iso (selfOpensFunctorIso B S hS U).symm _ _

/-- The structure map of `AlgebraicGeometry.Space.selfOpensFunctor`: the structure map of the
morphism of small étale ringed sites of Stacks 03DU of the scheme underlying `U`, followed by the
structure comparison of the inverse of the identification of the two small étale sites. -/
def selfOpensStructureMap :
    (chartScheme (idEtaleChart B S hS U)).ringCatSheaf ⟶
      ((selfOpensFunctor B S hS U).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS U)))
          (SmallEtale.topology B S hS (yoneda.obj U))).obj
        (representedStructureRingSheaf B S hS U) :=
  _root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ≫
    ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology ↥((BigFppfOver.toScheme B S hS).obj U))
      (representedSchemeSmallEtaleTopology B S hS U)).map
      (Stacks.SheafOfModules.reindexBackSharp
        (J' := SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeStructureSheaf B S hS U))

/-- Restricting an `𝒪`-module on the small étale site of the scheme underlying `U` along the
inclusion of the small Zariski site is reading it on the small étale site of `yoneda.obj U` and
taking the direct image along `AlgebraicGeometry.Space.selfOpensFunctor`: the direct images along
a composite of two morphisms of ringed sites compose. -/
def selfOpensPushforwardIso
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N) ≅
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj N :=
  (SheafOfModules.pushforwardComp.{u}
    (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (Stacks.SheafOfModules.reindexBackSharp
      (J' := SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeStructureSheaf B S hS U))).app N

/-- **The restriction of an `𝒪`-module on `yoneda.obj U` to the Zariski site of the scheme
underlying `U` along the identity chart is the right adjoint of the associated-module functor of
Stacks 03DU**, applied to the module read on the small étale site of that scheme.

Both sides are direct images: the left along the index functor of the restriction, the right along
the inclusion of the small Zariski site followed by the identification of the two small étale
sites.  The two index functors are identified by
`AlgebraicGeometry.Space.selfOpensFunctorIso`, compatibly with the two structure maps. -/
def restrictToChartSchemeIdEtaleChartIso
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)) :
    restrictToChartScheme B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) N (idEtaleChart B S hS U) ≅
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N) := by
  haveI := isContinuous_openChartFunctor_idEtaleChart B S hS U
  refine restrictToChartSchemeIsoPushforward B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U) N ≪≫ ?_
  refine ((SheafOfModules.pushforwardCongr₂ (selfOpensStructureMap B S hS U)
      (ψ := chartSchemeRestrictionSheafHom B S hS
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) (idEtaleChart B S hS U))
      (selfOpensFunctorIso B S hS U) ?_).app N).symm ≪≫
    (selfOpensPushforwardIso B S hS U N).symm
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun O => ?_)
  have h1 : (representedSmallEtaleEquivalence B S hS U).counit.app
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property O.unop) = 𝟙 _ :=
    @Subsingleton.elim _ (_root_.AlgebraicGeometry.SmallEtale.subsingleton_hom_opensToSmallEtale
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property _ O.unop)
      _ _
  have h2 : ((((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥((BigFppfOver.toScheme B S hS).obj U))
        (representedSchemeSmallEtaleTopology B S hS U)).map
        (Stacks.SheafOfModules.reindexBackSharp
          (J' := SmallEtale.topology B S hS (yoneda.obj U))
          (representedSmallEtaleEquivalence B S hS U)
          (representedSchemeStructureSheaf B S hS U))).hom.app O) = 𝟙 _ := by
    change (representedSchemeStructureSheaf B S hS U).obj.map
        ((representedSmallEtaleEquivalence B S hS U).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property O.unop)).op = 𝟙 _
    exact (congrArg (fun k => (representedSchemeStructureSheaf B S hS U).obj.map
          (Quiver.Hom.op k)) h1).trans
      ((congrArg (representedSchemeStructureSheaf B S hS U).obj.map op_id).trans
        ((representedSchemeStructureSheaf B S hS U).obj.map_id _))
  have h3 : ((Functor.sheafPushforwardContinuousNatTrans (selfOpensFunctorIso B S hS U).hom
        RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS U)))
        (SmallEtale.topology B S hS (yoneda.obj U))).app
        (representedStructureRingSheaf B S hS U)).hom.app O = 𝟙 _ := by
    change (representedStructureRingSheaf B S hS U).obj.map
      (eqToHom (selfOpensFunctor_obj B S hS U O.unop).symm).op = 𝟙 _
    exact (congrArg (representedStructureRingSheaf B S hS U).obj.map (eqToHom_op _)).trans
      ((eqToHom_map (representedStructureRingSheaf B S hS U).obj _).trans rfl)
  change (_ ≫ _) ≫ _ = _
  rw [h2, h3]
  exact (Category.comp_id _).trans (Category.comp_id _)

end Represented

/-! ### Base change -/

section BaseChange

variable {B S hS}

/-! ### The factors of the base-change isomorphism -/

/-- **A quasi-coherent `𝒪`-module on `yoneda.obj U`, read on the small étale site of the scheme
underlying `U`, is quasi-coherent.**  Quasi-coherence is invariant under the identification of
the two small étale sites, and the module read back is the original up to the counit of that
identification. -/
theorem isQuasicoherentOnSite_representedSmallEtaleModuleInverse {U : BigFppfOver B S hS}
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) :
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)).1
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app N).symm hN)

/-- **The Zariski restriction of a quasi-coherent `𝒪`-module on `yoneda.obj U` to the scheme
underlying `U` is quasi-coherent.**  This is the target of
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`, so it is quasi-coherence of the
restriction to the scheme of the identity chart read across that identification. -/
theorem isQuasicoherent_restrictModule_representedSmallEtaleModuleInverse
    {U : BigFppfOver B S hS}
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)) :=
  _root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)
    (isQuasicoherentOnSite_representedSmallEtaleModuleInverse N hN)

/-- **A quasi-coherent module on the small étale site of the scheme underlying `U` is the
associated module of its own Zariski restriction.**  This is the counit of the Stacks 03DU
adjunction, which is an isomorphism at a quasi-coherent module by
`AlgebraicGeometry.SmallEtale.isIso_counit`, whose second hypothesis — quasi-coherence of the
restriction — is `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`.

It is named because it is a factor of
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`: a factor written as
`asIso` of an `IsIso` inside that construction cannot be peeled off the adjunct of the
composite, there being nothing to name it by. -/
def associatedModuleRestrictModuleIsoSelf {U : BigFppfOver B S hS}
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U))
    (hM : M.IsQuasicoherentOnSite) :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M) ≅ M :=
  @asIso _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.isIso_counit (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property M hM
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property M hM))

/-- **A quasi-coherent Zariski module on the scheme underlying `U` is the Zariski restriction of
its own associated module.**  This is the unit of the Stacks 03DU adjunction, an isomorphism at a
quasi-coherent module by `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`.

It is named for the same reason as
`AlgebraicGeometry.Space.associatedModuleRestrictModuleIsoSelf`: it is a factor of
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`. -/
def restrictModuleAssociatedModuleIsoSelf {U : BigFppfOver B S hS}
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (h𝓕 : SheafOfModules.IsQuasicoherent 𝓕) :
    𝓕 ≅ (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj 𝓕) :=
  @asIso _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⟨𝓕, h𝓕⟩)

/-- **Every factor of `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso` except the
last.**  The last factor of that isomorphism is the only one which is an image of the Zariski
pullback functor; this is the five-fold composite in front of it, landing in the Zariski pullback
of the restriction of `N` read on the small étale site of the scheme underlying `U`.

The five factors are, in order: the identification of `N` with the associated module of its own
Zariski restriction, carried along the inverse image of Stacks 03LU
(`AlgebraicGeometry.Space.associatedModuleRestrictModuleIsoSelf`, under the counit of the
identification of the two small étale sites); the commutation of the associated module with
pullback, `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`; the reading of the
restriction to the scheme of the identity chart as a Zariski restriction,
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`; the unit of the identification of
the two small étale sites of the scheme underlying `U'`; and the unit of Stacks 03DU at the
Zariski pullback, `AlgebraicGeometry.Space.restrictModuleAssociatedModuleIsoSelf`.

It is named so that the adjunct of the base-change isomorphism can be peeled: a composite
`e ≪≫ f` with `f` an image of the pullback functor has, in its *inverse*, that image standing
alone in front, where `CategoryTheory.Adjunction.homEquiv_naturality_left` discharges it.  That
is `AlgebraicGeometry.Space.homEquiv_restrictToChartSchemeBaseChangeIso_inv` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionBaseChangeAdjunct.lean`. -/
def restrictToChartSchemeBaseChangeIsoHead
    {U' U : BigFppfOver B S hS} (r : U' ⟶ U)
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) :
    restrictToChartScheme B S hS (yoneda.obj U')
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U')
          ((modulePullback B S hS (representedSpaceMap B S hS r)).obj N)
          (idEtaleChart B S hS U') ≅
        (AlgebraicGeometry.Scheme.Modules.pullback (B.inclusion.map r.left)).obj
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)) :=
  (restrictToChartSchemeFunctor B S hS (yoneda.obj U')
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U') (idEtaleChart B S hS U')).mapIso
      ((modulePullback B S hS (representedSpaceMap B S hS r)).mapIso
        (((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app N).symm ≪≫
          (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
            (associatedModuleRestrictModuleIsoSelf
              ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)
              (isQuasicoherentOnSite_representedSmallEtaleModuleInverse N hN)).symm)) ≪≫
    (restrictToChartSchemeFunctor B S hS (yoneda.obj U')
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U') (idEtaleChart B S hS U')).mapIso
      (representedAssociatedModulePullbackIso B S hS r
        (relativelyRepresentable_yoneda_map B S hS r)
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N))) ≪≫
    restrictToChartSchemeIdEtaleChartIso B S hS U'
      ((representedSmallEtaleModuleEquivalence B S hS U').functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback (B.inclusion.map r.left)).obj
            ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
              ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N))))) ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS U').unitIso.app
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback (B.inclusion.map r.left)).obj
            ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
              ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N))))).symm ≪≫
    (restrictModuleAssociatedModuleIsoSelf
      ((AlgebraicGeometry.Scheme.Modules.pullback (B.inclusion.map r.left)).obj
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)))
      (Stacks.Modules.isQuasicoherent_pullback _ _
        (isQuasicoherent_restrictModule_representedSmallEtaleModuleInverse N hN))).symm

/-- **For a quasi-coherent module the restriction to the scheme of the identity chart commutes
with base change**, as data.  Let `r : U' ⟶ U` be a morphism of the big fppf category over `S`
and let `N` be a quasi-coherent `𝒪`-module on `yoneda.obj U`.  The restriction to the scheme
underlying `U'` of the inverse image of `N` of Stacks 03LU along the represented morphism is the
Zariski pullback, along the morphism of schemes underlying `r`, of the restriction of `N` to the
scheme underlying `U`.

A quasi-coherent module is the associated module of its own restriction, the counit of the
associated-module adjunction of Stacks 03DU being an isomorphism there, and the associated module
commutes with pullback by `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`.  The
Zariski pullback is again quasi-coherent, so the unit of that adjunction is an isomorphism at it
and the restriction of its associated module is itself.

**This is a named composite and not a choice.**  The isomorphism was previously produced only
inside the proof of
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent`, which
wrapped it in `Nonempty` and so discarded it; every consumer then recovered an isomorphism with
`Nonempty.some`, and a composite built from such a choice admits no description of its action on
sections.  Nothing about the construction needed choice: it is the six-fold composite displayed
below, and the only thing the quasi-coherence hypothesis supplies is that the two adjunction
maps it passes through are isomorphisms.

**Its factors are named.**  The first five are
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIsoHead`, assembled there from
`AlgebraicGeometry.Space.associatedModuleRestrictModuleIsoSelf` and
`AlgebraicGeometry.Space.restrictModuleAssociatedModuleIsoSelf` — the counit and the unit of
Stacks 03DU at a quasi-coherent module, which used to be `have`-bound `asIso`s inside this
construction and so could not be referred to.  The sixth stands alone here because it is the one
factor which is an image of the Zariski pullback functor, and in the *inverse* of this
isomorphism it therefore stands alone in front, where the adjunct discharges it for free. -/
def restrictToChartSchemeBaseChangeIso
    {U' U : BigFppfOver B S hS} (r : U' ⟶ U)
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) :
    restrictToChartScheme B S hS (yoneda.obj U')
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U')
          ((modulePullback B S hS (representedSpaceMap B S hS r)).obj N)
          (idEtaleChart B S hS U') ≅
        pullbackModule ((BigFppfOver.toScheme B S hS).map r)
          (restrictToChartScheme B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) N (idEtaleChart B S hS U)) :=
  restrictToChartSchemeBaseChangeIsoHead r N hN ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback (B.inclusion.map r.left)).mapIso
      (restrictToChartSchemeIdEtaleChartIso B S hS U N).symm

/-- **For a quasi-coherent module the restriction to the scheme of the identity chart commutes
with base change.**  This is the existence statement of
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`, which is the isomorphism itself and
is what a consumer that needs to say anything about the isomorphism should use. -/
theorem nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent
    {U' U : BigFppfOver B S hS} (r : U' ⟶ U)
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) :
    Nonempty (restrictToChartScheme B S hS (yoneda.obj U')
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U')
          ((modulePullback B S hS (representedSpaceMap B S hS r)).obj N)
          (idEtaleChart B S hS U') ≅
        pullbackModule ((BigFppfOver.toScheme B S hS).map r)
          (restrictToChartScheme B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) N (idEtaleChart B S hS U))) :=
  ⟨restrictToChartSchemeBaseChangeIso r N hN⟩

/-- **The inverse image of an invertible module is quasi-coherent.**  The inverse image of
Stacks 03LU of an invertible `𝒪_Y`-module along a morphism `f : X ⟶ Y` of algebraic spaces is
quasi-coherent, with no hypothesis on `f`.

The inverse image of an invertible module along a morphism of ringed topoi is invertible,
Stacks 0B8P, and an invertible module on the small étale site of an algebraic space is
quasi-coherent. -/
theorem isQuasicoherentOnSite_modulePullback_of_isInvertible
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (L : Modules.{u, u} B S hS Y.1 Y.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).property L) :
    ((modulePullback B S hS f).obj L).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isInvertible B S hS X _
    ((Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS f) (L := L) (hL := hL)).toAlgebraicGeometry
        _ _ _)

/-- **The chart-scheme reading of an invertible module commutes with base change of the chart.**
For an algebraic space `X` over the base, an invertible `𝒪_X`-module `L`, schemes `U` and `U'`
over the base, a morphism `p : yoneda.obj U ⟶ X` and a morphism `r : U' ⟶ U` of schemes, the
reading of `L` on `U'` along `yoneda.map r ≫ p` is the pullback along `r` of its reading on `U`
along `p`.

Both sides are `AlgebraicGeometry.Space.baseChangeModule`, the inverse image of Stacks 03LU
followed by restriction to the Zariski site of the chart.  Pulling back along the composite is
pulling back along `p` and then along `r`, by
`AlgebraicGeometry.Space.baseChangeModuleCompIso`; the inverse image of `L` along `p` is
quasi-coherent because `L` is invertible, and for a quasi-coherent module the restriction
commutes with base change. -/
theorem nonempty_baseChangeModule_baseChange_of_isInvertible
    {X : AlgebraicSpaces B S hS} (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (U U' : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1) (r : U' ⟶ U) :
    Nonempty (baseChangeModule B S hS L U' (yoneda.map r ≫ p) ≅
      pullbackModule ((BigFppfOver.toScheme B S hS).map r)
        (baseChangeModule B S hS L U p)) := by
  obtain ⟨e⟩ := nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent r
    ((modulePullback B S hS (ObjectProperty.homMk p :
      (⟨yoneda.obj U, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U⟩ :
        AlgebraicSpaces B S hS) ⟶ X)).obj L)
    (isQuasicoherentOnSite_modulePullback_of_isInvertible _ L hL)
  exact ⟨baseChangeModuleCompIso B S hS (ObjectProperty.homMk p :
    (⟨yoneda.obj U, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U⟩ :
      AlgebraicSpaces B S hS) ⟶ X) L U' (yoneda.map r) ≪≫ e⟩

end BaseChange

end AlgebraicGeometry.Space

end
