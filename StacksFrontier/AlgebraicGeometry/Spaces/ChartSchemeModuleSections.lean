module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.RelativeSpecFinish.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent

/-!
# The sections of the chart restriction of a quasi-coherent module on an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `M` be a
quasi-coherent `𝒪_X`-module on the small étale site of `X`, and let `A` be an étale scheme chart
of `X`.  `AlgebraicGeometry.Space.chartSchemeModule` transports `M` to a quasi-coherent
`AlgebraicGeometry.Scheme.Modules` on the scheme underlying `A`, by composing the localization of
Stacks 04M0 at the chart with Descent, Proposition 03DX (2) for a scheme.  The transport is
defined through the *inverse* of an equivalence of categories obtained from essential
surjectivity, so nothing about its sections is visible in the definition.

This file computes them.  The inverse of the associated-module equivalence agrees, on the
quasi-coherent modules, with the right adjoint `AlgebraicGeometry.SmallEtale.restrictModule` of
the associated-module functor, which is restriction along the inclusion of the small Zariski site
and therefore *has* sections: over an open `V` they are the sections of the étale-site module over
`V` read as an object of the small étale site.  Chasing that through the comparison of the small
étale site of the chart space with the small étale site of the chart scheme and through the
localization at the chart, the sections of the transport over a Zariski open `V` of the chart
scheme turn out to be the sections of `M` over the étale chart `V` cuts out,
`AlgebraicGeometry.Space.openChart`.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeEtaleQcoh` and
  `AlgebraicGeometry.Space.chartSchemeEtaleModule`: the restriction of `M` to the small étale
  site of the chart *scheme*, i.e. the chart restriction read before Descent, Proposition
  03DX (2) is applied to it.

## Main results

* `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule`: **the chart restriction of a
  quasi-coherent `𝒪_X`-module is the restriction, along the inclusion of the small Zariski site
  of the chart scheme, of its restriction to the small étale site of that scheme.**
* `AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj`: a Zariski open of the chart
  scheme, carried through the comparison of the two small étale sites and through the
  localization at the chart, is the étale chart of `X` that it cuts out.
* `AlgebraicGeometry.Space.chartSchemeEtaleModule_obj_opensObj`,
  `AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_obj`: **the sections of the
  chart restriction over a Zariski open `V` of the chart scheme are the sections of `M` over the
  étale chart cut out by `V`.**

## Implementation notes

The two inputs that make this possible are both available and unconditional, so no hypothesis beyond
quasi-coherence of `M` is carried anywhere below:

* `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, the statement that the unit
  `𝓕 ⟶ (𝓕^a)|_{S_Zar}` of the associated-module adjunction of the small étale site of a scheme is
  an isomorphism at every quasi-coherent module.  This is what replaces the opaque inverse of the
  equivalence by the right adjoint.
* the counit of `AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`, which identifies the
  associated module of the transport with the module one started from.

**The unit isomorphism has to be invoked at `(chartSchemeQcoh …).obj`, not at
`chartSchemeModule`.**  The two are definitionally equal, but `chartSchemeModule` is an ordinary
definition and instance search does not unfold it, so `IsIso` of the unit is not found at the
second spelling.

**Why the sections come out definitionally.**  Three of the four steps are `rfl`: the sections of
a `CategoryTheory.SheafOfModules.pushforward` are the sections of the module at the image object,
and both the reindexing along the comparison of the two small étale sites
(`Stacks.SheafOfModules.reindexEquivalence`, whose inverse is a pushforward) and the restriction
to the slice at the chart are pushforwards.  Only the fourth step has content, and it is the
identification of objects of the site recorded in
`AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj`; there the sole discrepancy is
that `AlgebraicGeometry.Space.openSub` takes the open immersion into the size-bounded category of
schemes with `CategoryTheory.Functor.preimage`, while
`AlgebraicGeometry.BigEtaleOver.opensObj` takes it with
`CategoryTheory.ObjectProperty.homMk`.  The two agree because the inclusion is faithful, which is
`CategoryTheory.Functor.map_preimage`, and that single rewrite is the whole proof.

**The scalar action on the identified sections, and why it is the right one.**  The sections
equality is an equality of the underlying types, not of modules over one ring: on the left the
scalars are `Γ(T, V)` and on the right they are the global functions on the open subscheme `V`,
which are the sections of `𝒪_X` over the étale chart `V` cuts out.  The two are matched by the
restriction of scalars along `AlgebraicGeometry.SmallEtale.structureMap`, whose component at `V`
is `(AlgebraicGeometry.Scheme.Opens.topIso V).inv` by
`AlgebraicGeometry.SmallEtale.structureMap_hom_app` — *the same* ring isomorphism along which
`AlgebraicGeometry.Space.openChartIdeal` transports the ideal of sections of a sheaf of ideals of
`𝒪_X`, and so the one under which the two sides of the ideal-power identification are stated.
A lemma stating this semilinearity on the nose is not here: the module over which
`((AlgebraicGeometry.SmallEtale.restrictModule …).obj N).val.obj (op V)` is taken is a `RingCat`
object, `T.ringCatSheaf.obj (op V)`, while `Γ(T, V)` and the components of
`AlgebraicGeometry.Scheme.Opens.topIso` are spelled in `CommRingCat`; the two are definitionally
equal but instance search is syntactic, so the statement does not elaborate at either spelling
without a bridge, and the bridge is the only thing missing.  Everything below is stated at the
level of the section types, where this does not arise.

No declaration here carries a `stacks` tag: this is an input to the reduction of Stacks 07UM to
an étale chart, not an assertion of any tag.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The chart restriction on the small étale site of the chart scheme -/

/-- The restriction of a quasi-coherent `𝒪_X`-module to the small étale site of an étale scheme
chart, as an object of the category of quasi-coherent modules there.

This is `AlgebraicGeometry.Space.chartSmallEtaleQcoh` read across the comparison of the small
étale site of the chart space with the small étale site of the chart scheme; it is the chart
restriction before Descent, Proposition 03DX (2) is applied to it. -/
noncomputable abbrev chartSchemeEtaleQcoh
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) :=
  (representedQuasicoherentEquivalence B S hS ((SmallEtale.toOver B S hS X.1).obj A)).inverse.obj
    (chartSmallEtaleQcoh B S hS X M hM A)

/-- The restriction of a quasi-coherent `𝒪_X`-module to the small étale site of an étale scheme
chart, as a sheaf of modules. -/
noncomputable abbrev chartSchemeEtaleModule
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) :=
  (chartSchemeEtaleQcoh B S hS X M hM A).obj

/-- The associated module of the chart restriction is the restriction to the small étale site of
the chart scheme: this is the counit of the equivalence of Descent, Proposition 03DX (2) at the
chart. -/
noncomputable def associatedModuleChartSchemeModuleIso
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) :=
  (ObjectProperty.ι _).mapIso
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
      (associatedBigEtaleSite B) (chartScheme A)
      ((SmallEtale.toOver B S hS X.1).obj A).left.property).counitIso.app
        (chartSchemeEtaleQcoh B S hS X M hM A))

/-- **The chart restriction of a quasi-coherent `𝒪_X`-module is the restriction, along the
inclusion of the small Zariski site of the chart scheme, of its restriction to the small étale
site of that scheme.**

The chart restriction is defined through the inverse of the equivalence of Descent, Proposition
03DX (2), which is obtained from essential surjectivity and says nothing about sections.  This
replaces it by the right adjoint of the associated-module functor, which is a pushforward and so
computes its sections at an object of the site. -/
noncomputable def chartSchemeModuleIsoRestrictModule
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) :
    chartSchemeModule B S hS X M hM A ≅
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A) :=
  have := _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent
    (associatedBigEtaleSite B) (chartScheme A)
    ((SmallEtale.toOver B S hS X.1).obj A).left.property
    (chartSchemeQcoh B S hS X M hM A)
  (asIso ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
      (associatedBigEtaleSite B) (chartScheme A)
      ((SmallEtale.toOver B S hS X.1).obj A).left.property).unit.app
        (chartSchemeQcoh B S hS X M hM A).obj)).trans
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property).mapIso
        (associatedModuleChartSchemeModuleIso B S hS X M hM A))

/-! ### The sections over a Zariski open of the chart scheme -/

/-- **A Zariski open of the chart scheme, read as an object of the small étale site of that
scheme, carried back along the comparison of the two small étale sites and along the localization
at the chart, is the étale chart of `X` that it cuts out.**

The two sides differ only in how the open immersion is taken into the size-bounded category of
schemes: `AlgebraicGeometry.Space.openSub` uses `CategoryTheory.Functor.preimage` and
`AlgebraicGeometry.BigEtaleOver.opensObj` uses `CategoryTheory.ObjectProperty.homMk`.  They agree
because the inclusion is faithful. -/
theorem openChart_eq_chartLocalization_opensObj
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens) :
    ((SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor.obj
        ((representedSmallEtaleEquivalence B S hS
          ((SmallEtale.toOver B S hS X.1).obj A)).inverse.obj
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property V))).left =
      openChart B S hS X.1 A V :=
  Stacks.CategoryTheory.fullSubcategory_eq_of_obj_eq
    (congrArg (fun g => CostructuredArrow.mk
        (yoneda.map (Over.homMk (V := (SmallEtale.toOver B S hS X.1).obj A)
          (U := Over.mk (g ≫ ((SmallEtale.toOver B S hS X.1).obj A).hom)) g (w := rfl)) ≫
            A.obj.hom))
      (B.inclusion.map_injective (B.inclusion.map_preimage _).symm))

/-- The sections of a sheaf of modules restricted along the inclusion of the small Zariski site
of a scheme are its sections over the open read as an object of the small étale site. -/
theorem restrictModule_obj_val_obj (B' : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B'.Contains T)
    (N : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf B' T hT))
    (V : T.Opens) :
    ((((_root_.AlgebraicGeometry.SmallEtale.restrictModule B' T hT).obj N).val.obj
        (op V) : Type u)) =
      (N.val.obj (op (_root_.AlgebraicGeometry.SmallEtale.opensObj B' T hT V)) : Type u) := rfl

/-- The sections of the restriction of `M` to the small étale site of the chart scheme are the
sections, over the corresponding object of the small étale site of the chart space, of the
restriction of `M` to that site. -/
theorem chartSchemeEtaleModule_obj
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1)
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B) (chartScheme A)
      ((SmallEtale.toOver B S hS X.1).obj A).left.property) :
    (((chartSchemeEtaleModule B S hS X M hM A).val.obj (op T) : Type u)) =
      ((chartSmallEtaleRestriction B S hS X M A).val.obj
        (op ((representedSmallEtaleEquivalence B S hS
          ((SmallEtale.toOver B S hS X.1).obj A)).inverse.obj T)) : Type u) := rfl

/-- The sections of the restriction of `M` to the small étale site of the chart space over an
object of that site are the sections of `M` over the étale chart of `X` it becomes. -/
theorem chartSmallEtaleRestriction_obj
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1)
    (P : SmallEtale B S hS (chartSpace B S hS X A).1) :
    (((chartSmallEtaleRestriction B S hS X M A).val.obj (op P) : Type u)) =
      (M.val.obj (op ((SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor.obj
        P).left) : Type u) := rfl

/-- **The sections of the chart restriction of `M` over a Zariski open `V` of the chart scheme
are the sections of `M` over the étale chart cut out by `V`.**

This is the whole point of the module: the chart restriction is defined through the inverse of an
equivalence obtained from essential surjectivity, and this is a formula for its sections. -/
theorem restrictModule_chartSchemeEtaleModule_obj
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    ((((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V) : Type u)) =
      (M.val.obj (op (openChart B S hS X.1 A V)) : Type u) :=
  ((restrictModule_obj_val_obj (associatedBigEtaleSite B) (chartScheme A)
        ((SmallEtale.toOver B S hS X.1).obj A).left.property
        (chartSchemeEtaleModule B S hS X M hM A) V).trans
      ((chartSchemeEtaleModule_obj B S hS X M hM A _).trans
        (chartSmallEtaleRestriction_obj B S hS X M A _))).trans
    (congrArg (fun P => (M.val.obj (op P) : Type u))
      (openChart_eq_chartLocalization_opensObj B S hS X A V))

end AlgebraicGeometry.Space

end
