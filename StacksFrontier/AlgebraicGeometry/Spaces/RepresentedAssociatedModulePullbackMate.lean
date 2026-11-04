module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparisonMapTranspose
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition
public import StacksFrontier.CategoryTheory.CommutingSquares

/-!
# The comparison of Stacks 03LC (1) for a represented algebraic space, as a mate

Let `ψ : U ⟶ V` be a morphism of the big fppf category over a scheme `S`.  Stacks 03LC (1)
compares the two routes round the square of small étale ringed sites of Stacks 070R (2) attached
to `ψ`: pulling a Zariski module on the scheme underlying `V` back along the morphism of schemes
underlying `ψ` and then taking its associated module on the small étale site of the represented
algebraic space `yoneda.obj U`, against taking the associated module on the small étale site of
`yoneda.obj V` and then the inverse image of Stacks 03LU along the represented morphism.

## Why the mate

Both routes are *left* adjoints, so neither is computable on sections and no direct comparison
of them is available.  The two composite *right* adjoints, on the other hand, are computable:
each is a restriction of sections, and over an open of the scheme underlying `V` both give the
sections over the base change of that open, by
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_app_app`.  So the comparison of the
left adjoints is *defined* here as the mate — `CategoryTheory.conjugateIsoEquiv` — of the
comparison `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso` of the right
adjoints.  Conjugation is a bijection on isomorphisms, so this pins the comparison down: its
mate is the computable one by construction, which is exactly what a square whose sides are
morphisms out of one of these composite inverse images needs.

This is not an identification of the mate with
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`, the form of Stacks 03LC (1)
already in the tree; that comparison is natural in the module only, and no such identification is
needed by the consumers of the mate.

## Main definitions

* `AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIso`: the square of direct
  images `AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, conjugated through the
  two comparison equivalences of module categories so that it reads with their inverses.
* `AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoUnit` and
  `AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoCollapse`: its two named
  factors — the unit of the equivalence of module categories of `V` inserted on the right, which
  is the identity on sections, and the collapse of the square against the counit of the
  equivalence of `U`, which carries all of its content.
* `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIsoBaseChange` and
  `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIsoSquare`: the two halves of that
  comparison — the one carrying
  `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso` and the one carrying the square of
  direct images.
* `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso`: **the comparison of the two
  composite right adjoints round the square of Stacks 03LC (1)**, the composite of those two.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackMateIso`: **the comparison of the
  two composite left adjoints, defined as the mate of the previous one.**

## Main results

* `Space.representedRestrictModuleBaseChangeIso_inv_app_smallEtaleModuleEquivalence`:
  **the one bridge between the two spellings of the equivalence of module categories** — the
  comparison of the two composite right adjoints at an object, read with its source and target
  functors in the spelling its two named factors and everything beneath them use.
* `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app` and
  `…_hom_app`: the comparison of the two composite right adjoints splits, at an object, into its
  two named factors.
* `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIsoSquare_inv_app`: **the square
  half of that comparison, at an object, is the restriction to the small Zariski site of the
  square of direct images** — the step the assembly of the comparison on sections hangs off.
* `AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIso_inv_app` and
  `…_hom_app`: the same for the square of direct images inside it.
* `AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoCollapse_inv_app`: **the
  collapsing factor splits, at an object, into the direct image of Stacks 03LU of the counit, the
  chart comparison and a composite of restrictions** — the factorisation needed to
  read the comparison of the right adjoints on sections.
* `Space.representedModulePushforwardSquareInverseIsoCollapse_inv_app_chartFirst`:
  **the same three morphisms with the counit moved past the chart comparison**, which is the form
  in which every factor is a restriction of sections: the counit then sits inside the base-change
  direct image, which has a sections formula, instead of inside the direct image of Stacks 03LU,
  which has none.
* `AlgebraicGeometry.Space.conjugateIsoEquiv_representedAssociatedModulePullbackMateIso`: **the
  mate identity** — conjugating the mate returns the comparison of the right adjoints.
* `AlgebraicGeometry.Space.conjugateEquiv_representedAssociatedModulePullbackMateIso_hom`: its
  `hom` half, which is the form `CategoryTheory.homEquiv_comp_conjugateEquiv` consumes.

## Implementation notes

**Why the comparison of the right adjoints is built out of two named factors.**  A consumer which
reads it on sections has to split it into factors each of which is restriction along an arrow of
the site.  Splitting it *afterwards* is not available: writing the comparison as a chain of five
`CategoryTheory.Iso.trans`es and unfolding that chain with `simp only` leaves a goal which is no
longer type-correct at `implicit` transparency — the two spellings `Space.Modules` and
`SheafOfModules (AlgebraicGeometry.Space.ringStructureSheaf …)` of the modules on the small étale
site of a represented algebraic space agree only at default transparency — so no further `rw`
finds its pattern, not even `CategoryTheory.NatTrans.comp_app`; and discharging the concrete
instance of a collapse lemma stated on variables exhausts the heartbeat budget at `whnf`, even
with all seven functors of the chain explicit.  Building the comparison as a composite of two
top-level definitions makes the split a `rfl` lemma proved where the definition is in scope,
after which no consumer unfolds anything.

**Why the two named factors are written in one spelling of the equivalence of module categories,
and where the one bridge to the other is paid.**
`AlgebraicGeometry.Space.representedModuleSiteEquivalence` and
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` are the same equivalence — they
are equal by `rfl`, cheaply, since the comparison is the identity on sections both ways — but
they are not the same *term*, and the difference is not free where it is not the only thing being
checked.  On its own, `(representedModuleSiteEquivalence B S hS V).inverse.obj M =
(representedSmallEtaleModuleEquivalence B S hS V).inverse.obj M` is `rfl` in seconds.
Folded into anything larger — a factorisation which also has to unfold a chain of `Iso.trans`es,
or an `exact` whose other arguments are still metavariables — it is not: the unifier reduces the
sheaves of modules instead of the functors and the heartbeat budget goes at `whnf`.

The three definitions of the square of direct images and both named factors of the comparison of
the two composite right adjoints are therefore written with
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` and
`AlgebraicGeometry.Space.representedSpaceMap` — the spelling
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` comes in and the one every
sections reading beneath them is written in — so that the factorisations chain by `rfl`.  The
comparison *itself* is declared in the other spelling, because its consumers are the two composite
adjunctions `AlgebraicGeometry.Space.representedAssociatedModulePullbackAdjunction` and
`AlgebraicGeometry.Space.representedAssociatedModuleSpacePullbackAdjunction`, which are written
that way, and a square transposed across them meets the comparison at an object, not at a functor:
declaring the comparison in the lower spelling leaves
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_square_of_postcomp` unprovable,
its last step exhausting the heartbeat budget at `whnf` however the natural isomorphism, the
object, the two whiskered functors and the two morphisms are pinned, and however the hypothesis
and the mate identity are spelled.  Declaring it in the upper spelling is free: the body is checked
against the expected type, which makes the two spellings meet at the level of *functors*.

So the bridge is one `rfl` lemma,
`Space.representedRestrictModuleBaseChangeIso_inv_app_smallEtaleModuleEquivalence`:
`CategoryTheory.Iso.inv` of the comparison, at a module, with its source and target functors given
in the lower spelling.  It is a defeq of functors, and it is the only place in the chain where the
two spellings meet.

## References

* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Mate

variable {U V : BigFppfOver B S hS} (ψ : U ⟶ V)

/-- **The unit half of the square of direct images read with the inverses of the two comparison
equivalences of module categories.**  Pushing a module on the small étale site of the scheme
underlying `U` forward along the morphism of small étale ringed sites of Stacks 070R (2) is doing
that, reading the result on the small étale site of `yoneda.obj V`, and reading it back.

It is the unit of the equivalence of module categories of Stacks 03DX (2) of `V`, inserted on the
right of the composite and rebracketed.  Three of its four factors — a right unitor and two
associators — are the identity on sections; the fourth, the unit itself, is not: it is restriction
along the base change of the counit of the equivalence of sites of `V`, which is what
`AlgebraicGeometry.Space.induced_representedModulePushforwardSquareInverseIsoUnit_inv` reads it
as. -/
def representedModulePushforwardSquareInverseIsoUnit :
    (representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
        SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ) ≅
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
            (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ) ⋙
              (representedSmallEtaleModuleEquivalence B S hS V).functor)) ⋙
        (representedSmallEtaleModuleEquivalence B S hS V).inverse :=
  Functor.isoWhiskerLeft _ (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (representedSmallEtaleModuleEquivalence B S hS V).unitIso) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm

/-- **The collapsing half of the square of direct images read with the inverses of the two
comparison equivalences of module categories.**  Restricting an `𝒪`-module on the small étale site
of `yoneda.obj U` to the small étale site of the scheme underlying `U`, pushing it forward along
the morphism of small étale ringed sites of Stacks 070R (2) and reading the result on the small
étale site of `yoneda.obj V` is taking the direct image of Stacks 03LU along the represented
morphism.

This is where all the content of the square sits: it is
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, whose last factor is the
comparison `AlgebraicGeometry.Space.modulePushforwardChartIso` of the direct image of
Stacks 03LU with base change of étale scheme charts, followed by the counit of the equivalence of
module categories of `U`.  Those two are the only non-structural factors of the whole square, and
they are kept in one named definition because the counit has to be moved past the chart
comparison by naturality before either can be read on sections — the direct image of Stacks 03LU
of a *morphism* of modules has no sections formula, its sections over an object of the small étale
site being a limit over the étale scheme charts above a fibre product. -/
def representedModulePushforwardSquareInverseIsoCollapse :
    (representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
        (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ) ⋙
          (representedSmallEtaleModuleEquivalence B S hS V).functor) ≅
      modulePushforward B S hS (representedSpaceMap B S hS ψ) :=
  Functor.isoWhiskerLeft _
      (representedModulePushforwardSquareIso B S hS ψ
        (relativelyRepresentable_yoneda_map B S hS ψ)) ≪≫
    (representedSmallEtaleModuleEquivalence B S hS U).invFunIdAssoc
      (modulePushforward B S hS (representedSpaceMap B S hS ψ))

/-- **The collapsing half of the square, in its `inv` direction, split into its three factors.**
They are, in order: the direct image of Stacks 03LU of the inverse of the counit of the
equivalence of module categories of `U`; the comparison
`AlgebraicGeometry.Space.modulePushforwardChartIso` of the direct image of Stacks 03LU with base
change of étale scheme charts, at the transported module; and
`AlgebraicGeometry.Space.representedModulePushforwardSquareRestrictIso`, every factor of which is
a restriction of sections.

The first factor is the one with no sections formula — the sections of the direct image of
Stacks 03LU over an object of the small étale site are a limit over the étale scheme charts above
a fibre product — and the point of exposing the chart comparison as the factor beside it is that
`CategoryTheory.NatTrans.naturality` of the chart comparison at the counit exchanges the two.
After the exchange the counit sits inside the base-change direct image
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, which *is* a restriction of sections,
and is read over the base-changed chart by
`AlgebraicGeometry.Space.induced_representedModuleSiteEquivalence_counitIso_inv`.

The exchanged form is
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoCollapse_inv_app_chartFirst`,
below. -/
theorem representedModulePushforwardSquareInverseIsoCollapse_inv_app
    (N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (representedModulePushforwardSquareInverseIsoCollapse B S hS ψ).inv.app N =
      (modulePushforward B S hS (representedSpaceMap B S hS ψ)).map
          ((representedSmallEtaleModuleEquivalence B S hS U).counitInv.app N) ≫
        ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS ψ)
              (relativelyRepresentable_yoneda_map B S hS ψ)).hom.app
            ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj
              ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)) ≫
          (representedModulePushforwardSquareRestrictIso B S hS ψ
              (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)) := by
  have h1 : (representedModulePushforwardSquareInverseIsoCollapse B S hS ψ).inv.app N =
      ((representedSmallEtaleModuleEquivalence B S hS U).invFunIdAssoc
            (modulePushforward B S hS (representedSpaceMap B S hS ψ))).inv.app N ≫
        (representedModulePushforwardSquareIso B S hS ψ
            (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N) := rfl
  have hinv := Equivalence.invFunIdAssoc_inv_app
    (representedSmallEtaleModuleEquivalence B S hS U)
    (modulePushforward B S hS (representedSpaceMap B S hS ψ)) N
  have hsq := representedModulePushforwardSquareIso_inv_app B S hS ψ
    (relativelyRepresentable_yoneda_map B S hS ψ)
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)
  exact h1.trans ((eq_whisker hinv _).trans (whisker_eq _ hsq))

/-- **The collapsing half of the square, in its `inv` direction, with the counit moved past the
chart comparison.**  Its three factors are, in order: the comparison
`AlgebraicGeometry.Space.modulePushforwardChartIso` of the direct image of Stacks 03LU with base
change of étale scheme charts, at the module itself; the *base-change* direct image of the inverse
of the counit of the equivalence of module categories of `U`; and
`AlgebraicGeometry.Space.representedModulePushforwardSquareRestrictIso`.

This is the form in which every factor is a restriction of sections.  In
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoCollapse_inv_app` the counit
is pushed forward along the direct image of Stacks 03LU, which has no sections formula — its
sections over an object of the small étale site are a limit over the étale scheme charts above a
fibre product.  Here it sits inside
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward` instead, where it is read over the
base-changed chart by
`AlgebraicGeometry.Space.induced_representedSmallEtaleModuleEquivalence_counitIso_inv`, and the
chart comparison is read off as the chart projection by
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_chartSetProj`.

The exchange is the naturality square of the chart comparison at the inverse of the counit,
followed by one reassociation.  Both steps need care at these objects.  The naturality square
elaborates on its own, but its target is the composite `inverse ⋙ functor` applied to the module,
while the factorisation above has the two functors applied in turn, and the two spellings are
identified only by unfolding the equivalence: discharging that identification as part of
a larger unification problem exhausts the heartbeat budget at `whnf`.  So the square is first
normalised to the applied spelling by `dsimp only [Functor.comp_obj, Functor.id_obj]`, a purely
syntactic step.  The reassociation is then `CategoryTheory.square_comp'`, which is stated over a
variable category with every object and morphism a variable, so that each argument is read off the
naturality square rather than unified against the goal; `rw [← CategoryTheory.Category.assoc]`
cannot be used instead, reporting that it cannot find the pattern `?f ≫ ?g ≫ ?h` in a goal which
visibly has that shape — the two spellings of the category of modules on the small étale site of a
represented algebraic space carry different `CategoryTheory.Category`-instance paths — and both
`CategoryTheory.NatTrans.naturality_assoc` and `CategoryTheory.Category.assoc` with metavariable
arguments exhaust the heartbeat budget at `whnf`. -/
theorem representedModulePushforwardSquareInverseIsoCollapse_inv_app_chartFirst
    (N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (representedModulePushforwardSquareInverseIsoCollapse B S hS ψ).inv.app N =
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS ψ)
            (relativelyRepresentable_yoneda_map B S hS ψ)).hom.app N ≫
        (smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS ψ)
              (relativelyRepresentable_yoneda_map B S hS ψ)).map
            ((representedSmallEtaleModuleEquivalence B S hS U).counitInv.app N) ≫
          (representedModulePushforwardSquareRestrictIso B S hS ψ
              (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N) := by
  have hnat := NatTrans.naturality
    (modulePushforwardChartIso B S hS (representedSpaceMap B S hS ψ)
      (relativelyRepresentable_yoneda_map B S hS ψ)).hom
    ((representedSmallEtaleModuleEquivalence B S hS U).counitInv.app N)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hnat
  exact (representedModulePushforwardSquareInverseIsoCollapse_inv_app B S hS ψ N).trans
    (square_comp' hnat rfl)

/-- **The square of direct images of Stacks 03LU and of base change of schemes, read with the
inverses of the two comparison equivalences of module categories.**  Restricting an `𝒪`-module on
the small étale site of `yoneda.obj U` to the small étale site of the scheme underlying `U` and
then pushing it forward along the morphism of small étale ringed sites of Stacks 070R (2) is
taking the direct image of Stacks 03LU along the represented morphism and then restricting.

This is `AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, which states the same
square for the two equivalences themselves, transported across their unit and counit.  Like
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso`, which it is a factor of, it is
built as the composite of exactly two named factors —
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoUnit` and the whiskering of
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoCollapse` — so that a
consumer which reads it on sections splits it by
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIso_inv_app` instead of
unfolding a chain of associators and whiskerings. -/
def representedModulePushforwardSquareInverseIso :
    (representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
        SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ) ≅
      modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
        (representedSmallEtaleModuleEquivalence B S hS V).inverse :=
  representedModulePushforwardSquareInverseIsoUnit B S hS ψ ≪≫
    Functor.isoWhiskerRight (representedModulePushforwardSquareInverseIsoCollapse B S hS ψ)
      (representedSmallEtaleModuleEquivalence B S hS V).inverse

/-- **The factorisation of the square of direct images into its two named factors, in the `inv`
direction**, which is the direction in which every factor of
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso` computes on sections.  It holds
by `rfl`, the square being *defined* as that composite, and is proved here — where the definition
is in scope — so that no consumer has to unfold a chain of associators and whiskerings.

The whiskering is resolved here too, to the direct image along the reading-back of the collapsing
factor at the module: a consumer cannot do it, `CategoryTheory.Functor.isoWhiskerRight_inv`
failing to find its pattern in a goal which visibly has it — the two spellings of the category of
modules on the small étale site of a represented algebraic space carry different
`CategoryTheory.Category`-instance paths — and the factorisation of the collapsing factor is
stated at the module, so without the whiskering resolved it has no pattern to match either. -/
theorem representedModulePushforwardSquareInverseIso_inv_app
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (representedModulePushforwardSquareInverseIso B S hS ψ).inv.app M =
      (representedSmallEtaleModuleEquivalence B S hS V).inverse.map
          ((representedModulePushforwardSquareInverseIsoCollapse B S hS ψ).inv.app M) ≫
        (representedModulePushforwardSquareInverseIsoUnit B S hS ψ).inv.app M :=
  rfl

/-- **The factorisation of the square of direct images into its two named factors, in the `hom`
direction**, with the whiskering resolved for the reason recorded on the `inv` direction. -/
theorem representedModulePushforwardSquareInverseIso_hom_app
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (representedModulePushforwardSquareInverseIso B S hS ψ).hom.app M =
      (representedModulePushforwardSquareInverseIsoUnit B S hS ψ).hom.app M ≫
        (representedSmallEtaleModuleEquivalence B S hS V).inverse.map
          ((representedModulePushforwardSquareInverseIsoCollapse B S hS ψ).hom.app M) :=
  rfl

/-- **The base-change half of the comparison of the two composite right adjoints round the square
of Stacks 03LC (1).**  Reading an `𝒪`-module on the small étale site of `yoneda.obj U` on the
small étale site of the scheme underlying `U`, restricting it to the small Zariski site there and
pushing it forward along the morphism of schemes underlying `ψ` is pushing it forward along the
morphism of small étale sites of Stacks 070R (2) and then restricting to the small Zariski site of
the scheme underlying `V`.

This is `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso`, whiskered by the comparison
equivalence of module categories of `U` and rebracketed; over an open of the scheme underlying
`V` it is restriction of sections along the base change of that open, by
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_app_app`.

Like the square half beside it, it is written throughout in the
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` spelling of the equivalence of
module categories, the one the square of direct images and every sections reading beneath are
written in; see the implementation notes of this file. -/
def representedRestrictModuleBaseChangeIsoBaseChange :
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
        Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ) ≅
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
          SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ)) ⋙
        _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property :=
  Functor.associator ((representedSmallEtaleModuleEquivalence B S hS U).inverse)
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)) ≪≫
    Functor.isoWhiskerLeft _
      (_root_.AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso
        (associatedBigEtaleSite B) ψ.left).symm ≪≫
    (Functor.associator _ _ _).symm

/-- **The square half of the comparison of the two composite right adjoints round the square of
Stacks 03LC (1).**  Reading an `𝒪`-module on the small étale site of `yoneda.obj U` on the small
étale site of the scheme underlying `U`, pushing it forward along the morphism of small étale
sites of Stacks 070R (2) and restricting to the small Zariski site of the scheme underlying `V`
is taking its direct image of Stacks 03LU along the represented morphism and then restricting.

This is `AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIso`, whiskered by the
restriction to the small Zariski site of the scheme underlying `V` and rebracketed.

**Why nothing needs to be named here.**  `CategoryTheory.Functor.isoWhiskerRight` takes
the two functors it whiskers from the type of the isomorphism it is given and not from its own
expected type, so the spelling of
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIso` decides them.  That
spelling is `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` with
`AlgebraicGeometry.Space.representedSpaceMap`, and the declared type here is written the same
way, so the whiskered functors are already the declared type's and need no named implicits.  With
the declared type in the other spelling they would have to be pinned by hand, and even then the
factorisations *beneath* this one could not be chained onto
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIsoSquare_inv_app`: they are written
in this spelling, so the chaining would ask the two spellings to meet inside
`(·).inverse.obj`, where the unifier reduces the sheaves of modules rather than the functors and the
heartbeat budget goes.  The whole chain is therefore in one spelling, and the single bridge
between the two is paid once, in
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMateIso`, where an expected type
guides it and the two spellings meet at the level of *functors*, which is cheap. -/
def representedRestrictModuleBaseChangeIsoSquare :
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
          SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ)) ⋙
        _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property ≅
      modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
        ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property) :=
  Functor.isoWhiskerRight (representedModulePushforwardSquareInverseIso B S hS ψ)
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property) ≪≫
    Functor.associator _ _ _

/-- **The square half of the comparison of the two composite right adjoints, in its `inv`
direction, is the restriction to the small Zariski site of the square of direct images.**  Its
only other factor is an associator, which is the identity on sections.

This is the equation needed to assemble the comparison of the two composite right adjoints on
sections.  What makes it go through is
that the factorisation of the square half into the associator and the whiskering is taken at the
level of *natural transformations*, before the component at `M`: at the component neither `rfl`
nor `CategoryTheory.Category.id_comp` can do it and `CategoryTheory.NatTrans.comp_app` does not
even fire — the two spellings of the category of modules on the small étale site of a represented
algebraic space carry different `CategoryTheory.Category`-instance paths — while one line higher
up it is `rfl`, and the component of an explicit composite of two explicit natural
transformations then reduces on its own. -/
theorem representedRestrictModuleBaseChangeIsoSquare_inv_app
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (representedRestrictModuleBaseChangeIsoSquare B S hS ψ).inv.app M =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
        ((representedModulePushforwardSquareInverseIso B S hS ψ).inv.app M) := by
  have h : (representedRestrictModuleBaseChangeIsoSquare B S hS ψ).inv =
      (Functor.associator (modulePushforward B S hS (representedSpaceMap B S hS ψ))
            (representedSmallEtaleModuleEquivalence B S hS V).inverse
            (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property)).inv ≫
        (Functor.isoWhiskerRight (representedModulePushforwardSquareInverseIso B S hS ψ)
          (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property)).inv := rfl
  rw [h]
  exact Category.id_comp _

/-- **The comparison of the two composite right adjoints round the square of Stacks 03LC (1) for
a represented algebraic space.**  Reading an `𝒪`-module on the small étale site of
`yoneda.obj U` on the small étale site of the scheme underlying `U`, restricting it to the small
Zariski site there and pushing it forward along the morphism of schemes underlying `ψ` is taking
its direct image of Stacks 03LU along the represented morphism and then restricting to the small
Zariski site of the scheme underlying `V`.

It is `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso` — which over an open of the
scheme underlying `V` is restriction of sections along the base change of that open, hence
computable by `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_app_app` — carried
across the two comparison equivalences by
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIso`.  It is built as the
composite of exactly two named factors,
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIsoBaseChange` and
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIsoSquare`, so that a consumer which
has to read it on sections can split it by
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app` instead of unfolding a
chain of whiskerings. -/
def representedRestrictModuleBaseChangeIso :
    ((representedModuleSiteEquivalence B S hS U).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
        Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ) ≅
      modulePushforward B S hS (schemeSpaceMap ψ) ⋙
        ((representedModuleSiteEquivalence B S hS V).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property) :=
  representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ ≪≫
    representedRestrictModuleBaseChangeIsoSquare B S hS ψ

/-- **The one bridge between the two spellings of the equivalence of module categories**: the
comparison of the two composite right adjoints, in its `inv` direction at a module, read with its
two composite functors spelled the way everything *beneath* it is spelled —
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` with
`AlgebraicGeometry.Space.representedSpaceMap` — is the same morphism.

The comparison itself is declared in the other spelling,
`AlgebraicGeometry.Space.representedModuleSiteEquivalence` with
`AlgebraicGeometry.Space.schemeSpaceMap`, because that is the one
`AlgebraicGeometry.Space.representedAssociatedModulePullbackAdjunction` and
`AlgebraicGeometry.Space.representedAssociatedModuleSpacePullbackAdjunction` are written in, and a
consumer which transposes a square across them meets the comparison there; the square of direct
images inside it and every sections reading beneath it are written in the first, so that the
factorisations chain by `rfl`.  This is where the two meet, and it is the only place they do.

Both sides are `CategoryTheory.Iso.inv` of one and the same isomorphism, differing only in the two
functors given for its source and target, so the identification is a defeq of *functors* — cheap,
as `AlgebraicGeometry.Space.representedModuleSiteEquivalence` and
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` are `rfl` at that level.  Writing
the two functors out, rather than leaving them to be unified against a goal, is what keeps it
cheap: a consumer which asks for the two spellings to meet *inside* a component with the
functors inferred exhausts the heartbeat budget at `whnf`, and so does this very equation if the
factorisation into the two named halves is folded into it. -/
theorem representedRestrictModuleBaseChangeIso_inv_app_smallEtaleModuleEquivalence
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (representedRestrictModuleBaseChangeIso B S hS ψ).inv.app M =
      (Iso.inv
          (X := ((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
                _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
              Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ))
          (Y := modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
            ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
              _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
          (representedRestrictModuleBaseChangeIso B S hS ψ)).app M :=
  rfl

/-- **The factorisation of the comparison of the two composite right adjoints into its two named
factors, in the `inv` direction.**  The `inv` direction is the one in which every factor computes
on sections, and this is the equation a consumer needs in order to read the comparison one factor
at a time; it is proved here — where the comparison's definition is in scope — so that no consumer
has to unfold a chain of associators and whiskerings.

It is stated of the reading of
`Space.representedRestrictModuleBaseChangeIso_inv_app_smallEtaleModuleEquivalence`,
so that both sides are in the spelling of the two named factors and the two spellings of the
equivalence of module categories never have to meet inside a component here; a consumer which
starts from `(representedRestrictModuleBaseChangeIso B S hS ψ).inv.app M` reaches this through
that bridge.

The comparison is *defined* as the composite of the two factors, so this is `rfl` — but only one
step up, at the level of natural transformations.  At the component, `rfl` exhausts the
heartbeat budget at `whnf`, because it has to unfold the comparison past the spelling its declared
type gives it while an object is already applied; one line higher the unfolding is of functors
only, and the component of an explicit composite of two explicit natural transformations then
reduces on its own. -/
theorem representedRestrictModuleBaseChangeIso_inv_app
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (Iso.inv
          (X := ((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
                _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
              Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ))
          (Y := modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
            ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
              _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
          (representedRestrictModuleBaseChangeIso B S hS ψ)).app M =
      (representedRestrictModuleBaseChangeIsoSquare B S hS ψ).inv.app M ≫
        (representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).inv.app M := by
  have h : Iso.inv
        (X := ((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
              _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
            Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ))
        (Y := modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
          ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
            _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
        (representedRestrictModuleBaseChangeIso B S hS ψ) =
      (representedRestrictModuleBaseChangeIsoSquare B S hS ψ).inv ≫
        (representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).inv := rfl
  rw [h]
  rfl

/-- **The factorisation of the comparison of the two composite right adjoints into its two named
factors, in the `hom` direction**, stated in the spelling of those factors and proved one step up
at the natural transformations, both for the reasons recorded on the `inv` direction above. -/
theorem representedRestrictModuleBaseChangeIso_hom_app
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (Iso.hom
          (X := ((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
                _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
              Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ))
          (Y := modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
            ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
              _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
          (representedRestrictModuleBaseChangeIso B S hS ψ)).app M =
      (representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).hom.app M ≫
        (representedRestrictModuleBaseChangeIsoSquare B S hS ψ).hom.app M := by
  have h : Iso.hom
        (X := ((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
              _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
            Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ))
        (Y := modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
          ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
            _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
        (representedRestrictModuleBaseChangeIso B S hS ψ) =
      (representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).hom ≫
        (representedRestrictModuleBaseChangeIsoSquare B S hS ψ).hom := rfl
  rw [h]
  rfl

/-- **The comparison of the two composite left adjoints of Stacks 03LC (1) for a represented
algebraic space, defined as the mate of
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso`.**

Conjugation with respect to the two composite adjunctions
`AlgebraicGeometry.Space.representedAssociatedModulePullbackAdjunction` and
`AlgebraicGeometry.Space.representedAssociatedModuleSpacePullbackAdjunction` is a bijection
between the isomorphisms of the two composite left adjoints and the isomorphisms of the two
composite right adjoints, so this is the unique comparison of the two composite inverse images
whose mate is the comparison of the two composite restrictions. -/
def representedAssociatedModulePullbackMateIso :
    representedAssociatedModule B S hS V (schemeSpace V).property ⋙
        modulePullback B S hS (schemeSpaceMap ψ) ≅
      Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map ψ) ⋙
        representedAssociatedModule B S hS U (schemeSpace U).property :=
  (conjugateIsoEquiv (representedAssociatedModulePullbackAdjunction B S hS ψ)
      (representedAssociatedModuleSpacePullbackAdjunction B S hS ψ)).symm
    (representedRestrictModuleBaseChangeIso B S hS ψ)

/-- **The mate identity.**  Conjugating
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMateIso` with respect to the two
composite adjunctions round the square of Stacks 03LC (1) returns
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso`.

The mate was defined as the inverse image of that comparison under
`CategoryTheory.conjugateIsoEquiv`, so this is `Equiv.apply_symm_apply`.  It is the whole content
of the definition: because conjugation is a bijection, no other isomorphism of the two composite
inverse images has the computable comparison of the two composite restrictions for its
conjugate. -/
theorem conjugateIsoEquiv_representedAssociatedModulePullbackMateIso :
    conjugateIsoEquiv (representedAssociatedModulePullbackAdjunction B S hS ψ)
        (representedAssociatedModuleSpacePullbackAdjunction B S hS ψ)
        (representedAssociatedModulePullbackMateIso B S hS ψ) =
      representedRestrictModuleBaseChangeIso B S hS ψ :=
  (conjugateIsoEquiv (representedAssociatedModulePullbackAdjunction B S hS ψ)
      (representedAssociatedModuleSpacePullbackAdjunction B S hS ψ)).apply_symm_apply
    (representedRestrictModuleBaseChangeIso B S hS ψ)

/-- **The mate identity on the forward direction**, which is the form in which a square whose
sides are morphisms out of a composite inverse image consumes it: by
`CategoryTheory.homEquiv_comp_conjugateEquiv` the transpose of such a side, precomposed with the
mate, is the transpose across the other adjunction followed by this conjugate.  The forward
direction is the useful one, because it is the *inverse* of
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso` which
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_app_app` computes, and that inverse
is what `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso` puts into its `hom`.

The two functors of the comparison are given in the spelling the two composite adjunctions use,
for the reason recorded on
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_moduleSiteEquivalence`:
left to the dot notation they would be the comparison's own, and a consumer which rewrites with
this identity and then matches the result against a lemma stated in the adjunctions' spelling
would be left with the two to reconcile inside a component, where the heartbeat budget goes. -/
theorem conjugateEquiv_representedAssociatedModulePullbackMateIso_hom :
    conjugateEquiv (representedAssociatedModulePullbackAdjunction B S hS ψ)
        (representedAssociatedModuleSpacePullbackAdjunction B S hS ψ)
        (representedAssociatedModulePullbackMateIso B S hS ψ).hom =
      Iso.hom
        (X := ((representedModuleSiteEquivalence B S hS U).inverse ⋙
              _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
            Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ))
        (Y := modulePushforward B S hS (schemeSpaceMap ψ) ⋙
          ((representedModuleSiteEquivalence B S hS V).inverse ⋙
            _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
        (representedRestrictModuleBaseChangeIso B S hS ψ) :=
  congrArg Iso.hom (conjugateIsoEquiv_representedAssociatedModulePullbackMateIso B S hS ψ)

end Mate

end AlgebraicGeometry.Space

end
