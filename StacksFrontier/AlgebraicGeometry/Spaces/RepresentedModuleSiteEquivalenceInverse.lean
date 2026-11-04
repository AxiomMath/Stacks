module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponentsInduced
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparisonMapMate

/-!
# The inverse directions of the equivalence of module categories of Stacks 03DX (2)

The comparison of the two composite right adjoints round the square of Stacks 03LC (1) for a
represented algebraic space,
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso`, is read on sections in its
`inv` direction — that is the direction in which each of its factors computes, by the analysis in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMapMate.lean`.  Two of
those factors are the unit and the counit of the equivalence of module categories of
Stacks 03DX (2), and each enters in its `inv` direction, while the library had only the `hom`
directions: `CategoryTheory.SheafOfModules.pushforwardPushforwardEquivalence_unit_app_val_app`
and `…_counit_app_val_app`.  This file supplies the two missing readings, together with the
forward reading of the comparison of the two composite restrictions of
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso`, which is the outermost factor of the
same composite.

## The shape the readings are stated in

All of them are stated as `Stacks.SectionsComponents.Induced`: *the component at an object of the
site is restriction along an arrow of the site of a fixed module*.  That predicate carries the
identifications of the groups of sections as `cast`s inside an existential, which is what makes
the statements elaborate at all.  Written as an equation of elements instead — the shape of the
`hom` readings — the inverse readings do not type-check: the two spellings of one group of
sections, the sections of an iterated direct image over an object and the sections of the module
itself over the reindexed object, are identified only by unfolding two pushforwards, and the
elaborator exhausts its heartbeat budget at `whnf` on the statement's own type.  This
happens both at the concrete equivalence of a represented algebraic space and with the source
written in its folded spelling.

## Main results

* `Stacks.SectionsComponents.Induced.ofInv`: **the inverse of an invertible induced morphism is
  induced by the inverse arrow.**  This is the only content: a component which is restriction
  along an arrow of the site has, when the arrow is invertible, an inverse which is restriction
  along the inverse arrow, because restriction along the inverse arrow undoes it.
* `Stacks.SectionsComponents.Induced.pushforwardPushforwardEquivalenceUnitIsoInv` and
  `…CounitIsoInv`: the two missing readings, for an arbitrary equivalence of ringed sites whose
  two structure comparisons are coherent.
* `AlgebraicGeometry.Space.induced_representedModuleSiteEquivalence_unitIso_inv` and
  `…_counitIso_inv`: those two at the equivalence of Stacks 03DX (2) of a represented algebraic
  space.
* `AlgebraicGeometry.Space.induced_representedSmallEtaleModuleEquivalence_unitIso_inv` and
  `…_counitIso_inv`: the same two in the other spelling of that one equivalence, the one the
  square of direct images of Stacks 03LU is written in.  They are the previous two: the spellings
  agree, and at the top level of a statement the defeq is cheap.  Where it is *not* cheap is
  inside a composite applied to an object, which is why both spellings are wanted.
* `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_chartFirst`: **the
  three-way split** — the comparison of the two composite right adjoints, in its `inv` direction
  at a module, is the chart comparison taken inside two direct images, followed by the tail.
* `AlgebraicGeometry.SmallEtale.induced_restrictModuleBaseChangeIso_hom`: the comparison of the
  two composite restrictions of a morphism of schemes of a big étale site, in its `hom`
  direction, is restriction along `AlgebraicGeometry.SmallEtale.baseChangeOpensIso`.  The library
  had the `inv` direction, `…_inv_app_app`; both hold by `rfl`.

## What the assembly of `γ.inv` still owes

The factorisation itself is no longer the obstruction.  It was: splitting
`(AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso B S hS ψ).inv.app M` into its
factors by rewriting is not available — `simp only` unfolds the definition to its chain of
`CategoryTheory.Iso.trans`, but the unfolded goal is then no longer type-correct at `implicit`
transparency, the two spellings `AlgebraicGeometry.Space.Modules` and
`SheafOfModules (AlgebraicGeometry.Space.ringStructureSheaf …)` of the modules on the small étale
site of a represented algebraic space agreeing only at default transparency, so no further `rw`
finds its pattern, not even `CategoryTheory.NatTrans.comp_app`; and stating the collapse of the
chain as a lemma on variables and discharging the concrete instance exhausts the heartbeat budget
at `whnf`.  The answer was to *build* the comparison out of named factors rather than take it
apart afterwards, and that is now done at every level:
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app`,
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIso_inv_app`,
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoCollapse_inv_app` and
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso_inv_app` take `γ.inv` at an object
down to: two unitors and associators, the unit and the counit of the equivalence of module
categories, `CategoryTheory.SheafOfModules.pushforwardComp` and `pushforwardCongr₂`,
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso` — all of which the leaves here and in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SectionsComponentsInduced.lean` read as
`Stacks.SectionsComponents.Induced` — and exactly one factor which is not a restriction of
sections: the comparison `AlgebraicGeometry.Space.modulePushforwardChartIso` of the direct image
of Stacks 03LU with base change of étale scheme charts, which
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_chartSetProj` reads as the chart
projection.  So `γ.inv` on sections is the chart projection followed by a restriction -- and that
is now proved, in the shape the chart factor forces: a *three-way* split.

**The three-way split.**  `γ.inv.app M` is not itself `Stacks.SectionsComponents.Induced`, the
chart factor being a projection and not a restriction.  By
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app`,
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIso_inv_app` and
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoCollapse_inv_app_chartFirst`
it is an associator, which is the identity on sections; then the chart comparison inside *two*
direct images -- the restriction to the small Zariski site of the scheme underlying `V`, of the
reading-back along `V`'s equivalence of module categories; then the tail.  The tail is read by
`AlgebraicGeometry.Space.induced_representedRestrictModuleBaseChangeIso_inv_tail`: over an open
`O` of the scheme underlying `V` it is restriction along the single arrow of the small étale site
of `yoneda.obj U` from the base change along `ψ̃` of `O`, read as a chart, to the open
`ψ^{-1}O`, read as a chart.

Beyond the leaves that were already here the assembly needed seven more, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SectionsComponentsInduced.lean`:
`Stacks.SectionsComponents.Induced.isoTransHomIdLeft` and its three companions, which absorb a
structural factor of a chain of isomorphisms *without naming an object of the site for it*, so
that an associator or a unitor of functors which are not direct images needs no leaf of its own;
`…pushforwardMap`, for the counit, which enters the square as a direct image of a component and
not as a whiskering of an isomorphism; and `…reindexInverseMap` and `…descendReindex`, those two
operations at the reindexing equivalence of Stacks 06WI, stated on variables so that the two
spellings of its inverse are identified once.

The *equation* of the three-way split is proved too:
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_chartFirst` says that
`γ.inv.app M`, read through the one bridge below, is the chart factor followed by the tail.  What
remains is the sections identity itself.

**The proved steps.**  The associator of
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIsoSquare` comes off, and the square
half of the comparison at a module is the restriction to the small Zariski site of the square of
direct images:
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIsoSquare_inv_app`.  One
thing is needed for it: the factorisation of
the square half into the associator and the whiskering has to be taken at the level of *natural
transformations*, one step before the component at `M`.  At the component `rfl` and
`CategoryTheory.Category.id_comp` both exhaust the heartbeat budget at `whnf` and
`CategoryTheory.NatTrans.comp_app` does not even fire; one line higher up it is `rfl`, and the
component of an explicit composite of two explicit natural transformations then reduces on its
own.  The same device carries
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app` and `…_hom_app`.

**Where the one bridge between the two spellings sits.**  The lower half of the chain —
the square of direct images, its two named factors, and every sections reading here — is written
with `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` and
`AlgebraicGeometry.Space.representedSpaceMap`.  The upper half — the two composite adjunctions of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMapTranspose.lean`, and
so the square transposed across them — is written with
`AlgebraicGeometry.Space.representedModuleSiteEquivalence` and
`AlgebraicGeometry.Space.schemeSpaceMap`.  Both named factors of the comparison of the two
composite right adjoints,
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIsoBaseChange` and `…IsoSquare`, are
now in the lower spelling, so the factorisations beneath them chain by `rfl`.

The comparison *itself*,
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso`, stays in the upper spelling, and
that is forced rather than chosen: with it declared in the lower spelling,
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_square_of_postcomp` cannot be
closed.  Its last step exhausts the heartbeat budget at `whnf` with the natural
isomorphism and the object inferred, with them given, with the two whiskered functors pinned by
named implicits, with the hypothesis and the mate identity restated in the lower spelling, and
with the cancellation done by hand through a reassociation -- `CategoryTheory.Category.assoc` with
metavariable arguments dying there too.  Declared in the upper spelling it is free: the body is a
composite of the two factors checked against an expected type, which makes the two spellings meet
at the level of *functors*, where they are `rfl` cheaply.

So the bridge is exactly one `rfl` lemma,
`Space.representedRestrictModuleBaseChangeIso_inv_app_smallEtaleModuleEquivalence`:
`CategoryTheory.Iso.inv` of the comparison, at a module, with its source and target functors
written out in the lower spelling.  A consumer which starts from `γ.inv.app M` rewrites with it
once and is then in the lower spelling for the whole descent.  Nowhere else in the chain do the
two spellings meet at an object, and that is deliberate: an equation which asks them to
with the functors left to be inferred, or which folds the bridge together with the factorisation
into the two named halves, exhausts the budget at `whnf`.  On its own, with the functors written
out, the bridge costs seconds.

**What remains is the sections identity.**  With
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_chartFirst` the comparison
at a module is the chart factor followed by the tail; the tail is restriction along one arrow of
the small étale site of `yoneda.obj U` by
`AlgebraicGeometry.Space.induced_representedRestrictModuleBaseChangeIso_inv_tail`, and the chart
factor is the chart projection by
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_chartSetProj`.  What the hypothesis of
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_square_of_postcomp` then needs is
the identity of the two sides on sections — which regular function each side evaluates `d^a` of
`ψ ≫ χ` on — and after that the identity of derivations that hypothesis is stated in.

Assembling the split needs two things beyond the links.  The whiskering
inside the square of direct images has to be resolved where that square is *defined*, in
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIso_inv_app`: a consumer cannot
resolve it, `CategoryTheory.Functor.isoWhiskerRight_inv` failing to find its pattern in a goal
which visibly has it, and until it is resolved the factorisation of the collapsing factor — which
is stated at a module — has no pattern to match.  And peeling the chart factor off the front
through the two direct images has to be a lemma stated on variables,
`CategoryTheory.map_map_comp_assoc`, for the same reason that
`CategoryTheory.Category.assoc` cannot be used at these objects.

One step inside the factorisation needed care and is recorded where it arises, in the
implementation note on
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoCollapse_inv_app`: the
direct image of Stacks 03LU *of* the counit has no sections formula and must be exchanged with
the chart comparison by naturality, and that exchange is a reassociation which neither
`rw [← CategoryTheory.Category.assoc]` nor `CategoryTheory.NatTrans.naturality_assoc` can carry
out at these objects.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂ w m u

namespace Stacks.SectionsComponents

section Generic

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {M : SheafOfModules.{m} R} {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S' : Sheaf J' RingCat.{w}}

/-- **The inverse of an invertible induced morphism is induced by the inverse arrow.** -/
public theorem Induced.ofInv {N₁ N₂ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {g : N₂ ⟶ N₁}
    (hgf : g ≫ f = 𝟙 N₂) (U : C'ᵒᵖ) {A A' : C} (u : A' ⟶ A) (u' : A ⟶ A')
    (hu : u' ≫ u = 𝟙 A)
    (e₁ : ↥(N₁.val.obj U) = ↥(M.val.obj (op A))) (e₂ : ↥(N₂.val.obj U) = ↥(M.val.obj (op A')))
    (h : ∀ y, cast e₂ (f.val.app U y) = M.val.map u.op (cast e₁ y)) :
    Induced M g U A' A := by
  refine ⟨u', e₂, e₁, fun z => ?_⟩
  have hz : f.val.app U (g.val.app U z) = z :=
    congrArg (fun k : N₂ ⟶ N₂ => k.val.app U z) hgf
  have key : cast e₂ z = M.val.map u.op (cast e₁ (g.val.app U z)) :=
    Eq.trans (congrArg (cast e₂) hz.symm) (h (g.val.app U z))
  refine Eq.trans ?_ (congrArg (fun y => M.val.map u'.op y) key).symm
  refine Eq.trans ?_ (val_map_map M u' u (cast e₁ (g.val.app U z))).symm
  exact Eq.trans (val_map_id M (cast e₁ (g.val.app U z))).symm
    (congrArg (fun v : A ⟶ A => M.val.map v.op (cast e₁ (g.val.app U z))) hu.symm)

end Generic

section PushforwardPushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (eqv : C ≌ D)
  {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
  [eqv.functor.IsContinuous J K] [eqv.inverse.IsContinuous K J]
  (φ : S ⟶ (eqv.functor.sheafPushforwardContinuous RingCat.{w} J K).obj R)
  (ψ : R ⟶ (eqv.inverse.sheafPushforwardContinuous RingCat.{w} K J).obj S)
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit) R.obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) S.obj = 𝟙 S.obj)

/-- **The inverse of the unit of a pushforward-pushforward equivalence is restriction along the
inverse of the counit of the equivalence of sites.** -/
public theorem Induced.pushforwardPushforwardEquivalenceUnitIsoInv
    (M : SheafOfModules.{m} R) (U : Dᵒᵖ) :
    Induced M
      ((SheafOfModules.pushforwardPushforwardEquivalence.{m} eqv φ ψ H₁ H₂).unitIso.inv.app M) U
      (eqv.functor.obj (eqv.inverse.obj U.unop)) U.unop :=
  Induced.ofInv
    ((SheafOfModules.pushforwardPushforwardEquivalence.{m} eqv φ ψ H₁ H₂).unitIso.inv_hom_id_app M)
    U (eqv.counit.app U.unop) (eqv.counitIso.inv.app U.unop)
    (eqv.counitIso.inv_hom_id_app U.unop) rfl rfl
    (fun y => SheafOfModules.pushforwardPushforwardEquivalence_unit_app_val_app
      eqv φ ψ H₁ H₂ M U y)

/-- **The inverse of the counit of a pushforward-pushforward equivalence is restriction along the
inverse of the unit of the equivalence of sites.** -/
public theorem Induced.pushforwardPushforwardEquivalenceCounitIsoInv
    (N : SheafOfModules.{m} S) (U : Cᵒᵖ) :
    Induced N
      ((SheafOfModules.pushforwardPushforwardEquivalence.{m} eqv φ ψ H₁ H₂).counitIso.inv.app N) U
      U.unop (eqv.inverse.obj (eqv.functor.obj U.unop)) :=
  Induced.ofInv
    ((SheafOfModules.pushforwardPushforwardEquivalence.{m} eqv φ ψ
      H₁ H₂).counitIso.inv_hom_id_app N)
    U (eqv.unit.app U.unop) (eqv.unitIso.inv.app U.unop)
    (eqv.unitIso.inv_hom_id_app U.unop) rfl rfl
    (fun y => SheafOfModules.pushforwardPushforwardEquivalence_counit_app_val_app
      eqv φ ψ H₁ H₂ N U y)

end PushforwardPushforward

end Stacks.SectionsComponents

namespace AlgebraicGeometry.SmallEtale

/-- **The forward direction of the comparison of the two composite restrictions is restriction
along the base change of an open.** -/
theorem induced_restrictModuleBaseChangeIso_hom (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    (a : X ⟶ Y) (M : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (V : Y.obj.Opens) :
    Stacks.SectionsComponents.Induced M
      ((restrictModuleBaseChangeIso B a).hom.app M) (op V)
      ((smallEtaleBaseChange B a).obj (opensObj B Y.obj Y.property V))
      (opensObj B X.obj X.property ((schemeHom B a) ⁻¹ᵁ V)) :=
  ⟨(baseChangeOpensIso B a).hom.app V, rfl, rfl, fun _ => rfl⟩

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inverse of the unit of the equivalence of module categories of Stacks 03DX (2) is
restriction along the inverse of the counit of the equivalence of sites.**  Over an object `T` of
the small étale site of the scheme underlying `C`, the unit is restriction along
`AlgebraicGeometry.Space.representedModuleSiteEquivalence_unit_app_val_app`; that arrow of the
site is invertible, so the inverse of the unit is restriction along its inverse. -/
theorem induced_representedModuleSiteEquivalence_unitIso_inv (C : BigFppfOver B S hS)
    (M : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj C) C.left.property))
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj C) C.left.property) :
    Stacks.SectionsComponents.Induced M
      ((representedModuleSiteEquivalence B S hS C).unitIso.inv.app M) (op T)
      ((representedSmallEtaleEquivalence B S hS C).functor.obj
        ((representedSmallEtaleEquivalence B S hS C).inverse.obj T)) T :=
  Stacks.SectionsComponents.Induced.pushforwardPushforwardEquivalenceUnitIsoInv
    (representedSmallEtaleEquivalence B S hS C) (representedStructureMap B S hS C)
    (representedStructureMapInverse B S hS C)
    (representedStructureMap_counit_coherence B S hS C)
    (representedStructureMap_unit_coherence B S hS C) M (op T)

/-- **The inverse of the counit of the equivalence of module categories of Stacks 03DX (2) is
restriction along the inverse of the unit of the equivalence of sites.**  Over an object `Z` of
the small étale site of the represented algebraic space the counit is restriction along the unit
of the equivalence of sites, and that arrow is invertible. -/
theorem induced_representedModuleSiteEquivalence_counitIso_inv (C : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2)
    (Z : SmallEtale B S hS (schemeSpace C).1) :
    Stacks.SectionsComponents.Induced N
      ((representedModuleSiteEquivalence B S hS C).counitIso.inv.app N) (op Z) Z
      ((representedSmallEtaleEquivalence B S hS C).inverse.obj
        ((representedSmallEtaleEquivalence B S hS C).functor.obj Z)) :=
  Stacks.SectionsComponents.Induced.pushforwardPushforwardEquivalenceCounitIsoInv
    (representedSmallEtaleEquivalence B S hS C) (representedStructureMap B S hS C)
    (representedStructureMapInverse B S hS C)
    (representedStructureMap_counit_coherence B S hS C)
    (representedStructureMap_unit_coherence B S hS C) N (op Z)

/-- **The inverse of the counit of the equivalence of module categories of Stacks 03DX (2) is
restriction along the inverse of the unit of the equivalence of sites**, in the spelling
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` of that equivalence.

This is the same statement as
`AlgebraicGeometry.Space.induced_representedModuleSiteEquivalence_counitIso_inv`, in the spelling
the square of direct images is written in — the two spellings are one equivalence, but a defeq
between them inside a composite applied to an object is not free, so the factors of
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoCollapse` need the reading
in their own spelling.  Both are instances of
`Stacks.SectionsComponents.Induced.pushforwardPushforwardEquivalenceCounitIsoInv`; here the two
structure comparisons are the identity and
`Stacks.SheafOfModules.reindexBackSharp`. -/
theorem induced_representedSmallEtaleModuleEquivalence_counitIso_inv (C : BigFppfOver B S hS)
    (N : SheafOfModules.{u} (representedStructureRingSheaf B S hS C))
    (Z : SmallEtale B S hS (yoneda.obj C)) :
    Stacks.SectionsComponents.Induced N
      ((representedSmallEtaleModuleEquivalence B S hS C).counitIso.inv.app N) (op Z) Z
      ((representedSmallEtaleEquivalence B S hS C).inverse.obj
        ((representedSmallEtaleEquivalence B S hS C).functor.obj Z)) :=
  induced_representedModuleSiteEquivalence_counitIso_inv B S hS C N Z

/-- **The inverse of the unit of the equivalence of module categories of Stacks 03DX (2) is
restriction along the inverse of the counit of the equivalence of sites**, in the spelling
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` of that equivalence. -/
theorem induced_representedSmallEtaleModuleEquivalence_unitIso_inv (C : BigFppfOver B S hS)
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS C))
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj C) C.left.property) :
    Stacks.SectionsComponents.Induced M
      ((representedSmallEtaleModuleEquivalence B S hS C).unitIso.inv.app M) (op T)
      ((representedSmallEtaleEquivalence B S hS C).functor.obj
        ((representedSmallEtaleEquivalence B S hS C).inverse.obj T)) T :=
  induced_representedModuleSiteEquivalence_unitIso_inv B S hS C M T

/-! ### The comparison of the two composite right adjoints, read on sections

`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso` is read here factor by factor in
its `inv` direction.  Every factor but one is restriction along an arrow of the small étale site of
`yoneda.obj U`; the exception is the chart comparison
`AlgebraicGeometry.Space.modulePushforwardChartIso`, which is the chart projection, so the whole
composite is **not** `Stacks.SectionsComponents.Induced` and the reading is split: an associator,
which is the identity on sections, then the chart projection two direct images deep, then the
*tail* — and the tail is a single restriction,
`AlgebraicGeometry.Space.induced_representedRestrictModuleBaseChangeIso_inv_tail`.

Each step is stated as its own declaration with every functor spelled out.  That is forced twice
over.  A leaf applied directly to one of the concrete composites leaves the sheaf of rings of the
intermediate modules to unification, and the unifier reduces the sheaves of modules instead of the
functors: `Stacks.SectionsComponents.Induced.descendReindex`,
`…reindexInverseMap` and `…pushforwardMap` each exhaust the heartbeat budget at `whnf` that way,
and each becomes instant when the modules are pinned by an intermediate statement whose morphism is
a variable.  And the structural factors of
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoUnit` can only be absorbed
after
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoUnit_eq_explicit` has replaced
that definition by its chain of four factors: the identification is `rfl` at the top level of a
statement and exhausts the heartbeat budget inside `Induced M (·.inv.app M) …`.
-/

section Sections

variable {U V : BigFppfOver B S hS} (ψ : U ⟶ V)

/-- **The restriction half of the square of direct images, in its `inv` direction, is restriction
along an arrow of the small étale site of the scheme underlying `U`.**  Over an object `Zv` of the
small étale site of `yoneda.obj V` it carries the sections over the base change of `Zv`, read as a
chart of the scheme underlying `U`, to the sections over the base change of the chart of the scheme
underlying `V` that `Zv` is.

Its three factors are two contractions of an iterated direct image, which are the identity on
sections, and the transport of a direct image along
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`, which is restriction along that
isomorphism of sites — so this is the content of the claim that every factor of
`AlgebraicGeometry.Space.representedModulePushforwardSquareRestrictIso` is a restriction of
sections. -/
theorem induced_representedModulePushforwardSquareRestrictIso_inv
    (N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U))
    (Zv : SmallEtale B S hS (yoneda.obj V)) :
    Stacks.SectionsComponents.Induced N
      ((representedModulePushforwardSquareRestrictIso B S hS ψ
        (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app N) (op Zv)
      ((representedSmallEtaleEquivalence B S hS U).functor.obj
        ((smallBaseChange B S hS (representedSpaceMap B S hS ψ)
          (relativelyRepresentable_yoneda_map B S hS ψ)).obj Zv))
      ((representedSchemeBaseChange B S hS ψ).obj
        ((representedSmallEtaleEquivalence B S hS V).functor.obj Zv)) :=
  Stacks.SectionsComponents.Induced.isoTransInv N _ _
    (Stacks.SectionsComponents.Induced.isoTransInv N _ _
      (Stacks.SectionsComponents.Induced.isoSymmInv _ _
        (@Stacks.SectionsComponents.Induced.pushforwardCompHom ..))
      (@Stacks.SectionsComponents.Induced.pushforwardCongr₂Inv ..))
    (@Stacks.SectionsComponents.Induced.pushforwardCompInv ..)

/-- **A morphism of `𝒪`-modules on the small étale site of `yoneda.obj V` which is restriction
along an arrow of the small étale site of the scheme underlying `U` is restriction along the image
of that arrow on the small étale site of `yoneda.obj U`.**  This is
`Stacks.SectionsComponents.Induced.descendReindex` at the comparison equivalence of module
categories of `U`, with the two sheaves of modules pinned: applied directly to a concrete morphism
it leaves the sheaf of rings of those modules to unification and exhausts the heartbeat budget at
`whnf`. -/
theorem induced_of_induced_representedSmallEtaleModuleEquivalence_inverse
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (Zv : SmallEtale B S hS (yoneda.obj V))
    {N₁ N₂ : SheafOfModules.{u} (representedStructureRingSheaf B S hS V)} (f : N₁ ⟶ N₂)
    (a a' : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (h : Stacks.SectionsComponents.Induced
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M) f (op Zv) a a') :
    Stacks.SectionsComponents.Induced M f (op Zv)
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj a)
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj a') :=
  Stacks.SectionsComponents.Induced.descendReindex
    (J := SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U) (representedSchemeStructureSheaf B S hS U) M h

/-- **The restriction half of the square of direct images at the transported module, read on the
small étale site of `yoneda.obj U`.**  This is
`AlgebraicGeometry.Space.induced_representedModulePushforwardSquareRestrictIso_inv` with its arrow
carried from the small étale site of the scheme underlying `U` to the small étale site of
`yoneda.obj U`. -/
theorem induced_representedModulePushforwardSquareRestrictIso_inv_app
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (Zv : SmallEtale B S hS (yoneda.obj V)) :
    Stacks.SectionsComponents.Induced M
      ((representedModulePushforwardSquareRestrictIso B S hS ψ
          (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M)) (op Zv)
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((representedSmallEtaleEquivalence B S hS U).functor.obj
          ((smallBaseChange B S hS (representedSpaceMap B S hS ψ)
            (relativelyRepresentable_yoneda_map B S hS ψ)).obj Zv)))
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((representedSchemeBaseChange B S hS ψ).obj
          ((representedSmallEtaleEquivalence B S hS V).functor.obj Zv))) :=
  induced_of_induced_representedSmallEtaleModuleEquivalence_inverse B S hS M Zv _ _ _
    (induced_representedModulePushforwardSquareRestrictIso_inv B S hS ψ
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M) Zv)

/-- **The two factors of the collapsing half of the square which sit beside the chart comparison
are, together, restriction along an arrow of the small étale site of `yoneda.obj U`.**  They are
the base-change direct image of the inverse of the counit of the equivalence of module categories
of `U`, which is restriction along the unit of the equivalence of sites over the base-changed
chart, and the restriction half of the square; and the arrow of the first ends where the arrow of
the second begins. -/
theorem induced_smallBaseChangeModulePushforward_counitInv_comp
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (Zv : SmallEtale B S hS (yoneda.obj V)) :
    Stacks.SectionsComponents.Induced M
      ((smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS ψ)
              (relativelyRepresentable_yoneda_map B S hS ψ)).map
            ((representedSmallEtaleModuleEquivalence B S hS U).counitInv.app M) ≫
        (representedModulePushforwardSquareRestrictIso B S hS ψ
              (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M)) (op Zv)
      ((smallBaseChange B S hS (representedSpaceMap B S hS ψ)
        (relativelyRepresentable_yoneda_map B S hS ψ)).obj Zv)
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((representedSchemeBaseChange B S hS ψ).obj
          ((representedSmallEtaleEquivalence B S hS V).functor.obj Zv))) :=
  Stacks.SectionsComponents.Induced.comp
    (Stacks.SectionsComponents.Induced.pushforwardMap
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS ψ)
        (relativelyRepresentable_yoneda_map B S hS ψ)) _
      (induced_representedSmallEtaleModuleEquivalence_counitIso_inv B S hS U M _))
    (induced_representedModulePushforwardSquareRestrictIso_inv_app B S hS ψ M Zv)

/-- **A morphism of `𝒪`-modules on the small étale site of `yoneda.obj V` which is restriction
along an arrow of the small étale site of `yoneda.obj U` stays one after the comparison equivalence
of module categories of `V` has read it on the small étale site of the scheme underlying `V`.**
This is `Stacks.SectionsComponents.Induced.reindexInverseMap` at that equivalence, with the two
sheaves of modules pinned for the same reason as in
`AlgebraicGeometry.Space.induced_of_induced_representedSmallEtaleModuleEquivalence_inverse`. -/
theorem induced_representedSmallEtaleModuleEquivalence_inverse_map
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (Tv : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
    {N₁ N₂ : SheafOfModules.{u} (representedStructureRingSheaf B S hS V)} (f : N₁ ⟶ N₂)
    (a a' : SmallEtale B S hS (yoneda.obj U))
    (h : Stacks.SectionsComponents.Induced M f
      (op ((representedSmallEtaleEquivalence B S hS V).inverse.obj Tv)) a a') :
    Stacks.SectionsComponents.Induced M
      ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map f) (op Tv) a a' :=
  Stacks.SectionsComponents.Induced.reindexInverseMap
    (J₀ := SmallEtale.topology B S hS (yoneda.obj V))
    (representedSmallEtaleEquivalence B S hS V) (representedSchemeStructureSheaf B S hS V) f h

/-- **A morphism of modules on the small étale site of the scheme underlying `V` which is
restriction along an arrow of the small étale site of `yoneda.obj U` is one over an open of that
scheme.**  This is `Stacks.SectionsComponents.Induced.pushforwardMap` at the restriction to the
small Zariski site, with the two sheaves of modules pinned. -/
theorem induced_restrictModule_map
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    {N₁ N₂ : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS V)} (f : N₁ ⟶ N₂)
    (a a' : SmallEtale B S hS (yoneda.obj U))
    (h : Stacks.SectionsComponents.Induced M f
      (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property O)) a a') :
    Stacks.SectionsComponents.Induced M
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map f) (op O) a a' :=
  Stacks.SectionsComponents.Induced.pushforwardMap
    (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property) f h

/-- **The unit of the equivalence of module categories of `V`, taken inside the direct image along
the morphism of small étale ringed sites of `ψ`, is restriction along the base change of the counit
of the equivalence of sites of `V`.** -/
theorem induced_isoWhiskerLeft_representedSmallEtaleModuleEquivalence_unitIso_inv
    (N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U))
    (Tv : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property) :
    Stacks.SectionsComponents.Induced N ((Functor.isoWhiskerLeft
        (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ))
        (representedSmallEtaleModuleEquivalence B S hS V).unitIso).inv.app N) (op Tv)
      ((representedSchemeBaseChange B S hS ψ).obj
        ((representedSmallEtaleEquivalence B S hS V).functor.obj
          ((representedSmallEtaleEquivalence B S hS V).inverse.obj Tv)))
      ((representedSchemeBaseChange B S hS ψ).obj Tv) :=
  Stacks.SectionsComponents.Induced.isoWhiskerLeftInv N
    (representedSchemeStructureMapRing B S hS ψ) _
    (induced_representedSmallEtaleModuleEquivalence_unitIso_inv B S hS V _ Tv)

/-- **An isomorphism of functors out of the modules on the small étale site of the scheme
underlying `U` which is restriction along an arrow of that site, whiskered on the left by the
comparison equivalence of module categories of `U`, is restriction along the image of that
arrow.**  This is `Stacks.SectionsComponents.Induced.isoWhiskerLeftReindexInv` with the isomorphism
left a variable, so that the two categories of the whiskering are pinned by this statement rather
than unified against a concrete chain.

The ringed site the isomorphism lands on is a variable too: the whiskering arises both with the
small étale site of the scheme underlying `V` for its target, in the unit half of the square of
direct images, and with the small Zariski site of that scheme, in the base-change half of the
comparison of the two composite right adjoints. -/
theorem induced_isoWhiskerLeft_representedSmallEtaleModuleEquivalence_inverse_inv
    {C' : Type*} [Category C'] {J' : GrothendieckTopology C'} {S' : Sheaf J' RingCat.{u}}
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) (Z : C'ᵒᵖ)
    {F' G' : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U) ⥤
      SheafOfModules.{u} S'} (α : F' ≅ G')
    (a a' : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (h : Stacks.SectionsComponents.Induced
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M)
      (α.inv.app ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M))
      Z a a') :
    Stacks.SectionsComponents.Induced M ((Functor.isoWhiskerLeft
        (representedSmallEtaleModuleEquivalence B S hS U).inverse α).inv.app M) Z
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj a)
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj a') :=
  Stacks.SectionsComponents.Induced.isoWhiskerLeftReindexInv
    (J := SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U) (representedSchemeStructureSheaf B S hS U) M α h

/-- **The one factor of the unit half of the square of direct images which moves a section**: the
unit of the equivalence of module categories of `V`, inserted on the right of the composite and
whiskered by the two direct images, is restriction along the base change of the counit of the
equivalence of sites of `V`, read on the small étale site of `yoneda.obj U`. -/
theorem induced_representedModulePushforwardSquareInverseIsoUnit_unitFactor_inv
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (Tv : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property) :
    Stacks.SectionsComponents.Induced M ((Functor.isoWhiskerLeft
        (representedSmallEtaleModuleEquivalence B S hS U).inverse
        (Functor.isoWhiskerLeft
          (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ))
          (representedSmallEtaleModuleEquivalence B S hS V).unitIso)).inv.app M) (op Tv)
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((representedSchemeBaseChange B S hS ψ).obj
          ((representedSmallEtaleEquivalence B S hS V).functor.obj
            ((representedSmallEtaleEquivalence B S hS V).inverse.obj Tv))))
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((representedSchemeBaseChange B S hS ψ).obj Tv)) :=
  induced_isoWhiskerLeft_representedSmallEtaleModuleEquivalence_inverse_inv B S hS M (op Tv) _ _ _
    (induced_isoWhiskerLeft_representedSmallEtaleModuleEquivalence_unitIso_inv B S hS ψ _ Tv)

/-- **The unit half of the square of direct images, with its four factors written out.**  It holds
by `rfl`, the half being *defined* as that chain, and it is needed because the identification is
free only at the top level of a statement: inside
`Stacks.SectionsComponents.Induced M (·.inv.app M) …` the unifier reduces the sheaves of modules
instead of the functors and exhausts the heartbeat budget at `whnf`, at all three of the
`Stacks.SectionsComponents.Induced` combinators that consume this chain. -/
theorem representedModulePushforwardSquareInverseIsoUnit_eq_explicit :
    representedModulePushforwardSquareInverseIsoUnit B S hS ψ =
      Functor.isoWhiskerLeft (representedSmallEtaleModuleEquivalence B S hS U).inverse
          (Functor.rightUnitor
            (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ))).symm ≪≫
        (Functor.isoWhiskerLeft (representedSmallEtaleModuleEquivalence B S hS U).inverse
            (Functor.isoWhiskerLeft
              (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ))
              (representedSmallEtaleModuleEquivalence B S hS V).unitIso) ≪≫
          (Functor.isoWhiskerLeft (representedSmallEtaleModuleEquivalence B S hS U).inverse
              (Functor.associator
                (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ))
                (representedSmallEtaleModuleEquivalence B S hS V).functor
                (representedSmallEtaleModuleEquivalence B S hS V).inverse).symm ≪≫
            (Functor.associator (representedSmallEtaleModuleEquivalence B S hS U).inverse
              (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS ψ) ⋙
                (representedSmallEtaleModuleEquivalence B S hS V).functor)
              (representedSmallEtaleModuleEquivalence B S hS V).inverse).symm)) :=
  rfl

/-- **The unit half of the square of direct images, in its `inv` direction, is restriction along
the base change of the counit of the equivalence of sites of `V`.**  Three of its four factors — a
right unitor and two associators — are the identity on sections and are absorbed by
`Stacks.SectionsComponents.Induced.isoTransInvIdRight` and `…IdLeft`, which name no object of the
site for the factor they absorb; the fourth is the unit of the equivalence of module categories of
`V`, which is not. -/
theorem induced_representedModulePushforwardSquareInverseIsoUnit_inv
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (Tv : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property) :
    Stacks.SectionsComponents.Induced M
      ((representedModulePushforwardSquareInverseIsoUnit B S hS ψ).inv.app M) (op Tv)
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((representedSchemeBaseChange B S hS ψ).obj
          ((representedSmallEtaleEquivalence B S hS V).functor.obj
            ((representedSmallEtaleEquivalence B S hS V).inverse.obj Tv))))
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((representedSchemeBaseChange B S hS ψ).obj Tv)) := by
  rw [representedModulePushforwardSquareInverseIsoUnit_eq_explicit]
  exact Stacks.SectionsComponents.Induced.isoTransInvIdRight M _ _ rfl (fun _ => rfl)
    (Stacks.SectionsComponents.Induced.isoTransInvIdLeft M _ _ rfl (fun _ => rfl)
      (induced_representedModulePushforwardSquareInverseIsoUnit_unitFactor_inv B S hS ψ M Tv))

/-- **The base-change half of the comparison of the two composite right adjoints, in its `inv`
direction, is restriction along the base change of an open.**  Over an open `O` of the scheme
underlying `V` it carries the sections over the base change of `O`, read as a chart of the scheme
underlying `U`, to the sections over the open `ψ^{-1}O`.

Its outer two factors are associators, which are the identity on sections; the middle one is
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso`, read by
`AlgebraicGeometry.SmallEtale.induced_restrictModuleBaseChangeIso_hom`. -/
theorem induced_representedRestrictModuleBaseChangeIsoBaseChange_inv
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    Stacks.SectionsComponents.Induced M
      ((representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).inv.app M) (op O)
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((representedSchemeBaseChange B S hS ψ).obj
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property O)))
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ψ.left ⁻¹ᵁ
            O))) :=
  Stacks.SectionsComponents.Induced.isoTransInvIdRight M _ _ rfl (fun _ => rfl)
    (Stacks.SectionsComponents.Induced.isoTransInvIdLeft M _ _ rfl (fun _ => rfl)
      (induced_isoWhiskerLeft_representedSmallEtaleModuleEquivalence_inverse_inv B S hS M (op O) _
        _ _
        (Stacks.SectionsComponents.Induced.isoSymmInv _ _
          (_root_.AlgebraicGeometry.SmallEtale.induced_restrictModuleBaseChangeIso_hom
            (associatedBigEtaleSite B) ψ.left _ O))))

/-- **The tail of the comparison of the two composite right adjoints round the square of
Stacks 03LC (1), in its `inv` direction, is restriction along a single arrow of the small étale
site of `yoneda.obj U`** — from the base change along `ψ̃` of the open `O` of the scheme underlying
`V`, read as a chart of `yoneda.obj U`, to the open `ψ^{-1}O` of the scheme underlying `U`, read as
a chart of `yoneda.obj U`.

The tail is everything after the chart comparison
`AlgebraicGeometry.Space.modulePushforwardChartIso`, which is the one factor of the comparison that
is *not* a restriction of sections: by
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app`,
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIso_inv_app` and
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIsoCollapse_inv_app_chartFirst`,
the comparison's `inv` at `M` is an associator, which is the identity on sections, then that chart
comparison inside two direct images, then this.

Its six factors are, in order: the base-change direct image of the inverse of the counit of the
equivalence of module categories of `U`; the three factors of
`AlgebraicGeometry.Space.representedModulePushforwardSquareRestrictIso`; the unit half of the
square of direct images; and the base-change half of the comparison. -/
theorem induced_representedRestrictModuleBaseChangeIso_inv_tail
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    Stacks.SectionsComponents.Induced M
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
            ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
                ((smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS ψ)
                        (relativelyRepresentable_yoneda_map B S hS ψ)).map
                      ((representedSmallEtaleModuleEquivalence B S hS U).counitInv.app M) ≫
                  (representedModulePushforwardSquareRestrictIso B S hS ψ
                        (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
                      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M)) ≫
              (representedModulePushforwardSquareInverseIsoUnit B S hS ψ).inv.app M) ≫
        (representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).inv.app M) (op O)
      ((smallBaseChange B S hS (representedSpaceMap B S hS ψ)
          (relativelyRepresentable_yoneda_map B S hS ψ)).obj
        ((representedSmallEtaleEquivalence B S hS V).inverse.obj
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property O)))
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ψ.left ⁻¹ᵁ
            O))) :=
  Stacks.SectionsComponents.Induced.comp
    (induced_restrictModule_map B S hS M O _ _ _
      (Stacks.SectionsComponents.Induced.comp
        (induced_representedSmallEtaleModuleEquivalence_inverse_map B S hS M _ _ _ _
          (induced_smallBaseChangeModulePushforward_counitInv_comp B S hS ψ M _))
        (induced_representedModulePushforwardSquareInverseIsoUnit_inv B S hS ψ M _)))
    (induced_representedRestrictModuleBaseChangeIsoBaseChange_inv B S hS ψ M O)

/-- **The three-way split of the comparison of the two composite right adjoints round the square
of Stacks 03LC (1), in its `inv` direction at a module**: it is the chart comparison
`AlgebraicGeometry.Space.modulePushforwardChartIso`, taken inside the reading-back along `V`'s
equivalence of module categories and then inside the restriction to the small Zariski site of the
scheme underlying `V`, followed by the tail of
`AlgebraicGeometry.Space.induced_representedRestrictModuleBaseChangeIso_inv_tail`.

The chart comparison is the one factor of the comparison which is *not* a restriction of sections
— `AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_chartSetProj` reads it off as the
chart projection — which is why the split is three-way and not an `inv` which is itself
`Stacks.SectionsComponents.Induced`.

The equation is stated of the reading of
`representedRestrictModuleBaseChangeIso_inv_app_smallEtaleModuleEquivalence`, the one bridge
between the two spellings of the equivalence of module categories, so that every term of it is in
the spelling of the factors; a consumer which starts from
`(representedRestrictModuleBaseChangeIso B S hS ψ).inv.app M` rewrites with that bridge once and
is then here.

Its four steps are the factorisation of the comparison into its two named factors, the square half
at a module, the factorisation of the square of direct images into its two named factors, and the
exchanged factorisation of the collapsing factor — all of them `rfl` in this spelling — followed
by one reassociation, `CategoryTheory.map_map_comp_assoc`, which peels the chart factor off the
front through the two direct images.  That reassociation has to be a lemma stated on variables:
`CategoryTheory.Category.assoc` and `CategoryTheory.Functor.map_comp` with metavariable
arguments both exhaust the heartbeat budget at `whnf` at these two module categories. -/
theorem representedRestrictModuleBaseChangeIso_inv_app_chartFirst
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
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
            ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS ψ)
              (relativelyRepresentable_yoneda_map B S hS ψ)).hom.app M)) ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
              ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
                  ((smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS ψ)
                          (relativelyRepresentable_yoneda_map B S hS ψ)).map
                        ((representedSmallEtaleModuleEquivalence B S hS U).counitInv.app M) ≫
                    (representedModulePushforwardSquareRestrictIso B S hS ψ
                          (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
                        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M)) ≫
                (representedModulePushforwardSquareInverseIsoUnit B S hS ψ).inv.app M) ≫
          (representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).inv.app M := by
  rw [representedRestrictModuleBaseChangeIso_inv_app,
    representedRestrictModuleBaseChangeIsoSquare_inv_app,
    representedModulePushforwardSquareInverseIso_inv_app,
    representedModulePushforwardSquareInverseIsoCollapse_inv_app_chartFirst]
  exact map_map_comp_assoc _ _ _ _ _ _

end Sections

end AlgebraicGeometry.Space

end
