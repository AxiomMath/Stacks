module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackIdIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedKernelIdealSquareMapAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleObjPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackIdUnitLaw
public import StacksFrontier.CategoryTheory.PseudofunctorMorphismUnit

/-!
# The transport of the inverse image at the identity of the site

`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` carries the inverse image of
`𝒪`-modules of [Stacks Project, Tag 03LU] along a represented morphism of algebraic spaces, read
at the associated module of a Zariski module, onto the associated module of the Zariski pullback.
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp` is its compatibility with
composition.  This file is its value at the **identity** of the big fppf category: the
*identity-vertical bridge*, which is what lets a square one of whose verticals is an identity be
compared with the change-of-ambient agreement
`AlgebraicGeometry.Space.conormalChangeOfAmbientAgreement`, whose left vertical is the identity of
the represented algebraic space.  It is a step of part (2) of [Stacks Project, Tag 04G2].

The derivation asks for no new geometry.  A morphism of pseudofunctors has its unit law forced by
its composition law together with the unit laws of the two pseudofunctors it compares — that is
`StacksFrontier/CategoryTheory/PseudofunctorMorphismUnit.lean`, the analogue for a morphism of
pseudofunctors of what
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardUnitLaws.lean` proves for a
pseudofunctor.  Here the two pseudofunctors are the inverse image of `𝒪`-modules of 03LU on the
spaces side and `AlgebraicGeometry.Scheme.Modules.pullback` on the Zariski side, and the morphism
between them is the transport.

So the composition law at the identity, the naturality of the transport in the module, and the
two pseudofunctors' own unit laws determine the transport at the identity, and the bridge is
proved here with nothing assumed.

## Main results

* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_id`: the composition law
  for the transport at the identity of the site for both factors.
* `AlgebraicGeometry.Space.map_representedAssociatedModulePullbackIso_id`: **the coherence-free
  half of the bridge** — the component of the composition comparison of 03LU at the represented
  identity, read at an associated module, is the transport there followed by the associated
  module of the Zariski unit law.  No unit law of 03LU enters.
* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_representedSpaceMap_id`: **the unit law
  of [Stacks Project, Tag 03LU] at the represented identity**, which is the hypothesis `hm`
  below.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_id_of_unitLaws`: the
  identity-vertical bridge from the two unit laws.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_id`: **the identity-vertical
  bridge, with nothing assumed.**

## The two unit laws, and where each comes from

`hn` is the unit law of the Zariski inverse image.  Mathlib states it as
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality`, an equation of natural
transformations; solved for the component of the composition comparison it is
`AlgebraicGeometry.Scheme.Modules.pullbackComp_id_id_hom_app`.  No transport is needed to apply
it here: the morphism of schemes which the represented identity induces,
`B.inclusion.map (Over.Hom.left (𝟙 T))`, is the identity of `(BigFppfOver.toScheme B S hS).obj T`
by definitional unfolding, so `hn` is that unit law at a literal identity.

`hm` is the unit law of [Stacks Project, Tag 03LU] at the represented identity: that the
composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` at a pair of represented
identities is the comparison `AlgebraicGeometry.Space.modulePullbackIdIso` of the inverse image
along an identity with the identity functor, transported along
`AlgebraicGeometry.Space.representedSpaceMap_id`.  **The transport cannot be dropped**: unlike its
Zariski counterpart, `representedSpaceMap (𝟙 T)` is the identity of the represented algebraic
space only propositionally.

`hm` rests on two facts.
`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIso_id_left` is the law for
`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackIdIso`, built from the `idIso`
field of a coherence; and the coherence this repository constructs,
`AlgebraicGeometry.Space.modulePushforwardCoherence`, takes for that field the *normalisation*
`CategoryTheory.Functor.idIsoOfCompIso` of `AlgebraicGeometry.Space.modulePushforwardIdIso`
against the composition comparison at a pair of identities, not
`AlgebraicGeometry.Space.modulePushforwardIdIso` itself — that normalisation is exactly what
`AlgebraicGeometry.Space.modulePushforwardCoherenceOfIdIso` does to avoid proving a unit law.  So
the law held for the normalised identification and had to be moved to the one that carries the
03LU tag, which is
`AlgebraicGeometry.Space.modulePushforwardCoherence_modulePullbackIdIso`, resting in turn on the
direct image's own unit law at a pair of identities,
`AlgebraicGeometry.Space.modulePushforwardCompIso_id_id_hom_app`.  Both are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardIdUnitLaw.lean`.  The transport
along `representedSpaceMap_id` is then
`AlgebraicGeometry.Space.modulePullbackCompIso_of_eq_id` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackIdUnitLaw.lean`, which carries it
out between isomorphisms of functors because at the level of a component the same substitution is
a kernel deterministic timeout.

## Implementation notes

**Every statement here is at the identity written as `𝟙 T`, while the composition law is
indexed by a pair of morphisms and so meets the identity as `𝟙 T ≫ 𝟙 T`; identifying the two is
`rfl`, and it is affordable only in a declaration of its own.**  Concretely, the composition law
restated verbatim at `p = q = 𝟙 T`, with the composite left written `𝟙 T ≫ 𝟙 T`, checks in one
second; the same restatement with `𝟙 T` in that one place is a kernel deterministic timeout, with
no elaboration error — while
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_id_comp`, which is that
identification alone and at the level of isomorphisms, is free.  So it is proved there and
carried by `congrArg`.

**The generic unit law is instantiated in two halves and through its algebraic skeleton, not in
one application.**  `Stacks.CategoryTheory.transportApp_of_compLaw_of_idIso` abstracts over three
functors, and at this instantiation the source and target of the transport are two *spellings* of
one category — `AlgebraicGeometry.Space.Modules` and the `CategoryTheory.SheafOfModules` it
unfolds to — so matching them is a kernel deterministic timeout even with the functors passed by
name and every composition comparison weakened to its components.  A `rewrite` cannot bridge the
two spellings at all: the pattern and the target print identically and differ in the category
instance that `CategoryTheory.CategoryStruct.comp` carries.  What works is a term application
of a lemma proved at plain variables, which unifies up to definitional equality:
`Stacks.CategoryTheory.map_comp_eq_of_cancel` and
`Stacks.CategoryTheory.eq_app_comp_of_map_comp_eq`, the two halves of the generic law with every
functor but the one whose image is taken replaced by plain objects and morphisms.

**The naturality of the transport must have its two modules passed by name.**  Left implicit they
are inferred from the morphism `(Scheme.Modules.pullbackId _).hom.app 𝓕`, whose source is spelled
with `𝟙` rather than with `AlgebraicGeometry.BigFppfSite.inclusion`, and the rewrite then reports
that it cannot find a pattern the goal displays.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local irreducible] modulePullback modulePullbackCompIso modulePushforward
  modulePushforwardCompIso modulePushforwardFactoredCompIso representedSmallEtaleEquivalence
  representedSmallEtaleModuleEquivalence representedAssociatedModulePullbackIso
  representedModuleObjPullbackIso representedModulePushforwardSquareIso
  smallBaseChange structureSheaf structureSheaf' structurePresheaf
  _root_.AlgebraicGeometry.SmallEtale.associatedModule
  _root_.AlgebraicGeometry.Scheme.Modules.pullback
  _root_.AlgebraicGeometry.Scheme.Modules.pullbackComp
  _root_.AlgebraicGeometry.Scheme.Modules.pullbackId

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) (h : yoneda.relativelyRepresentable (yoneda.map (𝟙 T)))

/-- The transport at the identity of the site does not depend on whether the identity is
presented as itself or as its own composite with itself.  Composition in `BigFppfOver` is unital
by definitional unfolding, so this is `rfl` — and it is **isolated in a declaration of its own
because it is affordable only there**: see the implementation notes. -/
theorem representedAssociatedModulePullbackIso_id_comp
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    representedAssociatedModulePullbackIso B S hS (𝟙 T ≫ 𝟙 T) h 𝓕 =
      representedAssociatedModulePullbackIso B S hS (𝟙 T) h 𝓕 :=
  rfl

/-- The composition law for the transport at an associated module, at the identity of the site
for both factors, in the shape the generic unit law consumes. -/
theorem representedAssociatedModulePullbackIso_comp_id
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    (modulePullback B S hS (representedSpaceMap B S hS (𝟙 T))).map
          (representedAssociatedModulePullbackIso B S hS (𝟙 T) h 𝓕).hom ≫
        (representedAssociatedModulePullbackIso B S hS (𝟙 T) h
            ((Scheme.Modules.pullback
              (B.inclusion.map (Over.Hom.left (𝟙 T)))).obj 𝓕)).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS T).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
              ((Scheme.Modules.pullbackComp (B.inclusion.map (Over.Hom.left (𝟙 T)))
                (B.inclusion.map (Over.Hom.left (𝟙 T)))).hom.app 𝓕)) =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS (𝟙 T))
            (representedSpaceMap B S hS (𝟙 T))).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕)) ≫
        (representedAssociatedModulePullbackIso B S hS (𝟙 T) h 𝓕).hom :=
  (representedAssociatedModulePullbackIso_comp B S hS (𝟙 T) (𝟙 T) h h h 𝓕).trans
    (congrArg (fun x ↦ _ ≫ x)
      (congrArg Iso.hom (representedAssociatedModulePullbackIso_id_comp B S hS T h 𝓕)))

/-- **The coherence-free half of the identity-vertical bridge.**  The component of the
composition comparison of [Stacks Project, Tag 03LU] at the represented identity, read at an
associated module, is the transport there followed by the associated module of the schemes-side
unit law.  No unit law of [Stacks Project, Tag 03LU] enters. -/
theorem map_representedAssociatedModulePullbackIso_id
    (hn : ∀ 𝓖 : ((BigFppfOver.toScheme B S hS).obj T).Modules,
      (Scheme.Modules.pullbackComp (B.inclusion.map (Over.Hom.left (𝟙 T)))
            (B.inclusion.map (Over.Hom.left (𝟙 T)))).hom.app 𝓖 =
        (Scheme.Modules.pullback (B.inclusion.map (Over.Hom.left (𝟙 T)))).map
          ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).hom.app 𝓖))
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    (modulePullback B S hS (representedSpaceMap B S hS (𝟙 T))).map
        ((representedAssociatedModulePullbackIso B S hS (𝟙 T) h 𝓕).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS T).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
              ((Scheme.Modules.pullbackId
                ((BigFppfOver.toScheme B S hS).obj T)).hom.app 𝓕))) =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS (𝟙 T))
            (representedSpaceMap B S hS (𝟙 T))).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕)) :=
    by
  have hcoc := representedAssociatedModulePullbackIso_comp_id B S hS T h 𝓕
  rw [hn 𝓕] at hcoc
  exact Stacks.CategoryTheory.map_comp_eq_of_cancel
    (modulePullback B S hS (representedSpaceMap B S hS (𝟙 T)))
    (representedAssociatedModulePullbackIso B S hS (𝟙 T) h 𝓕)
    ((representedSmallEtaleModuleEquivalence B S hS T).functor.map
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).hom.app 𝓕)))
    (representedAssociatedModulePullbackIso B S hS (𝟙 T) h
      ((Scheme.Modules.pullback (B.inclusion.map (Over.Hom.left (𝟙 T)))).obj 𝓕)).hom
    ((representedSmallEtaleModuleEquivalence B S hS T).functor.map
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((Scheme.Modules.pullback (B.inclusion.map (Over.Hom.left (𝟙 T)))).map
          ((Scheme.Modules.pullbackId
            ((BigFppfOver.toScheme B S hS).obj T)).hom.app 𝓕))))
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS (𝟙 T))
          (representedSpaceMap B S hS (𝟙 T))).hom.app
      ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj (
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕)))
    hcoc
    (representedAssociatedModulePullbackIso_naturality B S hS (𝟙 T) h
      (𝓕 := (Scheme.Modules.pullback
        (B.inclusion.map (Over.Hom.left (𝟙 T)))).obj 𝓕) (𝓖 := 𝓕)
      ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).hom.app 𝓕))
/-- **The identity-vertical bridge: the transport of the inverse image at the identity of the
site.**  Given the unit law `hm` of [Stacks Project, Tag 03LU] at the represented identity and the
unit law `hn` of the Zariski inverse image, the transport of the inverse image at the identity of
the site is the unit law of 03LU, transported along `representedSpaceMap_id`, followed by the
associated module of the inverse of the Zariski unit law. -/
theorem representedAssociatedModulePullbackIso_id_of_unitLaws
    (hm : ∀ Z : Modules.{u, u} B S hS
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS).1
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS).2,
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS (𝟙 T))
            (representedSpaceMap B S hS (𝟙 T))).hom.app Z =
        (eqToIso (congrArg (modulePullback B S hS) (representedSpaceMap_id B S hS T)) ≪≫
            modulePullbackIdIso B S hS
              (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :
                AlgebraicSpaces B S hS)).hom.app
          ((modulePullback B S hS (representedSpaceMap B S hS (𝟙 T))).obj Z))
    (hn : ∀ 𝓖 : ((BigFppfOver.toScheme B S hS).obj T).Modules,
      (Scheme.Modules.pullbackComp (B.inclusion.map (Over.Hom.left (𝟙 T)))
            (B.inclusion.map (Over.Hom.left (𝟙 T)))).hom.app 𝓖 =
        (Scheme.Modules.pullback (B.inclusion.map (Over.Hom.left (𝟙 T)))).map
          ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).hom.app 𝓖))
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    (representedAssociatedModulePullbackIso B S hS (𝟙 T) h 𝓕).hom =
      (eqToIso (congrArg (modulePullback B S hS) (representedSpaceMap_id B S hS T)) ≪≫
            modulePullbackIdIso B S hS
              (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :
                AlgebraicSpaces B S hS)).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj (
            (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕)) ≫
        (representedSmallEtaleModuleEquivalence B S hS T).functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
            ((Scheme.Modules.pullbackId
              ((BigFppfOver.toScheme B S hS).obj T)).inv.app 𝓕)) :=
  Stacks.CategoryTheory.eq_app_comp_of_map_comp_eq
    (modulePullback B S hS (representedSpaceMap B S hS (𝟙 T)))
    (eqToIso (congrArg (modulePullback B S hS) (representedSpaceMap_id B S hS T)) ≪≫
      modulePullbackIdIso B S hS
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS))
    (representedAssociatedModulePullbackIso B S hS (𝟙 T) h 𝓕)
    ((representedSmallEtaleModuleEquivalence B S hS T).functor.map
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).hom.app 𝓕)))
    ((representedSmallEtaleModuleEquivalence B S hS T).functor.map
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).inv.app 𝓕)))
    (Stacks.CategoryTheory.map_map_comp_eq_id
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (representedSmallEtaleModuleEquivalence B S hS T).functor _ _
      ((Scheme.Modules.pullbackId
        ((BigFppfOver.toScheme B S hS).obj T)).hom_inv_id_app 𝓕))
    ((map_representedAssociatedModulePullbackIso_id B S hS T h hn 𝓕).trans
      (hm ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj (
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕))))

/-- **The unit law `hm` of [Stacks Project, Tag 03LU] at the represented identity.**  The
composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of the inverse image at
the pair `(representedSpaceMap (𝟙 T), representedSpaceMap (𝟙 T))`, read at a module, is the
transport along `AlgebraicGeometry.Space.representedSpaceMap_id` followed by the unit law
`AlgebraicGeometry.Space.modulePullbackIdIso`.

It is `AlgebraicGeometry.Space.modulePullbackCompIso_of_eq_id` — the law at a morphism given
with an equality to the identity, stated between isomorphisms of functors — instantiated at
`AlgebraicGeometry.Space.representedSpaceMap_id` and read at the module.  The transport of the
target is supplied as `rfl`, because `representedSpaceMap (𝟙 T)` composed with itself is
definitionally itself: `AlgebraicGeometry.Space.representedSpaceMap_comp` holds by `rfl` and
composition in `AlgebraicGeometry.BigFppfOver` is unital by definitional unfolding.  That is
also why the leading `CategoryTheory.Category.comp_id` closes against the reflexive `eqToIso`
of the instantiated statement. -/
theorem modulePullbackCompIso_hom_app_representedSpaceMap_id
    (Z : Modules.{u, u} B S hS
      (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS).1
      (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS).2) :
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS (𝟙 T))
          (representedSpaceMap B S hS (𝟙 T))).hom.app Z =
      (eqToIso (congrArg (modulePullback B S hS) (representedSpaceMap_id B S hS T)) ≪≫
          modulePullbackIdIso B S hS
            (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS)).hom.app
        ((modulePullback B S hS (representedSpaceMap B S hS (𝟙 T))).obj Z) :=
  ((Category.comp_id _).symm.trans
      (Stacks.CategoryTheory.trans_hom_app
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS (𝟙 T))
          (representedSpaceMap B S hS (𝟙 T))) (eqToIso rfl) Z).symm).trans
    ((congr_app (congrArg Iso.hom
          (modulePullbackCompIso_of_eq_id B S hS (representedSpaceMap_id B S hS T) rfl)) Z).trans
      (Stacks.CategoryTheory.isoWhiskerLeft_trans_rightUnitor_hom_app
        (modulePullback B S hS (representedSpaceMap B S hS (𝟙 T))) _ Z))

/-- **The identity-vertical bridge: the transport of the inverse image at the identity of the
site, with nothing assumed.**

`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_id_of_unitLaws` with its two
hypotheses discharged — `hm` by
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_representedSpaceMap_id` and `hn` by
`AlgebraicGeometry.Scheme.Modules.pullbackComp_id_id_hom_app`.

`hn` is supplied by the Zariski unit law *at a literal identity*: the morphism of schemes the
represented identity induces, `B.inclusion.map (Over.Hom.left (𝟙 T))`, is the identity of
`(BigFppfOver.toScheme B S hS).obj T` by definitional unfolding — unlike its spaces-side
counterpart `representedSpaceMap (𝟙 T)`, whose identification with the identity is
`AlgebraicGeometry.Space.representedSpaceMap_id` and not `rfl`.  So no transport is needed on
the Zariski side and the hypothesis is the unit law itself. -/
theorem representedAssociatedModulePullbackIso_id
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    (representedAssociatedModulePullbackIso B S hS (𝟙 T) h 𝓕).hom =
      (eqToIso (congrArg (modulePullback B S hS) (representedSpaceMap_id B S hS T)) ≪≫
            modulePullbackIdIso B S hS
              (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :
                AlgebraicSpaces B S hS)).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj (
            (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕)) ≫
        (representedSmallEtaleModuleEquivalence B S hS T).functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
            ((Scheme.Modules.pullbackId
              ((BigFppfOver.toScheme B S hS).obj T)).inv.app 𝓕)) :=
  representedAssociatedModulePullbackIso_id_of_unitLaws B S hS T h
    (modulePullbackCompIso_hom_app_representedSpaceMap_id B S hS T)
    (fun 𝓖 ↦ Scheme.Modules.pullbackComp_id_id_hom_app
      ((BigFppfOver.toScheme B S hS).obj T) 𝓖) 𝓕

end AlgebraicGeometry.Space

end
