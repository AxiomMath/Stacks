module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Generator.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidInvariantSubmodule
public import StacksFrontier.AlgebraicGeometry.Properties.CardinalGeneratedSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivalenceRelationGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange

/-!
# Quasi-coherent modules on an algebraic space form a Grothendieck abelian category

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  This file
proves Stacks 077V: `QCoh(𝒪_F)` is a Grothendieck abelian category, hence has enough injectives
and all limits, and the inclusion `QCoh(𝒪_F) ⥤ Mod(𝒪_F)` has a right adjoint `Q`, the
*coherator*, whose adjunction morphism `Q(𝓕) ⟶ 𝓕` is an isomorphism for quasi-coherent `𝓕`.
Everything is at the universe `u` of the schemes, where the source puts the `𝒪_F`-modules.

The colimit clauses of Stacks 03M1 are in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentCoherator.lean`; what is added here is the
generator, constructed as in the source from a presentation and Stacks 03M3 and 077U.

## The generator

Choose a presentation `F = U/R` (Stacks 0263,
`AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace`) and let `(U, R, s, t, c)` be its
groupoid in algebraic spaces, `AlgebraicGeometry.Space.presentationGroupoid`, whose source and
target are the two represented projections of `R = U ×_F U`.  By Stacks 03M3
(`AlgebraicGeometry.Space.isEquivalence_quasicoherentFromSpaceBase`) `QCoh(𝒪_F)` is equivalent
to the quasi-coherent modules `(ℱ, α)` on this groupoid, so it suffices to find a separating set
there.

Let `κ` bound the affine opens of `U` and of `R`, `AlgebraicGeometry.Space.presentationCardinal`.
A quasi-coherent module `ℱ` on `U` is the associated module of a quasi-coherent Zariski module
`𝓕` on the scheme `U` (Descent, Proposition 03DX (2)), and since the inverse images along the
represented morphisms `s`, `t` are the associated modules of the Zariski pullbacks, `α` reads as
a morphism `t^*𝓕 ⟶ s^*𝓕` of Zariski modules,
`AlgebraicGeometry.Space.schemeTransition`.  The closure step of the proof of Stacks 077U —
`Stacks.AlgebraicGeometry.GroupoidCardinalGeneration.exists_transitionInvariant_mono_of_section`,
which uses only `α` and not its cocycle condition — puts every local section of `𝓕` in a
`κ`-generated quasi-coherent submodule `𝒵 ⊆ 𝓕` to which `α` restricts.  Back on the étale side,
`AlgebraicGeometry.Space.restrictedQuasicoherentModule` makes `(𝒵^a, α|)` a quasi-coherent module
on the groupoid: its cocycle and unit conditions are those of `α`, read through the
monomorphisms `(c ≫ s)^*𝒵^a ⟶ (c ≫ s)^*ℱ` and `(e ≫ s)^*𝒵^a ⟶ (e ≫ s)^*ℱ`, which are
monomorphisms because `s` is flat.  This is
`AlgebraicGeometry.Space.exists_restricted_of_section`.

The modules `(𝒵^a, β)` with `𝒵` `κ`-generated have only a set of isomorphism classes: the
`κ`-generated Zariski modules do, by Stacks 077M, and over a fixed underlying module the
transition morphisms form a set.  A set of representatives therefore separates,
`AlgebraicGeometry.Space.exists_isSeparating_quasicoherentSheaves`, and its coproduct is a
separator, `AlgebraicGeometry.Space.hasSeparator_quasicoherentSheaves`.

## Main results

* `AlgebraicGeometry.Space.hasSeparator_quasicoherentSheaves`: `QCoh(𝒪_F)` has a separator.
* `AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_enoughInjectives_hasLimits`:
  **Stacks 077V, part (1).**
* `AlgebraicGeometry.Space.exists_coherator`: **Stacks 077V, part (2).**
* `AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian`,
  `AlgebraicGeometry.Space.quasicoherentSheaves_enoughInjectives`,
  `AlgebraicGeometry.Space.quasicoherentSheaves_hasLimitsOfSize`,
  `AlgebraicGeometry.Space.isLeftAdjoint_ι_quasicoherentSheaves` and
  `AlgebraicGeometry.Space.isIso_quasicoherentCoheratorCounit_app`: the individual assertions.

## Implementation notes

The source and the target of `AlgebraicGeometry.Space.presentationGroupoid` are *literally* the
represented morphisms `AlgebraicGeometry.Space.representedSpaceMap` of the two projections, and
its object and arrow spaces are literally the represented algebraic spaces: the groupoid is
written out as a structure, with only its composition and the groupoid axioms taken from the
groupoid of Stacks 043Y.  This is what lets the comparisons of inverse images with Zariski
pullbacks, `AlgebraicGeometry.Space.representedAssociatedModulePullbackNatIso`, be applied to the
transition morphism of a quasi-coherent module on the groupoid without any transport.

The commutation of the transported transition morphism with the inclusion is the purely
categorical `AlgebraicGeometry.Space.comparisonTransportBack_comm`.

## References

* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 077U](https://stacks.math.columbia.edu/tag/077U)
* [Stacks Project, Tag 077M](https://stacks.math.columbia.edu/tag/077M)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Represented

/-- The associated module functor from Zariski modules on the scheme underlying `T` to the
`𝒪`-modules on the small étale site of the representable algebraic space `yoneda.obj T`. -/
noncomputable def representedAssociatedModuleFunctor (T : BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj T).Modules ⥤
      Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).obj
        (representedAlgebraicSpace B S hS T).property :=
  _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
    (representedSmallEtaleModuleEquivalence B S hS T).functor

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- **The inverse image along a morphism of representable algebraic spaces of an associated
module is the associated module of the Zariski pullback, naturally in the module.** -/
noncomputable def representedAssociatedModulePullbackNatIso :
    representedAssociatedModuleFunctor B S hS T ⋙
        modulePullback B S hS (representedSpaceMap B S hS g) ≅
      Scheme.Modules.pullback (B.inclusion.map g.left) ⋙
        representedAssociatedModuleFunctor B S hS T' :=
  let e := representedSmallEtaleModuleEquivalence B S hS T
  let e' := representedSmallEtaleModuleEquivalence B S hS T'
  let ρ' := Iso.isoCompInverse (H := e'.symm) (representedModulePullbackIso B S hS g hg)
  let E1 : e.functor ⋙ modulePullback B S hS (representedSpaceMap B S hS g) ≅
      SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g) ⋙ e'.functor :=
    Functor.isoWhiskerLeft e.functor ρ' ≪≫ (Functor.associator _ _ e'.functor).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.unitIso.symm _ ≪≫ Functor.leftUnitor _) e'.functor
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ E1 ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
        (associatedBigEtaleSite B) g.left).symm e'.functor ≪≫ Functor.associator _ _ _

end Represented

section Restriction

variable {B S hS} {A : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}
  (Y : QuasicoherentModule B S hS G)
  (E : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
  (ι : E.obj ⟶ Y.F.obj)
  (β : (modulePullback B S hS G.target).obj E.obj ⟶ (modulePullback B S hS G.source).obj E.obj)
  (hβ : β ≫ (modulePullback B S hS G.source).map ι =
    (modulePullback B S hS G.target).map ι ≫ Y.alpha)
  (hc : Mono ((modulePullback B S hS (G.comp ≫ G.source)).map ι))
  (he : Mono ((modulePullback B S hS (GroupoidInAlgebraicSpaces.identityArrow G ≫
    G.source)).map ι))

/-- **The restriction of a quasi-coherent module on a groupoid in algebraic spaces to a
submodule its transition morphism preserves.**  Let `(ℱ, α)` be a quasi-coherent module on
`(U, R, s, t, c)`, let `ι : 𝒢 ⟶ ℱ` be a morphism from a quasi-coherent `𝒪_U`-module and let
`β : t^*𝒢 ⟶ s^*𝒢` be compatible with `α` through `ι`.  If the inverse images of `ι` along `c ≫ s`
and along `e ≫ s` are monomorphisms, then `(𝒢, β)` satisfies the cocycle and unit conditions, so
it is a quasi-coherent module on the groupoid. -/
def restrictedQuasicoherentModule : QuasicoherentModule B S hS G where
  F := E
  alpha := β
  cocycle := by
    refine (cancel_mono ((modulePullback B S hS (G.comp ≫ G.source)).map ι)).1 ?_
    rw [← groupoidPullbackTransition_naturality B S hS G (M := E.obj) (N := Y.F.obj) ι hβ G.comp,
      Y.cocycle,
      groupoidTransitionComposite_naturality B S hS G (M := E.obj) (N := Y.F.obj) ι hβ]
  unit := by
    refine (cancel_mono ((modulePullback B S hS
      (GroupoidInAlgebraicSpaces.identityArrow G ≫ G.source)).map ι)).1 ?_
    rw [← groupoidPullbackTransition_naturality B S hS G (M := E.obj) (N := Y.F.obj) ι hβ
        (GroupoidInAlgebraicSpaces.identityArrow G),
      Y.unit,
      ← comp₂_eq (C := Modules.{u, u} B S hS G.objects.1 G.objects.2),
      ← comp₂_eq (C := Modules.{u, u} B S hS G.objects.1 G.objects.2)]
    exact (pullbackTransport_naturality₂ (M := E.obj) (N := Y.F.obj) ι
      ((GroupoidInAlgebraicSpaces.identityArrow_comp_target G).trans
        (GroupoidInAlgebraicSpaces.identityArrow_comp_source G).symm)).symm

/-- The inclusion of the restriction of a quasi-coherent module on a groupoid in algebraic
spaces into the module, as a morphism of quasi-coherent modules on the groupoid. -/
def restrictedQuasicoherentModuleHom : restrictedQuasicoherentModule Y E ι β hβ hc he ⟶ Y :=
  ⟨ι, hβ⟩

end Restriction

section PresentationGroupoid

open Stacks.Groupoids.GroupoidScheme

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (P : Presentation B S hS F hF)

/-- The terminal algebraic space of the site over `S` is terminal among presheaves. -/
noncomputable def isTerminal_realizationBase_obj : IsTerminal (realizationBase B hS).obj :=
  Over.mkIdTerminal.isTerminalObj yoneda _

/-- The structure morphism of a representable algebraic space to the terminal algebraic space. -/
noncomputable abbrev toRealizationBase (X : AlgebraicSpaces B S hS) : X ⟶ realizationBase B hS :=
  ObjectProperty.homMk ((isTerminal_realizationBase_obj (hS := hS)).from X.obj)

/-- The pre-relation of a presentation `X = U/R`, over the terminal algebraic space: the target
and the source projections of `R`. -/
noncomputable def presentationSpaceRelation :
    PreRelation (Over.mk (toRealizationBase (representedAlgebraicSpace B S hS P.R)).hom)
      (Over.mk (toRealizationBase (representedAlgebraicSpace B S hS P.U)).hom) :=
  prod.lift (Over.homMk (yoneda.map P.target) (isTerminal_realizationBase_obj.hom_ext _ _))
    (Over.homMk (yoneda.map P.source) (isTerminal_realizationBase_obj.hom_ext _ _))

/-- The target of the pre-relation of a presentation is its target projection. -/
theorem presentationSpaceRelation_target :
    (presentationSpaceRelation P).target =
      Over.homMk (yoneda.map P.target) (isTerminal_realizationBase_obj.hom_ext _ _) :=
  prod.lift_fst _ _

/-- The source of the pre-relation of a presentation is its source projection. -/
theorem presentationSpaceRelation_source :
    (presentationSpaceRelation P).source =
      Over.homMk (yoneda.map P.source) (isTerminal_realizationBase_obj.hom_ext _ _) :=
  prod.lift_snd _ _

set_option synthInstance.maxHeartbeats 400000 in
-- synthesizing `HasPullbacks` for presheaves on the big fppf site needs a deep instance search
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_quasicoherentSeparator :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_quasicoherentSeparator
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

local instance hasPullbacks_over_presheaf_quasicoherentSeparator
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : HasPullbacks (Over X) := inferInstance

local instance (priority := high) hasPullback_over_presheaf_quasicoherentSeparator
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y Z W : Over X} (f : Y ⟶ W) (g : Z ⟶ W) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The pre-relation of a presentation is an equivalence relation: its two projections are the
kernel pair of the atlas `U ⟶ X`. -/
instance isEquivalenceRelation_presentationSpaceRelation :
    IsEquivalenceRelation (presentationSpaceRelation P).target
      (presentationSpaceRelation P).source := by
  have hT := isTerminal_realizationBase_obj (hS := hS)
  have : (Over.forget (realizationBase B hS).obj).IsEquivalence :=
    (Over.equivalenceOfIsTerminal hT).isEquivalence_functor
  let f : Over.mk (toRealizationBase (representedAlgebraicSpace B S hS P.U)).hom ⟶
      Over.mk (hT.from F) := Over.homMk P.toSpace (hT.hom_ext _ _)
  let a : Over.mk (toRealizationBase (representedAlgebraicSpace B S hS P.R)).hom ⟶
      Over.mk (toRealizationBase (representedAlgebraicSpace B S hS P.U)).hom :=
    Over.homMk (yoneda.map P.target) (hT.hom_ext _ _)
  let b : Over.mk (toRealizationBase (representedAlgebraicSpace B S hS P.R)).hom ⟶
      Over.mk (toRealizationBase (representedAlgebraicSpace B S hS P.U)).hom :=
    Over.homMk (yoneda.map P.source) (hT.hom_ext _ _)
  have hk : IsKernelPair f a b :=
    IsPullback.of_map_of_faithful (Over.forget _) (by exact P.isPullback)
  rw [presentationSpaceRelation_target, presentationSpaceRelation_source]
  exact (IsKernelPair.equivalenceRelation _ _ _ (pullback.isLimit _ _) hk).isEquivalenceRelation

/-- The groupoid in algebraic spaces extending the pre-relation of a presentation, by
Stacks 043Y. -/
noncomputable def presentationSpaceRelationGroupoid :
    GroupoidInAlgebraicSpaces B S hS (realizationBase B hS) :=
  groupoidOfIsEquivalenceRelation (presentationSpaceRelation P)

/-- The target of the groupoid of Stacks 043Y extending the pre-relation of a presentation is the
represented target projection. -/
theorem presentationSpaceRelationGroupoid_target :
    (presentationSpaceRelationGroupoid P).target = representedSpaceMap B S hS P.target :=
  ObjectProperty.hom_ext _ (congrArg (fun k => k.left) (presentationSpaceRelation_target P))

/-- The source of the groupoid of Stacks 043Y extending the pre-relation of a presentation is the
represented source projection. -/
theorem presentationSpaceRelationGroupoid_source :
    (presentationSpaceRelationGroupoid P).source = representedSpaceMap B S hS P.source :=
  ObjectProperty.hom_ext _ (congrArg (fun k => k.left) (presentationSpaceRelation_source P))

/-- The composition of `AlgebraicGeometry.Space.presentationSpaceRelationGroupoid`, read on the
fibre product of two morphisms equal to its source and target. -/
noncomputable def presentationSpaceComp
    (s t : representedAlgebraicSpace B S hS P.R ⟶ representedAlgebraicSpace B S hS P.U)
    (hs : s = (presentationSpaceRelationGroupoid P).source)
    (ht : t = (presentationSpaceRelationGroupoid P).target) :
    AlgebraicSpaces.fiberProduct B S hS s t ⟶ representedAlgebraicSpace B S hS P.R := by
  subst hs
  subst ht
  exact (presentationSpaceRelationGroupoid P).comp

/-- The transported composition of `AlgebraicGeometry.Space.presentationSpaceComp` still makes
every set of points a groupoid. -/
theorem presentationSpaceComp_pointwiseGroupoid
    (s t : representedAlgebraicSpace B S hS P.R ⟶ representedAlgebraicSpace B S hS P.U)
    (hs : s = (presentationSpaceRelationGroupoid P).source)
    (ht : t = (presentationSpaceRelationGroupoid P).target) (T : (BigFppfOver B S hS)ᵒᵖ) :
    Nonempty (Deformation.PointwiseGroupoid (s.hom.app T) (t.hom.app T)
      (fun p => (composableToPullback s.hom t.hom ≫ (presentationSpaceComp P s t hs ht).hom).app T
        p)) := by
  subst hs
  subst ht
  exact (presentationSpaceRelationGroupoid P).pointwiseGroupoid T

/-- **The groupoid in algebraic spaces of a presentation `X = U/R`**: its object space is `U`, its
arrow space is `R`, its target and source are the two projections of `R = U ×_X U`, and its
composition is the one forced by Stacks 043Y.  The source and the target are the represented
morphisms themselves, so that inverse images along them are inverse images along represented
morphisms. -/
noncomputable abbrev presentationGroupoid :
    GroupoidInAlgebraicSpaces B S hS (realizationBase B hS) where
  objects := representedAlgebraicSpace B S hS P.U
  arrows := representedAlgebraicSpace B S hS P.R
  objectsToBase := toRealizationBase _
  arrowsToBase := toRealizationBase _
  source := representedSpaceMap B S hS P.source
  target := representedSpaceMap B S hS P.target
  source_over := ObjectProperty.hom_ext _ (isTerminal_realizationBase_obj.hom_ext _ _)
  target_over := ObjectProperty.hom_ext _ (isTerminal_realizationBase_obj.hom_ext _ _)
  comp := presentationSpaceComp P _ _ (presentationSpaceRelationGroupoid_source P).symm
    (presentationSpaceRelationGroupoid_target P).symm
  comp_over := ObjectProperty.hom_ext _ (isTerminal_realizationBase_obj.hom_ext _ _)
  pointwiseGroupoid := presentationSpaceComp_pointwiseGroupoid P _ _
    (presentationSpaceRelationGroupoid_source P).symm
    (presentationSpaceRelationGroupoid_target P).symm

/-- The atlas of a presentation, as a morphism from the object space of its groupoid. -/
noncomputable abbrev presentationAtlas :
    (presentationGroupoid P).objects ⟶ (⟨F, hF⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk P.toSpace

/-- The atlas of a presentation is étale. -/
theorem presentationAtlas_isEtale : IsEtale B S hS (presentationAtlas P).hom :=
  (isEtale_iff_presheaf_of_yoneda B S hS P.toSpace).2 P.etale

/-- The two projections of the relation of a presentation have the same composite with the
atlas. -/
theorem presentationAtlas_comm :
    (presentationGroupoid P).target ≫ presentationAtlas P =
      (presentationGroupoid P).source ≫ presentationAtlas P :=
  ObjectProperty.hom_ext _ P.isPullback.w

/-- The arrow space of the groupoid of a presentation is the fibre product `U ×_X U`, with the
target and the source as the two projections. -/
theorem presentationGroupoid_isPullback :
    IsPullback (presentationGroupoid P).target.hom (presentationGroupoid P).source.hom
      (presentationAtlas P).hom (presentationAtlas P).hom :=
  P.isPullback

/-- The atlas of a presentation, as a one-member family, is an étale covering in the sense of
Stacks 041E. -/
theorem presentationAtlas_isEtaleCovering :
    IsEtaleCovering B S hS (fun _ : Unit => (presentationGroupoid P).objects.1)
      (fun _ => (presentationAtlas P).hom) := by
  refine ⟨hF, fun _ => isAlgebraicSpace_yoneda B S hS P.U, fun _ => presentationAtlas_isEtale P,
    ?_⟩
  rw [Set.iUnion_const, Set.range_eq_univ]
  exact surjective_pointsMap_of_presheaf_surjective B S hS P.toSpace P.surjective

/-- The atlas of a presentation is relatively representable, its source being representable. -/
theorem presentationAtlas_relativelyRepresentable :
    yoneda.relativelyRepresentable (presentationAtlas P).hom :=
  relativelyRepresentable_of_representableSource B S hS (presentationAtlas P) P.U (Iso.refl _)

/-- The source of the groupoid of a presentation is étale, as a base change of the atlas. -/
theorem presentationGroupoid_source_isEtale :
    IsEtale B S hS (presentationGroupoid P).source.hom :=
  isEtale_of_isPullback_yoneda B S hS P.isPullback (presentationAtlas_isEtale P)

/-- The target of the groupoid of a presentation is étale, as a base change of the atlas. -/
theorem presentationGroupoid_target_isEtale :
    IsEtale B S hS (presentationGroupoid P).target.hom :=
  isEtale_of_isPullback_yoneda B S hS P.isPullback.flip (presentationAtlas_isEtale P)

end PresentationGroupoid

section Transport

variable {B S hS} {A : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}

/-- The transition morphism of a quasi-coherent module on a groupoid in algebraic spaces,
transported along an isomorphism of its underlying module with a fixed module. -/
noncomputable def transportedTransition (Y : QuasicoherentModule B S hS G)
    {W : Modules.{u, u} B S hS G.objects.obj G.objects.property} (e : Y.F.obj ≅ W) :
    (modulePullback B S hS G.target).obj W ⟶ (modulePullback B S hS G.source).obj W :=
  (modulePullback B S hS G.target).map e.inv ≫ Y.alpha ≫ (modulePullback B S hS G.source).map e.hom

/-- A morphism of the underlying modules which identifies the transported transition morphisms
is compatible with the transition morphisms. -/
theorem comm_of_transportedTransition_eq {Y Y' : QuasicoherentModule B S hS G}
    {W : Modules.{u, u} B S hS G.objects.obj G.objects.property}
    (e : Y.F.obj ≅ W) (e' : Y'.F.obj ≅ W)
    (h : transportedTransition Y e = transportedTransition Y' e') :
    Y.alpha ≫ (modulePullback B S hS G.source).map (e.hom ≫ e'.inv) =
      (modulePullback B S hS G.target).map (e.hom ≫ e'.inv) ≫ Y'.alpha := by
  have hh := congrArg (fun z => (modulePullback B S hS G.target).map e.hom ≫ z ≫
    (modulePullback B S hS G.source).map e'.inv) h
  dsimp only [transportedTransition] at hh
  simp only [Category.assoc] at hh
  rw [Iso.hom_inv_id_map_assoc, Iso.hom_inv_id_map, Category.comp_id] at hh
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, hh]

/-- Two quasi-coherent modules on a groupoid in algebraic spaces whose underlying modules are
identified with a common one, compatibly with the transported transition morphisms, are
isomorphic. -/
noncomputable def isoOfTransportedTransitionEq {Y Y' : QuasicoherentModule B S hS G}
    {W : Modules.{u, u} B S hS G.objects.obj G.objects.property}
    (e : Y.F.obj ≅ W) (e' : Y'.F.obj ≅ W)
    (h : transportedTransition Y e = transportedTransition Y' e') : Y ≅ Y' where
  hom := ⟨e.hom ≫ e'.inv, comm_of_transportedTransition_eq e e' h⟩
  inv := ⟨e'.hom ≫ e.inv, comm_of_transportedTransition_eq e' e h.symm⟩
  hom_inv_id := QuasicoherentModule.Hom.ext (by
    change (e.hom ≫ e'.inv) ≫ e'.hom ≫ e.inv = 𝟙 Y.F.obj
    rw [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id])
  inv_hom_id := QuasicoherentModule.Hom.ext (by
    change (e'.hom ≫ e.inv) ≫ e.hom ≫ e'.inv = 𝟙 Y'.F.obj
    rw [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id])

end Transport

section Separator

open Stacks.Groupoids.GroupoidScheme Stacks.AlgebraicGeometry

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (P : Presentation B S hS F hF)

/-- The cardinal bounding the affine opens of the presenting scheme and of the relation scheme of a
presentation. -/
noncomputable abbrev presentationCardinal : Cardinal.{u} :=
  max Cardinal.aleph0 (max (Cardinal.mk ((BigFppfOver.toScheme B S hS).obj P.U).affineOpens)
    (Cardinal.mk ((BigFppfOver.toScheme B S hS).obj P.R).affineOpens))

/-- The source projection of the relation of a presentation is flat, being étale. -/
instance flat_presentation_source :
    Flat (B.inclusion.map P.source.left) := by
  have h : Etale (PreRelation.source
      (prod.lift ((Over.post B.inclusion).map P.target)
        ((Over.post B.inclusion).map P.source))).left :=
    P.isEtaleEquivalenceRelation.etale_source
  change Etale (prod.lift ((Over.post B.inclusion).map P.target)
    ((Over.post B.inclusion).map P.source) ≫ prod.snd).left at h
  rw [prod.lift_snd] at h
  exact inferInstanceAs (Flat ((Over.post B.inclusion).map P.source).left)

end Separator

section Flatness

variable {B S hS} {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)

/-- An inverse image of `𝒪`-modules along a flat morphism of algebraic spaces carries
monomorphisms to monomorphisms. -/
theorem mono_modulePullback_map_of_isFlat {X' X : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (hf : IsFlat B S hS f.hom) {M N : Modules.{u, u} B S hS X.obj X.property} (ι : M ⟶ N)
    (hι : Mono ι) : Mono ((modulePullback B S hS f).map ι) := by
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS f hf
  exact Functor.map_mono _ _

/-- If the source of a groupoid in algebraic spaces is flat, so is the composite of the
composition with the source. -/
theorem isFlat_comp_comp_source (hs : IsFlat B S hS G.source.hom) :
    IsFlat B S hS (G.comp ≫ G.source).hom :=
  isFlat_comp B S hS (AlgebraicSpaces.fiberProduct B S hS G.source G.target).2 G.arrows.2
    G.objects.2 G.comp.hom G.source.hom
    ((isFlat_isStableUnderBaseChange B S hS).of_isPullback (Space.isPullback_comp_source G).flip
      hs) hs

/-- The composite of the unit with the source of a groupoid in algebraic spaces is flat, being
the identity. -/
theorem isFlat_identityArrow_comp_source :
    IsFlat B S hS (GroupoidInAlgebraicSpaces.identityArrow G ≫ G.source).hom := by
  rw [GroupoidInAlgebraicSpaces.identityArrow_comp_source]
  exact isFlat_id B S hS G.objects.2

end Flatness

section Abstract

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  {LU : C ⥤ D} {LR : C' ⥤ D'} {pT pS : C ⥤ C'} {mT mS : D ⥤ D'}
  (ct : LU ⋙ mT ≅ pT ⋙ LR) (cs : LU ⋙ mS ≅ pS ⋙ LR)

/-- A morphism `mT M ⟶ mS M`, read through an isomorphism `LU F ≅ M` and two comparison
isomorphisms `LU ⋙ mT ≅ pT ⋙ LR` and `LU ⋙ mS ≅ pS ⋙ LR` as a morphism `LR (pT F) ⟶ LR (pS F)`. -/
def comparisonTransport {FZ : C} {M : D} (εM : LU.obj FZ ≅ M) (α : mT.obj M ⟶ mS.obj M) :
    LR.obj (pT.obj FZ) ⟶ LR.obj (pS.obj FZ) :=
  ct.inv.app FZ ≫ mT.map εM.hom ≫ α ≫ mS.map εM.inv ≫ cs.hom.app FZ

/-- A morphism `pT Z ⟶ pS Z`, read through two comparison isomorphisms as a morphism
`mT (LU Z) ⟶ mS (LU Z)`. -/
def comparisonTransportBack {Z : C} (β : pT.obj Z ⟶ pS.obj Z) :
    mT.obj (LU.obj Z) ⟶ mS.obj (LU.obj Z) :=
  ct.hom.app Z ≫ LR.map β ≫ cs.inv.app Z

/-- **Transporting a compatible transition morphism along two comparison isomorphisms.**  If
`LR αZ` is `α` read through `εM : LU F ≅ M` and the comparisons, then a morphism
`β : pT Z ⟶ pS Z` compatible with `αZ` along `ι : Z ⟶ F` reads back to a morphism compatible with
`α` along `LU ι ≫ εM`. -/
theorem comparisonTransportBack_comm {Z FZ : C} {M : D} (εM : LU.obj FZ ≅ M)
    (α : mT.obj M ⟶ mS.obj M) (αZ : pT.obj FZ ⟶ pS.obj FZ)
    (hαZ : LR.map αZ = comparisonTransport ct cs εM α)
    (ι : Z ⟶ FZ) (β : pT.obj Z ⟶ pS.obj Z) (hβ : β ≫ pS.map ι = pT.map ι ≫ αZ) :
    comparisonTransportBack ct cs β ≫ mS.map (LU.map ι ≫ εM.hom) =
      mT.map (LU.map ι ≫ εM.hom) ≫ α := by
  have nt : mT.map (LU.map ι) ≫ ct.hom.app FZ = ct.hom.app Z ≫ LR.map (pT.map ι) :=
    ct.hom.naturality ι
  have ns : LR.map (pS.map ι) ≫ cs.inv.app FZ = cs.inv.app Z ≫ mS.map (LU.map ι) :=
    cs.inv.naturality ι
  simp only [comparisonTransportBack, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% ns, ← Functor.map_comp_assoc LR, hβ, Functor.map_comp, Category.assoc, hαZ]
  simp only [comparisonTransport, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% nt, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_map, Category.comp_id]

/-- Two morphisms of `𝒪_X`-modules on a scheme agreeing on every section are equal. -/
theorem scheme_modules_hom_ext_of_app_apply {X : Scheme.{u}} {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ (O : X.Opens) (x : Γ(M, O)), f.app O x = g.app O x) : f = g :=
  Scheme.Modules.hom_ext f g fun O => by
    ext x
    exact h O x

/-- Two morphisms out of `X` agree after `e.inverse` and a morphism `ι` into `e.inverse X` as soon
as they agree after `e.functor ι` followed by the counit. -/
theorem comp_inverse_map_eq_of_counit (e : C ≌ D) {Z : C} {X X' : D} (ι : Z ⟶ e.inverse.obj X)
    (g₁ g₂ : X ⟶ X')
    (h : e.functor.map ι ≫ e.counit.app X ≫ g₁ = e.functor.map ι ≫ e.counit.app X ≫ g₂) :
    ι ≫ e.inverse.map g₁ = ι ≫ e.inverse.map g₂ := by
  apply e.functor.map_injective
  rw [Functor.map_comp, Functor.map_comp, Equivalence.fun_inv_map, Equivalence.fun_inv_map]
  simpa only [Category.assoc] using congrArg (· ≫ e.counitInv.app X') h

end Abstract

section SchemeTransition

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (P : Presentation B S hS F hF)

/-- The associated module functor from Zariski modules on the presenting scheme to the
`𝒪`-modules on the object space of the groupoid of a presentation. -/
noncomputable def presentationObjectsFunctor :
    ((BigFppfOver.toScheme B S hS).obj P.U).Modules ⥤
      Modules.{u, u} B S hS (presentationGroupoid P).objects.obj
        (presentationGroupoid P).objects.property :=
  representedAssociatedModuleFunctor B S hS P.U

/-- The associated module functor from Zariski modules on the relation scheme to the
`𝒪`-modules on the arrow space of the groupoid of a presentation. -/
noncomputable def presentationArrowsFunctor :
    ((BigFppfOver.toScheme B S hS).obj P.R).Modules ⥤
      Modules.{u, u} B S hS (presentationGroupoid P).arrows.obj
        (presentationGroupoid P).arrows.property :=
  representedAssociatedModuleFunctor B S hS P.R

/-- The inverse image along the target of the groupoid of a presentation, compared with the
Zariski pullback along the target of the relation. -/
noncomputable def presentationTargetIso :
    presentationObjectsFunctor P ⋙ modulePullback B S hS (presentationGroupoid P).target ≅
      Scheme.Modules.pullback (B.inclusion.map P.target.left) ⋙ presentationArrowsFunctor P :=
  representedAssociatedModulePullbackNatIso B S hS P.target
    (relativelyRepresentable_yoneda_map B S hS P.target)

/-- The inverse image along the source of the groupoid of a presentation, compared with the
Zariski pullback along the source of the relation. -/
noncomputable def presentationSourceIso :
    presentationObjectsFunctor P ⋙ modulePullback B S hS (presentationGroupoid P).source ≅
      Scheme.Modules.pullback (B.inclusion.map P.source.left) ⋙ presentationArrowsFunctor P :=
  representedAssociatedModulePullbackNatIso B S hS P.source
    (relativelyRepresentable_yoneda_map B S hS P.source)

variable (M : QuasicoherentSheaves.{u, u} B S hS (presentationGroupoid P).objects.obj
    (presentationGroupoid P).objects.property)
  (α : (modulePullback B S hS (presentationGroupoid P).target).obj M.obj ⟶
    (modulePullback B S hS (presentationGroupoid P).source).obj M.obj)

/-- A morphism of quasi-coherent modules on the object space of the groupoid of a presentation,
read in the category of quasi-coherent modules on the small étale site of the presenting scheme. -/
noncomputable abbrev presentationQcohHom {N N' : QuasicoherentSheaves.{u, u} B S hS
      (presentationGroupoid P).objects.obj (presentationGroupoid P).objects.property}
    (f : N.obj ⟶ N'.obj) :
    (N : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS P.U)).FullSubcategory) ⟶ N' :=
  ObjectProperty.homMk f

/-- The pullback of a quasi-coherent Zariski module along a morphism of the site, as a
quasi-coherent Zariski module. -/
noncomputable abbrev qcohSchemePullback {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf).FullSubcategory :=
  ⟨(Scheme.Modules.pullback (B.inclusion.map g.left)).obj N.obj,
    haveI : N.obj.IsQuasicoherent := N.property
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _⟩

/-- The Zariski module on the presenting scheme which corresponds to `M`. -/
noncomputable abbrev schemeModuleOf :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory :=
  (representedQuasicoherentSchemeEquivalence B S hS P.U).inverse.obj M

/-- The identification of the module corresponding to `M` with `M`, as an isomorphism of
`𝒪`-modules. -/
noncomputable def schemeModuleOfModulesIso :
    (presentationObjectsFunctor P).obj (schemeModuleOf P M).obj ≅ M.obj :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (representedStructureRingSheaf B S hS P.U)).ι.mapIso
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).counitIso.app M)

/-- The transition morphism `α`, read on the étale site of the relation scheme as a morphism
between the two associated modules of Zariski pullbacks. -/
noncomputable abbrev associatedSchemeTransition :
    (presentationArrowsFunctor P).obj
        ((Scheme.Modules.pullback (B.inclusion.map P.target.left)).obj (schemeModuleOf P M).obj) ⟶
      (presentationArrowsFunctor P).obj
        ((Scheme.Modules.pullback (B.inclusion.map P.source.left)).obj
          (schemeModuleOf P M).obj) :=
  comparisonTransport (presentationTargetIso P) (presentationSourceIso P)
    (schemeModuleOfModulesIso P M) α

/-- **The transition morphism on the Zariski side.**  The unique morphism `t^*𝓕 ⟶ s^*𝓕` of
Zariski modules on the relation scheme whose associated module is
`AlgebraicGeometry.Space.associatedSchemeTransition`, for `𝓕` the Zariski module corresponding to
`M`; it exists because `𝓕 ↦ 𝓕^a` is fully faithful on quasi-coherent modules. -/
noncomputable def schemeTransition :
    (Scheme.Modules.pullback (B.inclusion.map P.target.left)).obj (schemeModuleOf P M).obj ⟶
      (Scheme.Modules.pullback (B.inclusion.map P.source.left)).obj (schemeModuleOf P M).obj :=
  ((representedQuasicoherentSchemeEquivalence B S hS P.R).fullyFaithfulFunctor.preimage
    (ObjectProperty.homMk (associatedSchemeTransition P M α) :
      (representedQuasicoherentSchemeEquivalence B S hS P.R).functor.obj
          (qcohSchemePullback P.target (schemeModuleOf P M)) ⟶
        (representedQuasicoherentSchemeEquivalence B S hS P.R).functor.obj
          (qcohSchemePullback P.source (schemeModuleOf P M)))).hom

/-- The associated module of `AlgebraicGeometry.Space.schemeTransition` is
`AlgebraicGeometry.Space.associatedSchemeTransition`. -/
theorem map_schemeTransition :
    (presentationArrowsFunctor P).map (schemeTransition P M α) =
      associatedSchemeTransition P M α :=
  congrArg (fun k => k.hom)
    ((representedQuasicoherentSchemeEquivalence B S hS P.R).fullyFaithfulFunctor.map_preimage
      (ObjectProperty.homMk (associatedSchemeTransition P M α) :
        (representedQuasicoherentSchemeEquivalence B S hS P.R).functor.obj
            (qcohSchemePullback P.target (schemeModuleOf P M)) ⟶
          (representedQuasicoherentSchemeEquivalence B S hS P.R).functor.obj
            (qcohSchemePullback P.source (schemeModuleOf P M))))

/-- The inclusion, into `M`, of the associated module of a Zariski module mapping to the module
corresponding to `M`. -/
noncomputable abbrev associatedInclusion {Z : ((BigFppfOver.toScheme B S hS).obj P.U).Modules}
    (ι : Z ⟶ (schemeModuleOf P M).obj) :
    (presentationObjectsFunctor P).obj Z ⟶ M.obj :=
  (presentationObjectsFunctor P).map ι ≫ (schemeModuleOfModulesIso P M).hom

/-- **A Zariski submodule invariant under the Zariski transition morphism gives an invariant
submodule on the étale side.**  If `β : t^*𝒵 ⟶ s^*𝒵` is compatible with
`AlgebraicGeometry.Space.schemeTransition` along `ι : 𝒵 ⟶ 𝓕`, then `β`, read back on the étale
site, is compatible with `α` along the associated inclusion. -/
theorem associatedTransition_comm {Z : ((BigFppfOver.toScheme B S hS).obj P.U).Modules}
    (ι : Z ⟶ (schemeModuleOf P M).obj)
    (β : (Scheme.Modules.pullback (B.inclusion.map P.target.left)).obj Z ⟶
      (Scheme.Modules.pullback (B.inclusion.map P.source.left)).obj Z)
    (hβ : β ≫ (Scheme.Modules.pullback (B.inclusion.map P.source.left)).map ι =
      (Scheme.Modules.pullback (B.inclusion.map P.target.left)).map ι ≫
        schemeTransition P M α) :
    comparisonTransportBack (presentationTargetIso P) (presentationSourceIso P) β ≫
        (modulePullback B S hS (presentationGroupoid P).source).map (associatedInclusion P M ι) =
      (modulePullback B S hS (presentationGroupoid P).target).map (associatedInclusion P M ι) ≫
        α :=
  comparisonTransportBack_comm _ _ _ α _ (map_schemeTransition P M α) ι β hβ

end SchemeTransition

section Core

open Stacks.AlgebraicGeometry

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (P : Presentation B S hS F hF)

/-- **Every section of a quasi-coherent module on the groupoid of a presentation lies in a
bounded submodule.**  Let `X = U/R` be a presentation and `(ℱ, α)` a quasi-coherent module on its
groupoid, with `𝓕` the quasi-coherent Zariski module on `U` corresponding to `ℱ`.  For every local
section `x` of `𝓕` there is a quasi-coherent module `(𝒢, β)` on the groupoid with a morphism
`j : (𝒢, β) ⟶ (ℱ, α)`, whose underlying module is the associated module of a quasi-coherent,
`κ`-generated Zariski module on `U` (`κ` bounding the affine opens of `U` and `R`), such that any
two morphisms out of `(ℱ, α)` which agree after `j` agree on `x`.

This is the closure step of the proof of Stacks 077U, run on the Zariski side through
`Stacks.AlgebraicGeometry.GroupoidCardinalGeneration.exists_transitionInvariant_mono_of_section`
and carried back to the groupoid along the comparison of Stacks 03DX (2) for the presenting
schemes. -/
theorem exists_restricted_of_section
    (Y : QuasicoherentModule B S hS (presentationGroupoid P))
    (O : ((BigFppfOver.toScheme B S hS).obj P.U).Opens)
    (x : Γ(((schemeModuleOf P Y.F).obj : ((BigFppfOver.toScheme B S hS).obj P.U).Modules), O)) :
    ∃ (Y' : QuasicoherentModule B S hS (presentationGroupoid P)) (j : Y' ⟶ Y)
      (Z : ((BigFppfOver.toScheme B S hS).obj P.U).Modules) (_ : Z.IsQuasicoherent),
      CardinalGeneration.IsCardinalGenerated Z (presentationCardinal P) ∧
      Nonempty (Y'.F.obj ≅ (presentationObjectsFunctor P).obj Z) ∧
      ∀ (Y'' : QuasicoherentModule B S hS (presentationGroupoid P)) (a b : Y ⟶ Y''),
        j ≫ a = j ≫ b →
          Scheme.Modules.Hom.app (X := (BigFppfOver.toScheme B S hS).obj P.U)
              ((representedQuasicoherentSchemeEquivalence B S hS P.U).inverse.map
                (presentationQcohHom P a.hom)).hom O x =
            Scheme.Modules.Hom.app (X := (BigFppfOver.toScheme B S hS).obj P.U)
              ((representedQuasicoherentSchemeEquivalence B S hS P.U).inverse.map
                (presentationQcohHom P b.hom)).hom O x := by
  classical
  let eU := representedQuasicoherentSchemeEquivalence B S hS P.U
  let FZ := schemeModuleOf P Y.F
  let αZ := schemeTransition P Y.F Y.alpha
  have : FZ.obj.IsQuasicoherent := FZ.property
  have hκ : Cardinal.aleph0 ≤ presentationCardinal P := le_max_left _ _
  have hU : Cardinal.mk ((BigFppfOver.toScheme B S hS).obj P.U).affineOpens ≤
      presentationCardinal P := (le_max_left _ _).trans (le_max_right _ _)
  have hR : Cardinal.mk ((BigFppfOver.toScheme B S hS).obj P.R).affineOpens ≤
      presentationCardinal P := (le_max_right _ _).trans (le_max_right _ _)
  have : Flat (B.inclusion.map P.source.left) := flat_presentation_source P
  have h0 := GroupoidCardinalGeneration.exists_transitionInvariant_mono_of_section
      (U := (BigFppfOver.toScheme B S hS).obj P.U) (R := (BigFppfOver.toScheme B S hS).obj P.R)
      (B.inclusion.map P.target.left) (B.inclusion.map P.source.left) FZ.obj αZ hκ hU hR O
      (x : Γ(FZ.obj, O))
  obtain ⟨Z, ι, β, hι, hZ, hZκ, hβ, ⟨y, hy⟩⟩ := h0
  let Zq : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory := ⟨Z, hZ⟩
  let ιq : Zq ⟶ FZ := ObjectProperty.homMk ι
  have hβ' := associatedTransition_comm P Y.F Y.alpha ι β hβ
  let E : QuasicoherentSheaves.{u, u} B S hS (presentationGroupoid P).objects.obj
      (presentationGroupoid P).objects.property :=
    ⟨(presentationObjectsFunctor P).obj Z, (eU.functor.obj Zq).property⟩
  let : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS P.U)).IsClosedUnderKernels :=
    isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS (yoneda.obj P.U)
      (isAlgebraicSpace_yoneda B S hS P.U)
  let : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS P.U)).IsClosedUnderCokernels :=
    isClosedUnderCokernels_quasicoherentSheaves B S hS (yoneda.obj P.U)
      (isAlgebraicSpace_yoneda B S hS P.U)
  have hpl : PreservesFiniteLimits (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS P.U)).ι :=
    @SheafOfModules.preservesFiniteLimits_ι_isQuasicoherentOnSite.{u + 1, u, u, u} _ _ _
      (representedStructureRingSheaf B S hS P.U) _ _ _ _ _
  have hpc : PreservesLimitsOfShape WalkingCospan (SheafOfModules.isQuasicoherentOnSite.{u + 1,
      u, u, u} (representedStructureRingSheaf B S hS P.U)).ι :=
    hpl.preservesFiniteLimits WalkingCospan
  have hιq : Mono ιq := (ObjectProperty.ι _).mono_of_mono_map hι
  have i1 : eU.functor.PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction eU.symm.toAdjunction
  have hFι : Mono (eU.functor.map ιq) := @Functor.map_mono _ _ _ _ eU.functor i1 _ _ ιq hιq
  have i2 : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS P.U)).ι.PreservesMonomorphisms :=
    @preservesMonomorphisms_of_preservesLimitsOfShape _ _ _ _ _ hpc
  have hLι : Mono ((presentationObjectsFunctor P).map ι) :=
    @Functor.map_mono _ _ _ _ _ i2 _ _ (eU.functor.map ιq) hFι
  have hε : Mono (schemeModuleOfModulesIso P Y.F).hom :=
    ⟨fun g h hgh => by
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (· ≫ (schemeModuleOfModulesIso P Y.F).inv) hgh⟩
  have hι' : Mono (associatedInclusion P Y.F ι) := mono_comp' hLι hε
  have hsflat : IsFlat B S hS (presentationGroupoid P).source.hom :=
    isFlat_of_isEtale B S hS (presentationGroupoid_source_isEtale P)
  have hc := mono_modulePullback_map_of_isFlat
    ((presentationGroupoid P).comp ≫ (presentationGroupoid P).source)
    (isFlat_comp_comp_source (presentationGroupoid P) hsflat) _ hι'
  have he := mono_modulePullback_map_of_isFlat
    (GroupoidInAlgebraicSpaces.identityArrow (presentationGroupoid P) ≫
      (presentationGroupoid P).source)
    (isFlat_identityArrow_comp_source (presentationGroupoid P)) _ hι'
  refine ⟨restrictedQuasicoherentModule Y E _ _ hβ' hc he,
    restrictedQuasicoherentModuleHom Y E _ _ hβ' hc he, Z, hZ, hZκ, ⟨Iso.refl _⟩, ?_⟩
  intro Y'' a b hab
  have hab' : associatedInclusion P Y.F ι ≫ a.hom = associatedInclusion P Y.F ι ≫ b.hom :=
    congrArg QuasicoherentModule.Hom.hom hab
  have key : eU.functor.map ιq ≫ eU.counit.app Y.F ≫ presentationQcohHom P a.hom =
      eU.functor.map ιq ≫ eU.counit.app Y.F ≫ presentationQcohHom P b.hom := by
    apply ObjectProperty.hom_ext
    simp only [associatedInclusion, schemeModuleOfModulesIso, Functor.mapIso_hom] at hab'
    exact hab'
  have h2 : ιq ≫ eU.inverse.map (presentationQcohHom P a.hom) =
      ιq ≫ eU.inverse.map (presentationQcohHom P b.hom) :=
    comp_inverse_map_eq_of_counit eU ιq _ _ key
  have h3 := congrArg (fun k => Scheme.Modules.Hom.app
    (X := (BigFppfOver.toScheme B S hS).obj P.U) k.hom O y) h2
  rw [← hy]
  simp only [ObjectProperty.FullSubcategory.comp_hom] at h3
  exact h3

end Core

section SeparatingFamily

open Stacks.AlgebraicGeometry

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **A separating family of quasi-coherent modules on an algebraic space.**  For an algebraic
space `F` there is a family of quasi-coherent `𝒪_F`-modules, indexed by a type in the universe of
the schemes, which is separating in `QCoh(𝒪_F)`.

This is the generator of the source's proof of Stacks 077V, part (1).  Choose a presentation
`F = U/R` (Stacks 0263).  By Stacks 03M3,
`AlgebraicGeometry.Space.isEquivalence_quasicoherentFromSpaceBase`, `QCoh(𝒪_F)` is equivalent
to the quasi-coherent modules on the groupoid `(U, R, s, t, c)`.  Let `κ` bound the affine opens
of `U` and of `R`.  The quasi-coherent modules on the groupoid whose underlying module comes from
a `κ`-generated quasi-coherent Zariski module on `U` have only a set of isomorphism classes —
the `κ`-generated modules form a set by Stacks 077M, and over a fixed underlying module the
transition morphisms form a set — and every local section of a quasi-coherent module on the
groupoid lies in such a submodule, by the closure step of Stacks 077U,
`AlgebraicGeometry.Space.exists_restricted_of_section`.  So a set of representatives separates. -/
theorem exists_isSeparating_quasicoherentSheaves :
    ∃ (β : Type u) (f : β → QuasicoherentSheaves.{u, u} B S hS F hF),
      (ObjectProperty.ofObj f).IsSeparating := by
  classical
  obtain ⟨P⟩ : Nonempty (Presentation B S hS F hF) := ⟨presentationOfIsAlgebraicSpace B S hS F hF⟩
  let eU := representedQuasicoherentSchemeEquivalence B S hS P.U
  let Pz : ObjectProperty ((BigFppfOver.toScheme B S hS).obj P.U).Modules := fun M =>
    M.IsQuasicoherent ∧ CardinalGeneration.IsCardinalGenerated M (presentationCardinal P)
  have : ObjectProperty.EssentiallySmall.{u}
      (fun M : ((BigFppfOver.toScheme B S hS).obj P.U).Modules =>
        CardinalGeneration.IsCardinalGenerated M (presentationCardinal P)) :=
    AlgebraicGeometry.CardinalGenerated.essentiallySmall_isCardinalGenerated
      (X := ((BigFppfOver.toScheme B S hS).obj P.U).toRingedSpace) (presentationCardinal P)
  have : ObjectProperty.EssentiallySmall.{u} Pz :=
    ObjectProperty.EssentiallySmall.of_le fun _ h => h.2
  obtain ⟨Q, hQsmall, -, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{u} Pz
  have := hQsmall
  let W : Subtype Q → Modules.{u, u} B S hS (presentationGroupoid P).objects.obj
      (presentationGroupoid P).objects.property :=
    fun z => (presentationObjectsFunctor P).obj z.1
  have : LocallySmall.{u} (Modules.{u, u} B S hS (presentationGroupoid P).arrows.obj
      (presentationGroupoid P).arrows.property) :=
    locallySmall_modules_smallEtale B S hS _ _
  let Aset : Subtype Q → Type (u + 1) := fun z =>
    {a : (modulePullback B S hS (presentationGroupoid P).target).obj (W z) ⟶
        (modulePullback B S hS (presentationGroupoid P).source).obj (W z) //
      ∃ (Y : QuasicoherentModule B S hS (presentationGroupoid P)) (e : Y.F.obj ≅ W z),
        transportedTransition Y e = a}
  let Ind := Σ z : Subtype Q, Aset z
  have : Small.{u} Ind := inferInstance
  let rep : Ind → QuasicoherentModule B S hS (presentationGroupoid P) :=
    fun i => Classical.choose i.2.2
  have hrep : ∀ (Y : QuasicoherentModule B S hS (presentationGroupoid P)) (z : Subtype Q)
      (e : Y.F.obj ≅ W z),
      ∃ i : Ind, Nonempty (rep i ≅ Y) := by
    intro Y z e
    let i : Ind := ⟨z, ⟨transportedTransition Y e, Y, e, rfl⟩⟩
    obtain ⟨e₀, h₀⟩ := Classical.choose_spec i.2.2
    exact ⟨i, ⟨isoOfTransportedTransitionEq e₀ e h₀⟩⟩
  let fG : Shrink.{u} Ind → QuasicoherentModule B S hS (presentationGroupoid P) :=
    fun b => rep ((equivShrink Ind).symm b)
  have hsepG : (ObjectProperty.ofObj fG).IsSeparating := by
    intro M M' a b hab
    apply QuasicoherentModule.Hom.ext
    have hq : eU.inverse.map (presentationQcohHom P a.hom) =
        eU.inverse.map (presentationQcohHom P b.hom) := by
      apply ObjectProperty.hom_ext
      refine scheme_modules_hom_ext_of_app_apply _ _ fun O x => ?_
      have h0 := exists_restricted_of_section P M O
        (x : Γ(((schemeModuleOf P M.F).obj : ((BigFppfOver.toScheme B S hS).obj P.U).Modules), O))
      obtain ⟨Y', j, Z, hZ, hZκ, ⟨eY⟩, hj⟩ := h0
      have hz : Pz Z := ⟨hZ, hZκ⟩
      have hz' := hPQ Z hz
      obtain ⟨Z₀, hZ₀, ⟨eZ⟩⟩ := hz'
      have e1 : Y'.F.obj ≅ W ⟨Z₀, hZ₀⟩ := eY ≪≫ (presentationObjectsFunctor P).mapIso eZ
      have h1 := hrep Y' ⟨Z₀, hZ₀⟩ e1
      obtain ⟨i, ⟨ei⟩⟩ := h1
      have hmem : ObjectProperty.ofObj fG (rep i) :=
        (ObjectProperty.ofObj_iff fG _).2 ⟨equivShrink Ind i, by simp [fG]⟩
      have h := hab (rep i) hmem (ei.hom ≫ j)
      have h' : j ≫ a = j ≫ b := by
        rw [Category.assoc, Category.assoc] at h
        exact (cancel_epi ei.hom).1 h
      exact hj M' a b h'
    exact congrArg (fun k => k.hom) (eU.inverse.map_injective hq)
  have := isEquivalence_quasicoherentFromSpaceBase B S hS (presentationGroupoid P)
    (presentationAtlas P)
    (presentationAtlas_isEtale P) (presentationAtlas_comm P)
    (presentationAtlas_isEtaleCovering P) (presentationAtlas_relativelyRepresentable P)
    (presentationGroupoid_isPullback P)
  let eqv := (quasicoherentFromSpaceBase B S hS (presentationGroupoid P) (presentationAtlas P)
    (presentationAtlas_comm P)).asEquivalence
  refine ⟨Shrink.{u} Ind, eqv.inverse.obj ∘ fG, ?_⟩
  refine (hsepG.of_equivalence eqv.symm).of_le ?_
  rintro _ ⟨X, ⟨i⟩⟩
  exact ObjectProperty.ofObj_apply _ i

end SeparatingFamily

section Stacks077V

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **`QCoh(𝒪_F)` has a separator**, for every algebraic space `F`: a coproduct of the separating
family of `AlgebraicGeometry.Space.exists_isSeparating_quasicoherentSheaves`.  The coproduct
exists in `QCoh(𝒪_F)` because quasi-coherence is closed under direct sums
(`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_discrete_quasicoherentSheaves`). -/
instance hasSeparator_quasicoherentSheaves :
    HasSeparator (QuasicoherentSheaves.{u, u} B S hS F hF) := by
  obtain ⟨β, f, hf⟩ := exists_isSeparating_quasicoherentSheaves (B := B) (S := S) (hS := hS)
    (F := F) (hF := hF)
  have := isClosedUnderColimitsOfShape_discrete_quasicoherentSheaves B S hS F hF β
  exact ⟨∐ f, (isSeparator_sigma f).2 hf⟩

variable (B S hS F hF)

/-- **`QCoh(𝒪_F)` is a Grothendieck abelian category**, at the universe of the schemes.  This is
`AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure` with every input
discharged: the separator is `AlgebraicGeometry.Space.hasSeparator_quasicoherentSheaves`, the
closure under arbitrary colimits is
`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse`, and
local smallness of the ambient modules is
`AlgebraicGeometry.Space.locallySmall_modules_smallEtale`. -/
theorem quasicoherentSheaves_isGrothendieckAbelian :
    letI := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
    letI := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
    letI := quasicoherentSheaves_abelian_of_closure B S hS F hF
    IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS F hF) :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  let := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  let := quasicoherentSheaves_abelian_of_closure B S hS F hF
  have := locallySmall_modules_smallEtale B S hS F hF
  quasicoherentSheaves_isGrothendieckAbelian_of_closure B S hS F hF
    fun K _ _ => isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse B S hS F hF K

/-- **`QCoh(𝒪_F)` has all limits**, being Grothendieck abelian
(`CategoryTheory.IsGrothendieckAbelian.hasLimits`). -/
theorem quasicoherentSheaves_hasLimitsOfSize :
    letI := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
    letI := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
    HasLimitsOfSize.{u, u} (QuasicoherentSheaves.{u, u} B S hS F hF) :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  let := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  let := quasicoherentSheaves_abelian_of_closure B S hS F hF
  have := quasicoherentSheaves_isGrothendieckAbelian B S hS F hF
  inferInstance

/-- **`QCoh(𝒪_F)` has enough injectives**, being Grothendieck abelian
(`CategoryTheory.IsGrothendieckAbelian.enoughInjectives`). -/
theorem quasicoherentSheaves_enoughInjectives :
    letI := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
    letI := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
    EnoughInjectives (QuasicoherentSheaves.{u, u} B S hS F hF) :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  let := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  let := quasicoherentSheaves_abelian_of_closure B S hS F hF
  have := quasicoherentSheaves_isGrothendieckAbelian B S hS F hF
  inferInstance

/-- **The inclusion `QCoh(𝒪_F) ⥤ Mod(𝒪_F)` has a right adjoint, the coherator.**

The special adjoint functor theorem applies: `QCoh(𝒪_F)` is cocomplete, locally small and
well-copowered because it is Grothendieck abelian, the inclusion preserves all colimits because
quasi-coherence is closed under them and the inclusion therefore creates them, and the separator
`AlgebraicGeometry.Space.hasSeparator_quasicoherentSheaves` provides the small separating
family. -/
theorem isLeftAdjoint_ι_quasicoherentSheaves :
    letI := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
    letI := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).ι.IsLeftAdjoint :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  let := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  let := quasicoherentSheaves_abelian_of_closure B S hS F hF
  have := locallySmall_modules_smallEtale B S hS F hF
  have := quasicoherentSheaves_isGrothendieckAbelian B S hS F hF
  have hPres : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι :=
    ⟨fun {K} _ =>
      have := isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse B S hS F hF K
      preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape _⟩
  have := hPres
  isLeftAdjoint_of_preservesColimits_of_isSeparating.{u} (isSeparator_separator _) _

/-- **The adjunction morphism `Q(𝓕) ⟶ 𝓕` of the coherator is an isomorphism at a quasi-coherent
`𝒪_F`-module `𝓕`.**  The inclusion is fully faithful, so the counit is an isomorphism exactly on
its essential image by `CategoryTheory.Adjunction.isIso_counit_app_iff_mem_essImage`, and a
quasi-coherent module is in that image. -/
theorem isIso_quasicoherentCoheratorCounit_app
    (M : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite) :
    letI := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
    letI := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
    letI := isLeftAdjoint_ι_quasicoherentSheaves B S hS F hF
    IsIso ((Adjunction.ofIsLeftAdjoint
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O))).ι).counit.app M) :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  let := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  let := isLeftAdjoint_ι_quasicoherentSheaves B S hS F hF
  (Adjunction.isIso_counit_app_iff_mem_essImage _).mpr ⟨⟨M, hM⟩, ⟨Iso.refl _⟩⟩

/-- **Stacks 077V, part (1).**  Let `F` be an algebraic space over a scheme `S`.  The category
`QCoh(𝒪_F)` of quasi-coherent `𝒪_F`-modules is a Grothendieck abelian category; consequently it
has enough injectives and all limits.

The abelian structure is the one given by the kernel and cokernel clauses of Stacks 03M1.  The
three conditions of a Grothendieck abelian category are: colimits, which exist and agree with
those of `𝒪_F`-modules by Stacks 03M1; exactness of filtered colimits; and a generator, which
is `AlgebraicGeometry.Space.hasSeparator_quasicoherentSheaves`, built from a presentation
`F = U/R` through Stacks 03M3 and 077U.  The assertions on injectives and limits hold in every
Grothendieck abelian category (Stacks 079H, 07D8). -/
@[stacks 077V "(1) QCoh(𝒪_X) is a Grothendieck abelian category; consequently it has enough \
injectives and all limits", sga "4 I 7.13" "special case", sga "4 V 0.2.1" "special case"]
theorem quasicoherentSheaves_isGrothendieckAbelian_enoughInjectives_hasLimits :
    letI := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
    letI := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
    letI := quasicoherentSheaves_abelian_of_closure B S hS F hF
    IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS F hF) ∧
      EnoughInjectives (QuasicoherentSheaves.{u, u} B S hS F hF) ∧
      HasLimitsOfSize.{u, u} (QuasicoherentSheaves.{u, u} B S hS F hF) :=
  ⟨quasicoherentSheaves_isGrothendieckAbelian B S hS F hF,
    quasicoherentSheaves_enoughInjectives B S hS F hF,
    quasicoherentSheaves_hasLimitsOfSize B S hS F hF⟩

/-- **Stacks 077V, part (2).**  Let `F` be an algebraic space over a scheme `S`.  The inclusion
functor `QCoh(𝒪_F) ⥤ Mod(𝒪_F)` has a right adjoint `Q`, the *coherator*, such that for every
quasi-coherent `𝒪_F`-module `𝓕` the adjunction morphism `Q(𝓕) ⟶ 𝓕` is an isomorphism.

The right adjoint exists by the special adjoint functor theorem applied to the Grothendieck
abelian category of part (1),
`AlgebraicGeometry.Space.isLeftAdjoint_ι_quasicoherentSheaves`; the inclusion is fully
faithful, so the counit is an isomorphism exactly on its essential image,
`AlgebraicGeometry.Space.isIso_quasicoherentCoheratorCounit_app`. -/
@[stacks 077V "(2) the inclusion QCoh(𝒪_X) ⥤ Mod(𝒪_X) has a right adjoint Q whose adjunction \
morphism Q(F) ⟶ F is an isomorphism for every quasi-coherent F"]
theorem exists_coherator :
    ∃ (Q : Modules.{u, u} B S hS F hF ⥤ QuasicoherentSheaves.{u, u} B S hS F hF)
      (adj : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι ⊣ Q),
      ∀ (M : Modules.{u, u} B S hS F hF), M.IsQuasicoherentOnSite → IsIso (adj.counit.app M) :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  let := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  let := isLeftAdjoint_ι_quasicoherentSheaves B S hS F hF
  ⟨_, Adjunction.ofIsLeftAdjoint _,
    fun M hM => isIso_quasicoherentCoheratorCounit_app B S hS F hF M hM⟩

end Stacks077V

end AlgebraicGeometry.Space

end
