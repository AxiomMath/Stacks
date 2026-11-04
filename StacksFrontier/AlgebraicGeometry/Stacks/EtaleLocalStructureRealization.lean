module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealizationEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.CartesianGroupoidQuotientStackEtale
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SchemeSplittings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SmallQuotientStackMap
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition

/-!
# Quotient stacks of realized groupoid schemes, and two étale 1-morphisms between them

The proofs of **Stacks 0DU3** and **Stacks 0DU4** pass from a groupoid scheme `(U, R, s, t, c)`
to the restriction `R|_{U''}` along an étale `U'' ⟶ U`, and from there to an open finite
subgroupoid `P ⊆ R|_{U''}`; the two 1-morphisms

    [U''/P] ⟶ [U''/R|_{U''}] ⟶ [U/R]

are then representable by algebraic spaces and étale (**Stacks 0DU2** for the first, and the
argument of Stacks 0DU2 for a restriction for the second). This file states both for the
realizations of the three groupoid schemes as groupoids in algebraic spaces
(`Stacks.Groupoids.GroupoidScheme.realization`), together with the algebraicity of their quotient
stacks (**Stacks 06FI**).

## Main results

* `Stacks.Groupoids.GroupoidScheme.isAlgebraicStack_quotientStack_realization`: Stacks 06FI at
  a realization.
* `Stacks.Groupoids.GroupoidScheme.isRelativelyEtale_smallQuotientStackMap_restriction`:
  the quotient stack of a restriction along an étale morphism is étale over the quotient stack.
* `Stacks.Groupoids.GroupoidScheme.isRelativelyEtale_smallQuotientStackMap_inclusion`:
  the quotient stack of an open finite subgroupoid is étale over the quotient stack.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space AlgebraicGeometry.Stack

universe u w

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (C : BigFppfSite.{u}) (hS : C.Contains S)

/-! ### Properties of Yoneda images of morphisms of schemes over `S` -/

section Yoneda

variable {X Y : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left) (f : X ⟶ Y)

/-- The underlying morphism of schemes of a morphism of schemes over `S` regarded in the site is
the original morphism. -/
theorem toScheme_map_schemeSiteMap :
    (BigFppfOver.toScheme C S hS).map (schemeSiteMap C hS hX hY f) = f.left := rfl

/-- The Yoneda image of a flat morphism of schemes over `S` is flat. -/
theorem isFlat_yoneda_map_schemeSiteMap [Flat f.left] :
    Space.IsFlat C S hS (yoneda.map (schemeSiteMap C hS hX hY f)) :=
  (Space.holdsOnEveryEtaleChart_yoneda_map_iff C S hS Flat.isEtaleLocalOnSourceAndTarget _).2
    (inferInstanceAs (Flat f.left))

/-- The Yoneda image of a morphism of schemes over `S` locally of finite presentation is locally
of finite presentation. -/
theorem isLocallyOfFinitePresentation_yoneda_map_schemeSiteMap
    [LocallyOfFinitePresentation f.left] :
    Space.IsLocallyOfFinitePresentation C S hS (yoneda.map (schemeSiteMap C hS hX hY f)) :=
  (Space.holdsOnEveryEtaleChart_yoneda_map_iff C S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget _).2
    (inferInstanceAs (LocallyOfFinitePresentation f.left))

/-- The Yoneda image of an open immersion of schemes over `S` is an open immersion. -/
theorem isOpenImmersion_yoneda_map_schemeSiteMap [IsOpenImmersion f.left] :
    Space.IsOpenImmersion C S hS (yoneda.map (schemeSiteMap C hS hX hY f)) :=
  MorphismProperty.relative_map (inferInstanceAs (IsOpenImmersion f.left))

/-- An isomorphism of schemes over `S`, regarded in the site, is an isomorphism. -/
instance isIso_schemeSiteMap [IsIso f] : IsIso (schemeSiteMap C hS hX hY f) := by
  refine ⟨schemeSiteMap C hS hY hX (inv f), ?_, ?_⟩
  · rw [← schemeSiteMap_comp, IsIso.hom_inv_id]
    apply Over.OverMorphism.ext; rfl
  · rw [← schemeSiteMap_comp, IsIso.inv_hom_id]
    apply Over.OverMorphism.ext; rfl

end Yoneda

/-! ### The quotient stack of a realization -/

variable {G : GroupoidScheme S} (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)

/-- The source of the realization of a groupoid scheme with flat source is flat. -/
theorem isFlat_realization_source [Flat G.source.left] :
    Space.IsFlat C S hS (G.realization C hS hU hR hP).source.hom :=
  isFlat_yoneda_map_schemeSiteMap C hS hR hU G.source

/-- The target of the realization of a groupoid scheme with flat target is flat. -/
theorem isFlat_realization_target [Flat G.target.left] :
    Space.IsFlat C S hS (G.realization C hS hU hR hP).target.hom :=
  isFlat_yoneda_map_schemeSiteMap C hS hR hU G.target

/-- The source of the realization of a groupoid scheme with locally finitely presented source is
locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_realization_source
    [LocallyOfFinitePresentation G.source.left] :
    Space.IsLocallyOfFinitePresentation C S hS (G.realization C hS hU hR hP).source.hom :=
  isLocallyOfFinitePresentation_yoneda_map_schemeSiteMap C hS hR hU G.source

/-- The target of the realization of a groupoid scheme with locally finitely presented target is
locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_realization_target
    [LocallyOfFinitePresentation G.target.left] :
    Space.IsLocallyOfFinitePresentation C S hS (G.realization C hS hU hR hP).target.hom :=
  isLocallyOfFinitePresentation_yoneda_map_schemeSiteMap C hS hR hU G.target

variable [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
  [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]

/-- **Stacks 06FI at a realization.** The quotient stack of the realization of a groupoid scheme
with flat, locally finitely presented source and target is an algebraic stack. -/
theorem isAlgebraicStack_quotientStack_realization :
    IsAlgebraicStack.{u, w} C S hS (quotientStack (G.realization C hS hU hR hP)) :=
  isAlgebraicStack_quotientStack_of_flat _
    (isFlat_realization_source C hS hU hR hP) (isFlat_realization_target C hS hU hR hP)
    (isLocallyOfFinitePresentation_realization_source C hS hU hR hP)
    (isLocallyOfFinitePresentation_realization_target C hS hU hR hP)

/-! ### The 1-morphisms induced by a restriction and by an open finite subgroupoid -/

variable {H : GroupoidScheme S} (hU' : C.Contains H.objects.left) (hR' : C.Contains H.arrows.left)
  (hP' : C.Contains (pullback H.source H.target).left)
  [Flat H.source.left] [LocallyOfFinitePresentation H.source.left]
  [Flat H.target.left] [LocallyOfFinitePresentation H.target.left]

/-- A morphism of groupoid schemes whose induced 1-morphism of quotient stacks of the
realizations is faithful induces a 1-morphism representable by algebraic spaces. -/
private theorem isRepresentableByAlgebraicSpaces_quotientStackMap_realization_of_faithful
    (φ : Hom G H)
    (h : (quotientStackMap (Hom.realization C hS φ hU hR hP hU' hR' hP')).toFunctor.Faithful) :
    Stack.IsRepresentableByAlgebraicSpaces C S hS
      (quotientStackMap (Hom.realization C hS φ hU hR hP hU' hR' hP')) :=
  isRepresentableByAlgebraicSpaces_quotientStackMap_of_faithful.{u, u} _
    (isAlgebraicStack_quotientStack_realization.{u, u} C hS hU hR hP)
    (isAlgebraicStack_quotientStack_realization.{u, u} C hS hU' hR' hP') h

/-- A morphism of groupoid schemes whose evaluated functors are faithful induces a 1-morphism of
quotient stacks of the realizations which is representable by algebraic spaces (Stacks 04Y5). -/
theorem isRepresentableByAlgebraicSpaces_quotientStackMap_realizationHom (φ : Hom G H)
    (hfaith : ∀ T : Over S, (φ.evaluation T).Faithful) :
    Stack.IsRepresentableByAlgebraicSpaces C S hS
      (quotientStackMap (Hom.realization C hS φ hU hR hP hU' hR' hP')) :=
  isRepresentableByAlgebraicSpaces_quotientStackMap_realization_of_faithful C hS hU hR hP hU' hR'
    hP' φ (faithful_quotientStackMap_of_evaluation_faithful _
      (Hom.realization_evaluation_faithful hS φ hU hR hP hU' hR' hP' hfaith))

/-- **The quotient stack of a restriction along an étale morphism is étale over the quotient
stack.** For a groupoid scheme `H` with flat, locally finitely presented source and target, an
étale morphism `g : U'' ⟶ U` to its object scheme and a groupoid scheme `R''` realizing the
restriction `H|_{U''}`, the 1-morphism `[U''/R''] ⟶ [U/H]` of quotient stacks of the
realizations is representable by algebraic spaces and has the relative property of being étale
(Stacks 03YK); hence so has the 1-morphism between their small models. -/
theorem isRelativelyEtale_smallQuotientStackMap_restriction {U'' : Over S}
    {g : U'' ⟶ H.objects} [Etale g.left]
    (R'' : AlgebraicGeometry.GroupoidScheme.Restriction H g)
    (hU : C.Contains R''.groupoid.objects.left) (hR : C.Contains R''.groupoid.arrows.left)
    (hP : C.Contains (pullback R''.groupoid.source R''.groupoid.target).left)
    [Flat R''.groupoid.source.left] [LocallyOfFinitePresentation R''.groupoid.source.left]
    [Flat R''.groupoid.target.left] [LocallyOfFinitePresentation R''.groupoid.target.left] :
    IsRelativelyEtale C S hS
      (smallQuotientStackMap.{u, w} (Hom.realization C hS (R''.hom) hU hR hP hU' hR' hP')
        (isAlgebraicStack_quotientStack_realization.{u, w} C hS hU hR hP)
        (isAlgebraicStack_quotientStack_realization.{u, w} C hS hU' hR' hP')).hom := by
  have hfaith : ∀ T : Over S, (R''.hom.evaluation T).Faithful := fun T =>
    (R''.evaluation_fullyFaithful T).some.faithful
  have hfull : ∀ T : Over S, (R''.hom.evaluation T).Full := fun T =>
    (R''.evaluation_fullyFaithful T).some.full
  have hrep := isRepresentableByAlgebraicSpaces_quotientStackMap_realizationHom C hS hU hR hP
    hU' hR' hP' R''.hom hfaith
  have hobj : R''.hom.mapObjects.left = (eqToHom R''.objects_eq).left ≫ g.left := by
    rw [R''.mapObjects_eq, Over.comp_left]
  have : IsIso (eqToHom R''.objects_eq).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom R''.objects_eq)))
  have : Etale R''.hom.mapObjects.left := by rw [hobj]; infer_instance
  exact isRelativelyEtale_smallQuotientStackMap _ _ _ hrep
    (hasRelativeProperty_etale_quotientStackMap_of_full_of_faithful
      (Hom.realization C hS (R''.hom) hU hR hP hU' hR' hP')
      (Hom.realization_evaluation_full hS (R''.hom) hU hR hP hU' hR' hP' hfull)
      (Hom.realization_evaluation_faithful hS (R''.hom) hU hR hP hU' hR' hP' hfaith)
      (isFlat_yoneda_map_schemeSiteMap C hS hU hU' R''.hom.mapObjects)
      (isLocallyOfFinitePresentation_yoneda_map_schemeSiteMap C hS hU hU' R''.hom.mapObjects)
      (isFlat_realization_source C hS hU' hR' hP')
      (isLocallyOfFinitePresentation_realization_source C hS hU' hR' hP') hrep)

/-- **Stacks 0DU2 at a realization: the quotient stack of an open finite subgroupoid is étale
over the quotient stack.** For a groupoid scheme `H` with flat, locally finitely presented source
and target and an open finite subgroupoid `P ⊆ H`, the 1-morphism `[U/P] ⟶ [U/H]` of quotient
stacks of the realizations is representable by algebraic spaces and has the relative property of
being étale; hence so has the 1-morphism between their small models. -/
theorem isRelativelyEtale_smallQuotientStackMap_inclusion
    (P : OpenFiniteSubgroupoid H) (hU : C.Contains P.subgroupoid.objects.left)
    (hR : C.Contains P.subgroupoid.arrows.left)
    (hP : C.Contains (pullback P.subgroupoid.source P.subgroupoid.target).left)
    [Flat P.subgroupoid.source.left] [LocallyOfFinitePresentation P.subgroupoid.source.left]
    [Flat P.subgroupoid.target.left] [LocallyOfFinitePresentation P.subgroupoid.target.left] :
    IsRelativelyEtale C S hS
      (smallQuotientStackMap.{u, w} (Hom.realization C hS (P.inclusion) hU hR hP hU' hR' hP')
        (isAlgebraicStack_quotientStack_realization.{u, w} C hS hU hR hP)
        (isAlgebraicStack_quotientStack_realization.{u, w} C hS hU' hR' hP')).hom := by
  have : IsOpenImmersion P.inclusion.mapArrows.left := P.arrows_open
  have hopen : Space.IsOpenImmersion C S hS
      (Hom.realization C hS (P.inclusion) hU hR hP hU' hR' hP').toGroupoidHom.mapArrows :=
    isOpenImmersion_yoneda_map_schemeSiteMap C hS hR hR' P.inclusion.mapArrows
  have hmono := mono_mapArrows_of_isOpenImmersion
    (Hom.realization C hS (P.inclusion) hU hR hP hU' hR' hP') hopen
  have hrep := isRepresentableByAlgebraicSpaces_quotientStackMap_realization_of_faithful C hS hU hR
    hP hU' hR' hP' P.inclusion (faithful_quotientStackMap_of_mono _ hmono)
  have : IsIso P.inclusion.mapObjects := by rw [P.mapObjects_eq]; infer_instance
  have hobj :
      IsIso (Hom.realization C hS (P.inclusion) hU hR hP hU' hR' hP').toGroupoidHom.mapObjects :=
    inferInstanceAs (IsIso (yoneda.map (schemeSiteMap C hS hU hU' P.inclusion.mapObjects)))
  exact isRelativelyEtale_smallQuotientStackMap _ _ _ hrep
    (hasRelativeProperty_etale_quotientStackMap
      (Hom.realization C hS (P.inclusion) hU hR hP hU' hR' hP') hobj hopen
      (isFlat_realization_source C hS hU' hR' hP')
      (isLocallyOfFinitePresentation_realization_source C hS hU' hR' hP') hrep)

end Stacks.Groupoids.GroupoidScheme

end
