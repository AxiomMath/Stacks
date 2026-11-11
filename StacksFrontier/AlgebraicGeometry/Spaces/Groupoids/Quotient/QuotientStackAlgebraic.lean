module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidRelativeProperty

/-!
# The quotient stack of a flat groupoid in algebraic spaces is algebraic

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` over a
scheme `S` of a big fppf site, with `s` and `t` flat and locally of finite presentation.
**Stacks 06FI** says that the quotient stack `[U/R]` of Stacks 044Q is then an algebraic stack
over `S`. Its proof applies Artin's theorem on representability of flat groupoids
(**Stacks 06DC**) to the canonical projection `π : S_U ⟶ [U/R]` of Stacks 044R: the source is an
algebraic space, and `π` is representable by algebraic spaces, surjective, flat and locally of
finite presentation by **Stacks 06FH**.

## Main definitions

* `AlgebraicGeometry.Stack.Theorem06DC`: Artin's theorem on representability of flat groupoids,
  as a hypothesis — a stack in groupoids receiving a representable, surjective, flat, locally
  finitely presented 1-morphism from a stack represented by an algebraic space is algebraic.
* `AlgebraicGeometry.Stack.Lemma06FH`: Stacks 06FH, as a hypothesis — for a groupoid whose source
  and target are flat and locally of finite presentation, the projection of Stacks 044R is
  surjective, flat and locally of finite presentation.
* `AlgebraicGeometry.Stack.QuotientStackIsomSheavesAlgebraic`: the conclusion of **Stacks 04TB**
  for a quotient stack, in the `ULift`-free shape
  `AlgebraicGeometry.Stack.representable_quotientStackProjectionHom_of_isomPresheafAlgebraic`
  consumes, and `AlgebraicGeometry.Stack.Lemma04TB`, the same for every groupoid over the site.
* `AlgebraicGeometry.Stack.QuotientStackHasSmoothPresentation`: the presentation clause of
  `AlgebraicGeometry.Stack.IsAlgebraicStack`, written out for a quotient stack.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_liftedObjectSpace`: the universe lift
  of the object-space fibration is represented by the object space, **Stacks 04SV**.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_hasSmoothPresentation`: a quotient
  stack satisfies every clause of algebraicity except the presentation, with no hypothesis on the
  groupoid beyond Stacks 04TB.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack`: Stacks 06FI from Stacks 06DC,
  Stacks 06FH and Stacks 04TB taken as hypotheses; the unconditional statement is
  `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_flat`.
* `AlgebraicGeometry.Stack.forall_isAlgebraicStack_quotientStack`: the same quantified over the
  groupoids on a fixed base, which is the shape a consumer takes Stacks 06FI in.

## Implementation notes

Four of the inputs Stacks 06DC asks for are discharged here rather than carried. The source of
the projection is `AlgebraicGeometry.Stack.liftedObjectSpace`, the object-space fibration with
its morphism universe raised to the one the quotient stack lives at; it is representable by the
object space because the raising functor is an equivalence over the site which commutes with the
structure functors on the nose, so the comparison of Stacks 04SV composes with the identity
comparison of `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fibredCategory`. Its two
stack clauses are `AlgebraicGeometry.Stack.liftedFibredCategory_isStack` and
`AlgebraicGeometry.Stack.isStackInGroupoids_liftedFibredCategory`, which apply because the
underlying based category of `liftedObjectSpace` is `liftedFibredCategory` of the object space on
the nose. The two stack clauses of the target are
`AlgebraicGeometry.Stack.isStack_quotientStack` and
`AlgebraicGeometry.Stack.isStackInGroupoids_quotientStack`. Representability of the projection is
**Stacks 04WZ** in the reduced form
`AlgebraicGeometry.Stack.representable_quotientStackProjectionHom_of_isomPresheafAlgebraic`,
whose input is the Stacks 04TB hypothesis `h04TB`.

The three hypotheses are proved elsewhere in the library: Stacks 06DC as
`AlgebraicGeometry.Stack.isAlgebraicStack_of_flatCover`, Stacks 04TB and Stacks 06FH for the
projection through
`AlgebraicGeometry.Stack.representable_quotientStackProjectionHom_unconditional` and
`AlgebraicGeometry.Stack.QuotientAtlas.surjective_flat_lfp_quotientStackProjectionHom`; they are
assembled, unconditionally, in `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_flat`.
The form here keeps `AlgebraicGeometry.Stack.Theorem06DC`, stated for an arbitrary 1-morphism of
stacks in groupoids at the morphism universe `u + 1` of `[U/R]`. That hypothesis cannot be
replaced by exhibiting the projection as the presentation clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack`: that clause demands a *smooth* presentation, and a
flat, locally finitely presented groupoid has no reason to give one —
`AlgebraicGeometry.dualNumbers_projections_not_smooth` is a counterexample to the strengthening.
Stacks 06FH is carried as `AlgebraicGeometry.Stack.Lemma06FH`; the lemma
`AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackProjectionHom_of_representingMap`
reduces it to Stacks 04M9 together with the three properties of `s`, which is why it is stated at
`AlgebraicGeometry.Stack.HasRelativeProperty` of Stacks 03YK rather than in any other spelling.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-- Flatness of a morphism of algebraic spaces over `S` (**Stacks 03ML**, part (1)), as a
property of morphisms of the category of algebraic spaces over `S`. -/
abbrev flatSpaceProperty : MorphismProperty (AlgebraicSpaces C S hS) :=
  fun ⦃_ _ : AlgebraicSpaces C S hS⦄ (g : _ ⟶ _) => Space.IsFlat C S hS g.hom

/-- Being locally of finite presentation (**Stacks 03XP**, part (1)), as a property of morphisms
of the category of algebraic spaces over `S`. -/
abbrev locallyOfFinitePresentationSpaceProperty : MorphismProperty (AlgebraicSpaces C S hS) :=
  fun ⦃_ _ : AlgebraicSpaces C S hS⦄ (g : _ ⟶ _) =>
    Space.IsLocallyOfFinitePresentation C S hS g.hom

/-- **Artin's theorem on representability of flat groupoids, Stacks 06DC, as a hypothesis.** A
stack in groupoids over the big fppf site of `S` is an algebraic stack as soon as it receives a
1-morphism, representable by algebraic spaces and relatively surjective, flat and locally of
finite presentation, from a stack in groupoids represented by an algebraic space.

This is a general criterion about an arbitrary 1-morphism of stacks in groupoids; it mentions no
groupoid and no quotient stack. -/
abbrev Theorem06DC.{u', w'} (C' : BigFppfSite.{u'}) (S' : Scheme.{u'}) (hS' : C'.Contains S') :
    Prop :=
  ∀ (𝒳 𝒴 : CatFiberedInGroupoids.{u', u' + 1, u' + 1, u' + 1} (BigFppfOver C' S' hS'))
    (F : 𝒳 ⟶ 𝒴), IsRepresentableByAlgebraicSpace C' S' hS' 𝒳 →
      𝒳.val.p.IsStack (BigFppfOver.topology C' S' hS') →
      𝒳.val.p.IsStackInGroupoids.{w'} (BigFppfOver.topology C' S' hS') →
      𝒴.val.p.IsStack (BigFppfOver.topology C' S' hS') →
      𝒴.val.p.IsStackInGroupoids.{w'} (BigFppfOver.topology C' S' hS') →
      ∀ hF : IsRepresentableByAlgebraicSpaces C' S' hS' F.hom,
        HasRelativeProperty.{u', u' + 1, u' + 1, u'} C' S' hS'
          (Space.surjectiveMorphismProperty C' S' hS') F hF →
        HasRelativeProperty.{u', u' + 1, u' + 1, u'} C' S' hS'
          (flatSpaceProperty C' S' hS') F hF →
        HasRelativeProperty.{u', u' + 1, u' + 1, u'} C' S' hS'
          (locallyOfFinitePresentationSpaceProperty C' S' hS') F hF →
        IsAlgebraicStack.{u', w'} C' S' hS' 𝒴.val

/-- **Stacks 06FH as a hypothesis.** For a groupoid in algebraic spaces whose source and target
are flat and locally of finite presentation, the canonical projection `S_U ⟶ [U/R]` of
Stacks 044R is relatively surjective, flat and locally of finite presentation in the sense of
Stacks 03YK.

The lemma
`AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackProjectionHom_of_representingMap`
reduces each of the three clauses to Stacks 04M9 together with that property of the source
map `s`. -/
abbrev Lemma06FH : Prop :=
  ∀ (A : AlgebraicSpaces C S hS) (G : GroupoidInAlgebraicSpaces C S hS A),
    Space.IsFlat C S hS G.source.hom → Space.IsFlat C S hS G.target.hom →
      Space.IsLocallyOfFinitePresentation C S hS G.source.hom →
      Space.IsLocallyOfFinitePresentation C S hS G.target.hom →
      ∀ hπ : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom,
        HasRelativeProperty.{u, u + 1, u + 1, u} C S hS
          (Space.surjectiveMorphismProperty C S hS) (quotientStackProjectionHom G) hπ ∧
        HasRelativeProperty.{u, u + 1, u + 1, u} C S hS
          (flatSpaceProperty C S hS) (quotientStackProjectionHom G) hπ ∧
        HasRelativeProperty.{u, u + 1, u + 1, u} C S hS
          (locallyOfFinitePresentationSpaceProperty C S hS)
          (quotientStackProjectionHom G) hπ

/-- **The conclusion of Stacks 04TB for a quotient stack**: every isomorphism sheaf of a fibre of
the quotient stack is an algebraic space over the scheme the fibre sits over, presented as a
presheaf of `Type u` together with a bijection over each object of the slice site, natural in
that object. -/
abbrev QuotientStackIsomSheavesAlgebraic {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) : Prop :=
  ∀ (T : BigFppfOver C S hS) (x y : (quotientStack G).p.Fiber T),
    ∃ F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace C T.left.1 T.left.2 F ∧
        ∃ e : ∀ V, ((Over.iteratedSliceBackward T).op ⋙
            (quotientStack G).p.isomPresheaf x y).obj V ≃ F.obj V,
          ∀ ⦃V₁ V₂⦄ (f : V₁ ⟶ V₂) (z : ((Over.iteratedSliceBackward T).op ⋙
              (quotientStack G).p.isomPresheaf x y).obj V₁),
            e V₂ (((Over.iteratedSliceBackward T).op ⋙
              (quotientStack G).p.isomPresheaf x y).map f z) = F.map f (e V₁ z)

/-- **The presentation clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` for a quotient
stack**: a 1-morphism to `[U/R]` from the category represented by a scheme over `S`,
representable by algebraic spaces, every algebraic space representing a base change of which
along a scheme-valued point has surjective and smooth structural morphism. -/
abbrev QuotientStackHasSmoothPresentation {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) : Prop :=
  ∃ (U : BigFppfOver C S hS)
    (f : (schemeFibredCategory C S hS U).val ⥤ᵇ quotientStack G),
    Stack.IsRepresentableByAlgebraicSpaces C S hS f ∧
      ∀ (V : BigFppfOver C S hS)
        (y : BigFppfOver C V.left.1 V.left.2 ⥤ (quotientStack G).obj)
        (_hy : y ⋙ (quotientStack G).p = Over.map V.hom)
        (F : (BigFppfOver C V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace C V.left.1 V.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map V.hom)
            (schemeFibredCategory C S hS U).val.p (quotientStack G).p y f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
          (let g := (algebraicSpaceMap C S hS V
            ((spacesOverSmallerBaseFunctor C V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
           Space.IsSurjective C S hS g ∧ Space.IsSmooth C S hS g)

/-- **Stacks 04TB as a hypothesis**, for every quotient stack of a groupoid in algebraic spaces
over the big fppf site of `S`. -/
abbrev Lemma04TB : Prop :=
  ∀ (A : AlgebraicSpaces C S hS) (G : GroupoidInAlgebraicSpaces C S hS A),
    QuotientStackIsomSheavesAlgebraic C S hS G

variable {C S hS}

/-- The universe lift of the object-space fibration of a groupoid in algebraic spaces is
represented, over the big fppf site, by the object space itself. This is **Stacks 04SV** for the
object space, transported along the universe lift of its morphisms. -/
theorem isRepresentableByAlgebraicSpace_liftedObjectSpace
    {A : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS A) :
    IsRepresentableByAlgebraicSpace C S hS (liftedObjectSpace G) := by
  refine ⟨G.objects.obj, G.objects.property, ⟨
    { hom := ⟨(ULiftHom.down : ULiftHom.{u + 1}
        (fibredCategory C S hS G.objects.obj).val.obj ⥤ _), rfl⟩
      inv := ⟨ULiftHom.up, rfl⟩
      unitIso := Iso.refl _
      counitIso := Iso.refl _
      unit_over := ?_
      counit_over := ?_ }⟩⟩
  all_goals
    apply StacksRepresentableCFG.whiskerRight_eq_eqToHom
    intro _
    exact IsHomLift.id rfl

/-- **Every clause of algebraicity of a quotient stack except the presentation.** The quotient
stack of a groupoid in algebraic spaces is an algebraic stack as soon as it has a smooth
surjective presentation by a scheme; no hypothesis on the source and target of the groupoid
enters.

The other three clauses are discharged outright: fibredness in groupoids and the two stack
conditions are those of **Stacks 044Q**, and the diagonal clause is **Stacks 04WZ** in the form
reduced to the Stacks 04TB hypothesis `h04TB`. So for a quotient stack the presentation is the
*only* residual content of algebraicity, and for a flat, locally finitely presented groupoid it
is exactly what Artin's theorem **Stacks 06DC** supplies — a flat presentation does not give a
smooth one, as `AlgebraicGeometry.dualNumbers_projections_not_smooth` shows. -/
theorem isAlgebraicStack_quotientStack_of_hasSmoothPresentation {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A)
    (h04TB : QuotientStackIsomSheavesAlgebraic C S hS G)
    (hpres : QuotientStackHasSmoothPresentation C S hS G) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) :=
  ⟨isFiberedInGroupoids_quotientStack G,
    ⟨isStack_quotientStack G, isStackInGroupoids_quotientStack G⟩,
    hasRepresentableDiagonal_quotientStack_of_isomPresheafAlgebraic G h04TB, hpres⟩

/-- **Stacks 06FI.** Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic
space `A` over a scheme `S` of a big fppf site. If the source and the target of `G` are flat and
locally of finite presentation, then the quotient stack `[U/R]` is an algebraic stack over `S`.

This form takes Artin's theorem **Stacks 06DC**, **Stacks 06FH** and **Stacks 04TB** as the
hypotheses `h06DC`, `h06FH` and `h04TB`. All three are proved in the library (Stacks 06DC as
`AlgebraicGeometry.Stack.isAlgebraicStack_of_flatCover`), and the unconditional statement is
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_flat`. -/
theorem isAlgebraicStack_quotientStack {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A)
    (h06DC : Theorem06DC.{u, w} C S hS) (h06FH : Lemma06FH C S hS)
    (h04TB : QuotientStackIsomSheavesAlgebraic C S hS G)
    (hsflat : Space.IsFlat C S hS G.source.hom)
    (htflat : Space.IsFlat C S hS G.target.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (htlfp : Space.IsLocallyOfFinitePresentation C S hS G.target.hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) := by
  have hπ : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom :=
    representable_quotientStackProjectionHom_of_isomPresheafAlgebraic G h04TB
  obtain ⟨hsurj, hflat, hlfp⟩ := h06FH A G hsflat htflat hslfp htlfp hπ
  exact h06DC (liftedObjectSpace G)
    (CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (quotientStackProjectionHom G) (isRepresentableByAlgebraicSpace_liftedObjectSpace G)
    (liftedFibredCategory_isStack G.objects)
    (isStackInGroupoids_liftedFibredCategory G.objects) (isStack_quotientStack G)
    (isStackInGroupoids_quotientStack G) hπ hsurj hflat hlfp

/-- **Stacks 06FI, quantified over the groupoids on a fixed base.** Every groupoid in algebraic
spaces over `A` whose source and target are flat and locally of finite presentation has an
algebraic quotient stack.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack` with the three carried
hypotheses pulled in front of the quantifier, which is the shape a consumer of Stacks 06FI — for
instance Stacks 06PL for the trivial action — takes it in. The unconditional form is
`AlgebraicGeometry.Stack.forall_isAlgebraicStack_quotientStack_of_flat`. -/
theorem forall_isAlgebraicStack_quotientStack (A : AlgebraicSpaces C S hS)
    (h06DC : Theorem06DC.{u, w} C S hS) (h06FH : Lemma06FH C S hS)
    (h04TB : Lemma04TB C S hS) :
    ∀ H : GroupoidInAlgebraicSpaces C S hS A,
      Space.IsFlat C S hS H.source.hom → Space.IsFlat C S hS H.target.hom →
        Space.IsLocallyOfFinitePresentation C S hS H.source.hom →
          Space.IsLocallyOfFinitePresentation C S hS H.target.hom →
            IsAlgebraicStack.{u, w} C S hS (quotientStack H) :=
  fun H hsflat htflat hslfp htlfp =>
    isAlgebraicStack_quotientStack H h06DC h06FH (h04TB A H) hsflat htflat hslfp htlfp

end AlgebraicGeometry.Stack

end
