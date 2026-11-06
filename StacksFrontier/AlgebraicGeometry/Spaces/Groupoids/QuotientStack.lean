module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.OfPresheaf
public import StacksFrontier.CategoryTheory.Sites.Stackification.Stackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.GroupoidStackification
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge
public import Mathlib.CategoryTheory.Category.ULift

/-!
# The quotient stack of a groupoid in algebraic spaces (Stacks 044Q)

Let `B` be an algebraic space over a scheme `S` of a big fppf site, and let `G` be a groupoid in
algebraic spaces over `B` in the sense of Stacks 043W. Evaluating `G` at every object of the big
fppf site gives a presheaf of groupoids; its Grothendieck construction is a category fibred in
groupoids over the site, the *pointwise groupoid fibration* of `G`. The *quotient stack* `[U/R]`
of `G` is the stackification of that fibration.

## Main definitions

* `AlgebraicGeometry.Stack.evaluationGroupoidFunctor`: the evaluation of a groupoid in presheaves,
  bundled as a groupoid-valued functor.
* `AlgebraicGeometry.Stack.quotientPrestack`: the pointwise groupoid fibration of `G`, with its
  morphisms raised to the universe the stackification construction needs.
* `AlgebraicGeometry.Stack.quotientStack`: **Stacks 044Q**, part (1) — the quotient stack `[U/R]`.
* `AlgebraicGeometry.Stack.toQuotientStack` and
  `AlgebraicGeometry.Stack.pointwiseToQuotientStack`: the canonical 1-morphisms from the
  universe-lifted and the original pointwise groupoid fibration to the quotient stack.

## Main results

* `AlgebraicGeometry.Stack.isStack_quotientStack`: the quotient satisfies descent for the fppf
  topology.
* `AlgebraicGeometry.Stack.isFiberedInGroupoids_quotientStack`: the quotient is fibred in
  groupoids.
* `AlgebraicGeometry.Stack.isStackInGroupoids_quotientStack`: the two together, in the sense of
  Stacks 02ZI.
* `AlgebraicGeometry.Stack.isLocallyBijective_toQuotientStack` and
  `AlgebraicGeometry.Stack.essImage_toQuotientStack`: the two clauses of Stacks 02ZN exhibiting
  the quotient as the stackification of the pointwise groupoid fibration. The second of them is
  also **Stacks 044X**, part (1): every object of the fibre category `[U/R]_T` is, locally on `T`
  for the fppf topology, isomorphic to the image of a `T`-point of `U`.

## DELIBERATE OWNERSHIP EXCEPTION — these are Chapter 78 tags

Stacks 044Q and Stacks 044X are `spaces-groupoids`, **Chapter 78**. They are here for the same
reason as `AlgebraicGeometry.GroupoidInAlgebraicSpaces` (Stacks 043W) in the sibling file
`GroupoidInSpaces.lean`: the Chapter 93–101 results that need the quotient stack — Stacks 04T4
parts (4) and (5), Stacks 04T5 and Stacks 05UL — cannot be stated without it. The canonical
1-morphism out of the quotient that those results name is available: Stacks 044U, the
two-coequalizer property of the quotient stack, is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuotientStackSquares/Coequalizer.lean`, and
`AlgebraicGeometry.Stack.exists_extension_quotientStack` there is the universal property of the
stackification, Stacks 0436, for this quotient. What Stacks 04T4 (5) and Stacks 04T5 still lack is
part (4) of Stacks 04T4, the groupoid in algebraic spaces itself.

## Implementation notes

Only part (1) of Stacks 044Q is formalized in this file. Part (2), the quotient stack `[X/G]` of a
group action, is the quotient stack of the action groupoid of Stacks 0444, which is formalized as
`AlgebraicGeometry.Space.groupoidOfAction` of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid`, whose
`ActionGroupoidConstruction` carries exactly the `GroupoidInAlgebraicSpaces` that `quotientStack`
consumes. Part (2) is `AlgebraicGeometry.Stack.quotientStackOfAction` of the sibling file
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuotientStackOfAction.lean`, which composes the
two; the tag `044Q` is carried by `quotientStack` here and by `quotientStackOfAction` there, the
two declarations together covering the whole definition.

Likewise only part (1) of Stacks 044X is registered here, and it is registered rather than
restated: part (1) is *the* stackification clause, so the declaration that carries it already
exists and no second general name is coined. Parts (2)–(6) of Stacks 044X are about
`[U/R]`-descent data and belong with the morphism description of Stacks 044V; they are not formalized
here.

The stackification used is the explicit three-stage construction of Stacks 02ZN,
`CategoryTheory.Functor.stageThreeProj`. Its input must have objects and morphisms in a common
universe, while the pointwise groupoid fibration of `G` has objects in `Type (u + 1)` and
morphisms in `Type u`; so the morphisms are raised by `CategoryTheory.ULiftHom` first. That lift
is an equivalence (`quotientPrestackEquivalence`) which commutes *strictly* with the projection
to the site, so nothing of the base category or of the fppf topology changes, and the original
fibration still maps to the quotient (`pointwiseToQuotientStack`).

That the quotient is fibred in groupoids is not part of the stackification construction: it is
Stacks 04WJ, `CategoryTheory.Functor.Stackification.isFiberedInGroupoids_of_isStackification`,
applied to the three clauses of Stacks 02ZN for this witness.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 06KB](https://stacks.math.columbia.edu/tag/06KB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v' w'

/-- Evaluation of a groupoid in presheaves, bundled as a groupoid-valued functor. This is the
groupoid-valued form of `Deformation.evaluationFunctor` (**Stacks 06KB**), which lands in `Cat`. -/
@[implicit_reducible]
noncomputable def evaluationGroupoidFunctor
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} D) : D ⥤ Grpd.{w, w} where
  obj T := Grpd.of ((Deformation.evaluationFunctor G).obj T)
  map f := Deformation.evaluationMap G f
  map_id T := congrArg Cat.Hom.toFunctor ((Deformation.evaluationFunctor G).map_id T)
  map_comp f g := congrArg Cat.Hom.toFunctor ((Deformation.evaluationFunctor G).map_comp f g)

/-- Raising the universe of the morphisms preserves a category fibred in groupoids.
The base category and its morphisms are unchanged. -/
theorem isFiberedInGroupoids_uliftHom
    {D : Type u} [Category.{v} D] {E : Type w} [Category.{v'} E]
    (p : E ⥤ D) (hp : p.IsFiberedInGroupoids) :
    ((ULiftHom.down : ULiftHom.{w'} E ⥤ E) ⋙ p).IsFiberedInGroupoids where
  exists_lift f x hx := by
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift f x.objDown hx
    exact ⟨ULiftHom.objUp y, ⟨φ⟩, (Functor.isHomLift_comp_iff ULiftHom.down p f ⟨φ⟩).2 hφ⟩
  unique_lift φ ψ f hf := by
    obtain ⟨χ, ⟨hχ, hcomp⟩, huniq⟩ := hp.unique_lift φ.down ψ.down f hf
    exact ⟨⟨χ⟩, ⟨hχ, congrArg ULift.up hcomp⟩,
      fun γ hγ => ULift.ext (huniq γ.down ⟨hγ.1, congrArg ULift.down hγ.2⟩)⟩

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The pointwise groupoid fibration, with its morphisms lifted to the universe needed
by stackification. `ULiftHom.equiv` identifies it with the original Grothendieck construction;
its base remains the original big fppf site. -/
noncomputable abbrev quotientPrestack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedCategory (BigFppfOver C S hS) :=
  let F : (BigFppfOver C S hS)ᵒᵖ ⥤ Grpd.{u, u} :=
    evaluationGroupoidFunctor G.toGroupoidInFunctors
  BasedCategory.ofFunctor
    ((ULiftHom.down : ULiftHom.{u + 1} (presheafOfGroupoids F).obj ⥤
      (presheafOfGroupoids F).obj) ⋙ (presheafOfGroupoids F).p)

/-- The universe lift is an equivalence with the original pointwise groupoid fibration. -/
noncomputable def quotientPrestackEquivalence
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj ≌
      (quotientPrestack G).obj :=
  ULiftHom.equiv

/-- The equivalence of presentations commutes strictly with the projection to the site. -/
theorem quotientPrestackEquivalence_comp
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientPrestackEquivalence G).functor ⋙ (quotientPrestack G).p =
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p := rfl

/-- The presentation of the quotient is fibred in groupoids. -/
theorem isFiberedInGroupoids_quotientPrestack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientPrestack G).p.IsFiberedInGroupoids :=
  isFiberedInGroupoids_uliftHom _ (isFiberedInGroupoids_presheafOfGroupoids _)

/-- The presentation of the quotient is a fibred category. -/
instance isFibered_quotientPrestack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientPrestack G).p.IsFibered :=
  (isFiberedInGroupoids_quotientPrestack G).isFibered

/-- **Stacks 044Q, part (1).** The quotient stack `[U/R]` of a groupoid in algebraic spaces, as a
category over the original big fppf site: the stackification of the pointwise groupoid
fibration. -/
@[stacks 044Q "part (1): quotient stack of a groupoid"]
noncomputable def quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedCategory (BigFppfOver C S hS) :=
  BasedCategory.ofFunctor
    ((quotientPrestack G).p.stageThreeProj (BigFppfOver.topology C S hS))

/-- The quotient stack is a fibred category. -/
instance isFibered_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientStack G).p.IsFibered :=
  Functor.isFibered_stageThreeProj _ _

/-- The canonical morphism from the pointwise groupoid presentation to its quotient stack. -/
noncomputable def toQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientPrestack G).obj ⥤ (quotientStack G).obj :=
  (quotientPrestack G).p.toStageThree (BigFppfOver.topology C S hS)

/-- The canonical morphism is a 1-morphism over the original fppf site. -/
theorem isFibredOneMorphism_toQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientPrestack G).p.IsFibredOneMorphism (quotientStack G).p (toQuotientStack G) :=
  Functor.isFibredOneMorphism_toStageThree _ _

/-- The quotient satisfies descent over the original fppf site. -/
theorem isStack_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientStack G).p.IsStack (BigFppfOver.topology C S hS) :=
  Functor.isStack_stageThreeProj.{u, u, u + 1, u + 1} _ _

/-- The quotient sheafifies the morphism presheaves of its presentation: clause (1) of
Stacks 02ZN for this witness. -/
theorem isLocallyBijective_toQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (U : BigFppfOver C S hS) (x y : (quotientPrestack G).p.Fiber U) :
    Presheaf.IsLocallyInjective ((BigFppfOver.topology C S hS).over U)
        ((isFibredOneMorphism_toQuotientStack G).morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective ((BigFppfOver.topology C S hS).over U)
        ((isFibredOneMorphism_toQuotientStack G).morPresheafMap x y) :=
  Functor.isLocallyBijective_morPresheafMap_toStageThree.{u, u, u + 1, u + 1} _ _ U x y

/-- Every object of the quotient locally comes from the pointwise groupoid presentation: clause
(2) of Stacks 02ZN for this witness, and part (1) of Stacks 044X. -/
@[stacks 044X "part (1): local representatives"]
theorem essImage_toQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (U : BigFppfOver C S hS) (x : (quotientStack G).p.Fiber U) :
    ∃ R ∈ BigFppfOver.topology C S hS U,
      ∀ ⦃V : BigFppfOver C S hS⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (Functor.fiberFunctorOfCompEq (isFibredOneMorphism_toQuotientStack G).comp_eq V).essImage
          (Functor.pullbackFiber (quotientStack G).p x f) :=
  Functor.essImage_pullbackFiber_toStageThree.{u, u, u + 1, u + 1} _ _ U x

/-- The stackification of this groupoid presentation is fibred in groupoids. -/
theorem isFiberedInGroupoids_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientStack G).p.IsFiberedInGroupoids :=
  Functor.Stackification.isFiberedInGroupoids_of_isStackification
    (isFiberedInGroupoids_quotientPrestack G) (isStack_quotientStack G)
    (isFibredOneMorphism_toQuotientStack G) (isLocallyBijective_toQuotientStack G)
    (essImage_toQuotientStack G)

/-- The quotient of a groupoid in algebraic spaces is a stack in groupoids on the
original big fppf site. -/
theorem isStackInGroupoids_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Functor.IsStackInGroupoids (quotientStack G).p
      (BigFppfOver.topology C S hS) :=
  (isStack_quotientStack G).isStackInGroupoids (isFiberedInGroupoids_quotientStack G)

/-- The canonical map from the original, unlifted pointwise groupoid fibration. -/
noncomputable def pointwiseToQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj ⥤
      (quotientStack G).obj :=
  (quotientPrestackEquivalence G).functor ⋙ toQuotientStack G

/-- The canonical map from the original pointwise groupoids lies over the site. -/
private theorem pointwiseToQuotientStack_comp
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    pointwiseToQuotientStack G ⋙ (quotientStack G).p =
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p := by
  rw [pointwiseToQuotientStack, Functor.assoc,
    (isFibredOneMorphism_toQuotientStack G).comp_eq, quotientPrestackEquivalence_comp]

/-- The canonical map from the original pointwise groupoids is a 1-morphism over the site. -/
theorem isFibredOneMorphism_pointwiseToQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsFibredOneMorphism
      (quotientStack G).p (pointwiseToQuotientStack G) where
  comp_eq := pointwiseToQuotientStack_comp G
  map_isStronglyCartesian := by
    intro R T f a b φ _
    have := Functor.isHomLift_map_of_comp_eq (pointwiseToQuotientStack_comp G) f φ
    exact (isFiberedInGroupoids_quotientStack G).isStronglyCartesian_homLift f _

end AlgebraicGeometry.Stack

end
