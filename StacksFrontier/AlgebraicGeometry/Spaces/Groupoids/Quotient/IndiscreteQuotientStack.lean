module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionGerbe
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftHomEquivalenceOver
public import StacksFrontier.CategoryTheory.Sites.Stackification.FullyFaithfulProjection
public import StacksFrontier.Deformation.Artin.FormalObject.Effectiveness

/-!
# Quotient stacks of indiscrete groupoids

Let `G` be a groupoid in algebraic spaces over an algebraic space `B` over a scheme `S` of a big
fppf site, and suppose that at every test object `T` the space of objects has exactly one
`T`-point and the space of arrows at most one. Then every pointwise groupoid of `G` is the
trivial groupoid, the pointwise groupoid fibration of `G` is the base fibred over itself, and so
is its stackification: the projection `[U/R] ⟶ (Sch/S)_fppf` of the quotient stack (Stacks 044Q)
is full and faithful, and every object of the base carries an object of `[U/R]`.

The case of interest is the trivial group acting on a base `B` with one point over every test
object, such as `Spec k` over `Spec k`: then `[B/1]` is the base itself, and every system of
objects of it is effective in the sense of Stacks 0CXT, over every base cocone whatsoever.

## Main results

* `CategoryTheory.faithful_presheafOfGroupoids_p` and `CategoryTheory.full_presheafOfGroupoids_p`:
  the category attached to a presheaf of groupoids whose values are indiscrete has a full and
  faithful projection.
* `AlgebraicGeometry.Stack.full_quotientStack_p` and
  `AlgebraicGeometry.Stack.faithful_quotientStack_p`: the projection of the quotient stack of an
  indiscrete groupoid is full and faithful.
* `AlgebraicGeometry.Stack.exists_quotientStack_p_obj_eq`: every object of the base carries an
  object of that quotient stack.
* `AlgebraicGeometry.Stack.isEffectiveSystem_quotientStack_of_subsingleton`: every system of
  objects of that quotient stack is effective over every base cocone.
* `AlgebraicGeometry.Stack.isEffectiveSystem_quotientStack_trivialGroup`: the same for the
  quotient of a base with one point over every test object by the trivial group.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u u₁ u₂ v₁ v₂

namespace CategoryTheory

open Pseudofunctor

attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, u₂})

/-- The projection of the category attached to a presheaf of groupoids is faithful when each value
has at most one morphism between any two objects. -/
theorem faithful_presheafOfGroupoids_p
    (hsub : ∀ (T : 𝒞) (x y : F.obj (op T)), Subsingleton (x ⟶ y)) :
    (presheafOfGroupoids F).p.Faithful where
  map_injective {X Y} f g h := by
    refine CoGrothendieck.Hom.ext _ _ h ?_
    exact (hsub X.base _ _).elim _ _

/-- The projection of the category attached to a presheaf of groupoids is full when each value
has a morphism between any two objects. -/
theorem full_presheafOfGroupoids_p
    (hne : ∀ (T : 𝒞) (x y : F.obj (op T)), Nonempty (x ⟶ y)) :
    (presheafOfGroupoids F).p.Full where
  map_surjective {X _} f := ⟨⟨f, Classical.choice (hne X.base _ _)⟩, rfl⟩

end CategoryTheory

namespace Deformation.Artin

section FullyFaithful

universe u₃ v₃

/-- Every system of objects is effective over every base cocone when `p` is full and faithful
and every object of the base is the image of an object: the vertex of the base cocone lifts, and
so does each of its legs, uniquely. -/
public theorem isEffectiveSystem_of_full_of_faithful {J : Type u₁} [Category.{v₁} J]
    {X : Type u₂} [Category.{v₂} X] {C : Type u₃} [Category.{v₃} C] (p : X ⥤ C) [p.Full]
    [p.Faithful] (hsurj : ∀ c : C, ∃ x : X, p.obj x = c) (ξ : J ⥤ X) (c : Cocone (ξ ⋙ p)) :
    IsEffectiveSystem p ξ c := by
  obtain ⟨pt, ι⟩ := c
  obtain ⟨y, rfl⟩ := hsurj pt
  refine ⟨⟨y, ⟨fun j => p.preimage (ι.app j), fun i j f => p.map_injective ?_⟩⟩, ?_⟩
  · simpa using ι.naturality f
  · exact congrArg (Cocone.mk (p.obj y))
      (NatTrans.ext (funext fun j => p.map_preimage (ι.app j)))

end FullyFaithful

end Deformation.Artin

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (hobj : ∀ T, Subsingleton (G.objects.obj.obj T))
  (harr : ∀ T, Subsingleton (G.arrows.obj.obj T))

include harr in
/-- Two arrows between the same points of a pointwise groupoid of `G` are equal when `G` has at
most one arrow over every test object. -/
private theorem subsingleton_evaluation_hom (T : (BigFppfOver C S hS)ᵒᵖ)
    (x y : G.toGroupoidInFunctors.Evaluation T) : Subsingleton (x ⟶ y) :=
  ⟨fun _ _ => (G.toGroupoidInFunctors.evaluationArrowEquiv T x y).injective
    (Subtype.ext ((harr T).elim _ _))⟩

include hobj in
/-- Any two points of a pointwise groupoid of `G` are joined by an arrow when `G` has at most one
point over every test object. -/
private theorem nonempty_evaluation_hom (T : (BigFppfOver C S hS)ᵒᵖ)
    (x y : G.toGroupoidInFunctors.Evaluation T) : Nonempty (x ⟶ y) := by
  obtain rfl : x = y := (hobj T).elim x y
  exact ⟨𝟙 x⟩

include hobj harr in
/-- The pointwise groupoid fibration of `G` has a full and faithful projection. -/
private theorem full_faithful_quotientPrestack_p :
    (quotientPrestack G).p.Full ∧ (quotientPrestack G).p.Faithful := by
  have : (ULiftHom.down : ULiftHom.{u + 1} (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj ⥤ _).Full :=
    Functor.full_uliftHomDown
  have : (ULiftHom.down : ULiftHom.{u + 1} (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj ⥤ _).Faithful :=
    Functor.faithful_uliftHomDown
  have := full_presheafOfGroupoids_p (evaluationGroupoidFunctor G.toGroupoidInFunctors)
    (fun T => nonempty_evaluation_hom G hobj (op T))
  have := faithful_presheafOfGroupoids_p (evaluationGroupoidFunctor G.toGroupoidInFunctors)
    (fun T => subsingleton_evaluation_hom G harr (op T))
  exact ⟨show Functor.Full (ULiftHom.down ⋙
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p) from
      inferInstance,
    show Functor.Faithful (ULiftHom.down ⋙
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p) from
      inferInstance⟩

include hobj harr in
/-- **The projection of the quotient stack of an indiscrete groupoid is full.** -/
theorem full_quotientStack_p : (quotientStack G).p.Full := by
  have : (ULiftHom.down : ULiftHom.{u + 1} (BigFppfOver C S hS) ⥤ _).Full :=
    Functor.full_uliftHomDown
  have : (ULiftHom.down : ULiftHom.{u + 1} (BigFppfOver C S hS) ⥤ _).Faithful :=
    Functor.faithful_uliftHomDown
  obtain ⟨_, _⟩ := full_faithful_quotientPrestack_p G hobj harr
  exact Functor.Stackification.full_of_full_of_faithful
    (isFibredOneMorphism_toQuotientStack G) (BigFppfOver.topology C S hS)
    (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G)
    (isStack_quotientStack G).isMorSheaf
    (ULiftHom.down : ULiftHom.{u + 1} (BigFppfOver C S hS) ⥤ _) ULiftHom.up rfl

include hobj harr in
/-- **The projection of the quotient stack of an indiscrete groupoid is faithful.** -/
theorem faithful_quotientStack_p : (quotientStack G).p.Faithful := by
  have : (ULiftHom.down : ULiftHom.{u + 1} (BigFppfOver C S hS) ⥤ _).Full :=
    Functor.full_uliftHomDown
  have : (ULiftHom.down : ULiftHom.{u + 1} (BigFppfOver C S hS) ⥤ _).Faithful :=
    Functor.faithful_uliftHomDown
  obtain ⟨_, _⟩ := full_faithful_quotientPrestack_p G hobj harr
  exact Functor.Stackification.faithful_of_full_of_faithful
    (isFibredOneMorphism_toQuotientStack G) (BigFppfOver.topology C S hS)
    (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G)
    (isStack_quotientStack G).isMorSheaf
    (ULiftHom.down : ULiftHom.{u + 1} (BigFppfOver C S hS) ⥤ _) ULiftHom.up rfl

/-- Every object of the base over which the object space of `G` has a point carries an object of
the quotient stack: the image of that point. -/
theorem exists_quotientStack_p_obj_eq (T : BigFppfOver C S hS)
    (x : G.objects.obj.obj (op T)) : ∃ ξ : (quotientStack G).obj, (quotientStack G).p.obj ξ = T :=
  let a₀ : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj := ⟨T, x⟩
  let a : (quotientPrestack G).obj := ULiftHom.objUp.{u + 1, u + 1} a₀
  ⟨(toQuotientStack G).obj a, Functor.congr_obj (isFibredOneMorphism_toQuotientStack G).comp_eq a⟩

include hobj harr in
/-- **Every system of objects of the quotient stack of an indiscrete groupoid is effective**, over
every base cocone: the projection is full and faithful and every object of the base carries an
object, which is all that `Deformation.Artin.isEffectiveSystem_of_full_of_faithful` needs. -/
theorem isEffectiveSystem_quotientStack_of_subsingleton
    (hne : ∀ T, Nonempty (G.objects.obj.obj T))
    {J : Type u₁} [Category.{v₁} J] (ξ : J ⥤ (quotientStack G).obj)
    (c : Cocone (ξ ⋙ (quotientStack G).p)) :
    Deformation.Artin.IsEffectiveSystem (quotientStack G).p ξ c := by
  have := full_quotientStack_p G hobj harr
  have := faithful_quotientStack_p G hobj harr
  exact Deformation.Artin.isEffectiveSystem_of_full_of_faithful _
    (fun T => exists_quotientStack_p_obj_eq G T (Classical.choice (hne (op T)))) ξ c

open CartesianMonoidalCategory in
/-- **The quotient of a one-point base by the trivial group.** Let `B` have exactly one point over
every test object, let `𝟙_` be the trivial group over `B`, acting on `B` over itself, and let `Q`
be the action groupoid of that action. Every system of objects of `[B/𝟙_]` is effective over every
base cocone. -/
theorem isEffectiveSystem_quotientStack_trivialGroup
    (hB : ∀ T, Subsingleton (B.obj.obj T)) (hBne : ∀ T, Nonempty (B.obj.obj T))
    (hA hX : IsAlgebraicSpace C S hS (𝟙_ (Over B.obj)).left)
    (Q : Space.ActionGroupoidConstruction B (𝟙_ (Over B.obj)) (𝟙_ (Over B.obj)) hA hX)
    {J : Type u₁} [Category.{v₁} J] (ξ : J ⥤ (quotientStack Q.groupoid).obj)
    (c : Cocone (ξ ⋙ (quotientStack Q.groupoid).p)) :
    Deformation.Artin.IsEffectiveSystem (quotientStack Q.groupoid).p ξ c := by
  have hunit : ∀ T, Subsingleton ((𝟙_ (Over B.obj)).left.obj T) := hB
  have hobj : ∀ T, Subsingleton (Q.groupoid.objects.obj.obj T) := by
    rw [Q.objects_eq]; exact hunit
  have harr : ∀ T, Subsingleton (Q.groupoid.arrows.obj.obj T) := by
    rw [Q.arrows_eq]
    intro T
    refine ⟨fun a b => ((pullbackObjIso _ _ T).toEquiv.trans
      (Types.pullbackIsoPullback _ _).toEquiv).injective ?_⟩
    exact Subtype.ext (Prod.ext ((hunit T).elim _ _) ((hunit T).elim _ _))
  have hne : ∀ T, Nonempty (Q.groupoid.objects.obj.obj T) := by
    rw [Q.objects_eq]; exact hBne
  exact isEffectiveSystem_quotientStack_of_subsingleton Q.groupoid hobj harr hne ξ c

end AlgebraicGeometry.Stack
