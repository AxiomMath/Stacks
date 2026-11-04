module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.MorPresheaf
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonFullyFaithful

/-!
# The structure isomorphism of the comparison at a square of fibres

The value of `Deformation.Artin.fiberSquareComparison` at an object `z` of the fibre over the
fourth corner of a commutative square is an object of a categorical pullback, so it carries a
structure isomorphism between the two iterated chosen pullbacks of `z`. By construction that
isomorphism is the composite of the two pullback-composition comparisons with the
`CategoryTheory.eqToIso` of the square's commutativity in between. This file reads it off, in two
forms.

The second form is the one a consumer uses. It is stated for the canonical choice of pullbacks,
and in it the `CategoryTheory.eqToIso` has disappeared: both comparisons are instances of
`CategoryTheory.Functor.pullbackFiberCompIso'`, which takes the morphism the composite is equal to
as a *named* argument, so writing both at the one name `f ≫ i` makes the transport implicit in
that argument instead.

## Main results

* `Deformation.Artin.fiberSquareComparison_obj_iso_hom` — the structure isomorphism for an
  arbitrary choice of pullbacks.
* `Deformation.Artin.fiberSquareComparison_obj_iso_hom_fac` — its compatibility with the two
  composites of chosen cartesian lifts that it compares.
* `Deformation.Artin.fiberSquareComparison_chosenPullbacks_obj_iso_hom` — the structure
  isomorphism for the canonical choice of pullbacks, free of `CategoryTheory.eqToIso`.

## Implementation notes

`Deformation.Artin.eqToIso_pullbackFunctor_app_fac` is the only place the commutativity of the
square is transported, and it is proved by substituting one side of that equality for the other —
which is possible because the two morphisms are quantified over, so that one of them is a variable
the other can replace. The same statement with the composite written out is not provable this way,
which is why the lemma is stated at a quantified pair of morphisms rather than inlined.

`Deformation.Artin.fiberSquareComparison_obj_iso_hom` is `rfl`; it is recorded because the
unfolding that makes it so needs the local reducibility attributes that
`StacksFrontier/Deformation/Artin/RimSchlessinger/ComparisonFullyFaithful.lean` sets, and which a
consumer that does not set them cannot see through.

## References

* [Stacks Project, Tag 02XN](https://stacks.math.columbia.edu/tag/02XN)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u v w

namespace Deformation.Artin

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

variable {C : Type u} [Category.{v} C] {X : Type w} [Category X]
variable (p : X ⥤ C) (c : p.ChoiceOfPullbacks)

/-- Transporting a chosen pullback along an equality of the morphism it is taken along is
compatible with the chosen cartesian lifts: the transport followed by the lift of the second
morphism is the lift of the first. -/
public theorem eqToIso_pullbackFunctor_app_fac {U V : C} {m m' : V ⟶ U} (hm : m = m')
    (z : p.Fiber U) :
    Fiber.fiberInclusion.map ((eqToIso (congrArg c.pullbackFunctor hm)).hom.app z) ≫
        c.map m' z =
      c.map m z := by
  subst hm
  simp

/-- **The structure isomorphism of the value of the comparison at an object.** It is the inverse
of the comparison `(f ∘ i)^* ≅ f^* ∘ i^*`, then the transport along the commutativity of the
square, then the comparison `(g ∘ j)^* ≅ g^* ∘ j^*`. -/
public theorem fiberSquareComparison_obj_iso_hom {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) (z : p.Fiber Z) :
    ((fiberSquareComparison p c f g i j h).obj z).iso.hom =
      (c.objCompIso f i z).inv ≫ (eqToIso (congrArg c.pullbackFunctor h)).hom.app z ≫
        (c.objCompIso g j z).hom :=
  rfl

/-- **The structure isomorphism of the value of the comparison at an object is compatible with the
two composites of chosen cartesian lifts it compares.** -/
public theorem fiberSquareComparison_obj_iso_hom_fac {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) (z : p.Fiber Z) :
    Fiber.fiberInclusion.map ((fiberSquareComparison p c f g i j h).obj z).iso.hom ≫
        c.map g (c.obj j z) ≫ c.map j z =
      c.map f (c.obj i z) ≫ c.map i z := by
  rw [fiberSquareComparison_obj_iso_hom, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, ChoiceOfPullbacks.objCompIso_hom_fac, eqToIso_pullbackFunctor_app_fac p c h,
    ← ChoiceOfPullbacks.objCompIso_hom_fac c f i z, ← Category.assoc, ← Functor.map_comp]
  simp

/-- **The structure isomorphism of the value of the comparison at an object, for the canonical
choice of pullbacks.** Both contractions of the iterated chosen pullbacks are taken at the one
named morphism `f ≫ i`, so no transport along the commutativity of the square appears. -/
public theorem fiberSquareComparison_chosenPullbacks_obj_iso_hom [p.IsFibered] {U V W Z : C}
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) (z : p.Fiber Z) :
    ((fiberSquareComparison p (chosenPullbacks p) f g i j h).obj z).iso.hom =
      (pullbackFiberCompIso' z i f (f ≫ i) rfl).hom ≫
        (pullbackFiberCompIso' z j g (f ≫ i) h.symm).inv := by
  refine fiber_hom_ext_of_cartesian (g ≫ j)
    (IsPreFibered.pullbackMap (pullbackFiber p z j).2 g ≫ IsPreFibered.pullbackMap z.2 j)
    (isCartesian_pullbackMap_comp_pullbackMap z j g (g ≫ j) rfl) _ _ ?_
  have hcontract : Fiber.fiberInclusion.map ((pullbackFiberCompIso' z i f (f ≫ i) rfl).hom ≫
        (pullbackFiberCompIso' z j g (f ≫ i) h.symm).inv) ≫
        IsPreFibered.pullbackMap (pullbackFiber p z j).2 g ≫ IsPreFibered.pullbackMap z.2 j =
      IsPreFibered.pullbackMap (pullbackFiber p z i).2 f ≫ IsPreFibered.pullbackMap z.2 i := by
    simp
  exact (fiberSquareComparison_obj_iso_hom_fac p (chosenPullbacks p) f g i j h z).trans
    hcontract.symm

end Deformation.Artin

end
