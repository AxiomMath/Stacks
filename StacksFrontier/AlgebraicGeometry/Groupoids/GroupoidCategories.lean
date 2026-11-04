module

public import Mathlib.CategoryTheory.Groupoid
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse

/-!
# Groupoids, and the groupoid of points of a groupoid scheme

A groupoid is a category in which every morphism is an isomorphism. Its identities and inverses
are determined by its composition law, inversion is a bijection on arrows, and a map of
groupoids compatible with composition is automatically compatible with identities and inverses.
For a groupoid scheme, evaluation on test schemes gives groupoids, the inverse morphism is an
isomorphism and the identity morphism is a section of both source and target.

## Main results

* `CategoryTheory.Groupoid.eq_id_of_comp_eq`, `CategoryTheory.Groupoid.eq_inv_of_comp_eq_id`:
  identities and inverses are uniquely determined by composition.
* `Prefunctor.map_id_of_map_comp`, `Prefunctor.map_inv_of_map_comp`: a map of groupoids
  compatible with composition is compatible with identities and inverses.
* `Prefunctor.toFunctorOfMapComp`: such a map is a functor.

## Implementation notes

These are the assertions of the introduction to Section 0230 of the source, which describes a
groupoid by its sets of objects and arrows, source, target and composition. Mathlib's
`CategoryTheory.Groupoid` bundles the identity and the inverse as data; the first two lemmas say
that no other choice is possible, and `CategoryTheory.Groupoid.invEquiv` is inversion as a
bijection. For a groupoid scheme `Stacks.Groupoids.GroupoidScheme` the groupoid of points over a
test scheme is `Stacks.Groupoids.GroupoidScheme.evaluationGroupoid`; the remaining assertions of
the section are the lemmas registered below by `add_to_stacks`.

## References

* [Stacks Project, Tag 0230](https://stacks.math.columbia.edu/tag/0230)
-/

@[expose] public section

open CategoryTheory

universe v v' u u'

namespace CategoryTheory.Groupoid

variable {C : Type u} [Groupoid.{v} C]

/-- In a groupoid, a family of endomorphisms which is a right unit for composition is the family
of identities. -/
@[stacks 0230 "the identity map e is uniquely determined"]
theorem eq_id_of_comp_eq (e : ∀ X : C, X ⟶ X) (he : ∀ {X Y : C} (f : X ⟶ Y), f ≫ e Y = f)
    (X : C) : e X = 𝟙 X := by
  simpa using he (𝟙 X)

/-- In a groupoid, a right inverse of a morphism is its inverse. -/
@[stacks 0230 "the inverse map i is uniquely determined"]
theorem eq_inv_of_comp_eq_id (i : ∀ {X Y : C}, (X ⟶ Y) → (Y ⟶ X))
    (hi : ∀ {X Y : C} (f : X ⟶ Y), f ≫ i f = 𝟙 X) {X Y : C} (f : X ⟶ Y) :
    i f = Groupoid.inv f := by
  rw [Groupoid.inv_eq_inv]
  exact IsIso.eq_inv_of_hom_inv_id (hi f)

end CategoryTheory.Groupoid

namespace Prefunctor

variable {C : Type u} [Groupoid.{v} C] {D : Type u'} [Groupoid.{v'} D]

/-- A map of groupoids compatible with composition preserves identities. -/
@[stacks 0230 "a map of groupoids compatible with composition preserves identities"]
theorem map_id_of_map_comp (F : C ⥤q D)
    (hF : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), F.map (f ≫ g) = F.map f ≫ F.map g) (X : C) :
    F.map (𝟙 X) = 𝟙 (F.obj X) := by
  have h := hF (𝟙 X) (𝟙 X)
  rw [Category.id_comp] at h
  exact (cancel_epi (F.map (𝟙 X))).mp (h.symm.trans (Category.comp_id _).symm)

/-- A map of groupoids compatible with composition is a functor. -/
@[simps]
def toFunctorOfMapComp (F : C ⥤q D)
    (hF : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), F.map (f ≫ g) = F.map f ≫ F.map g) : C ⥤ D where
  obj := F.obj
  map := F.map
  map_id := F.map_id_of_map_comp hF
  map_comp := hF

/-- A map of groupoids compatible with composition preserves inverses. -/
@[stacks 0230 "a map of groupoids compatible with composition preserves inverses"]
theorem map_inv_of_map_comp (F : C ⥤q D)
    (hF : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), F.map (f ≫ g) = F.map f ≫ F.map g)
    {X Y : C} (f : X ⟶ Y) : F.map (Groupoid.inv f) = Groupoid.inv (F.map f) := by
  simp only [Groupoid.inv_eq_inv]
  exact (F.toFunctorOfMapComp hF).map_inv f

end Prefunctor

add_to_stacks 0230 "groupoid categories" CategoryTheory.Groupoid
add_to_sga "3 V 1.2" "partial" CategoryTheory.Groupoid
add_to_sga "4 I 6.5.1" CategoryTheory.Groupoid
add_to_sga "4 I 6.5.2" CategoryTheory.Groupoid
add_to_sga "4 XVIII 1.2.1" "partial" CategoryTheory.Groupoid
add_to_stacks 0230 "the inverse map i is a bijection" CategoryTheory.Groupoid.invEquiv
add_to_stacks 0230 "the points of a groupoid scheme over a test scheme form a groupoid"
  Stacks.Groupoids.GroupoidScheme.evaluationGroupoid
add_to_stacks 0230 "the inverse morphism of a groupoid scheme is an isomorphism"
  AlgebraicGeometry.groupoidInverse_left_isIso
add_to_stacks 0230 "the identity morphism is a section of the source"
  Stacks.Groupoids.identity_left_comp_source_left
add_to_stacks 0230 "the identity morphism is a section of the target"
  Stacks.Groupoids.identity_left_comp_target_left
add_to_stacks 0230 "a morphism of groupoid schemes is compatible with the inverses"
  AlgebraicGeometry.groupoidHom_map_inverse
