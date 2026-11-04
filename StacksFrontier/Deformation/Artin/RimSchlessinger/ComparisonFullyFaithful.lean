module

public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong

/-!
# Full faithfulness of the comparison at a square of fibres

`Deformation.Artin.fiberSquareComparison` compares the fibre of a fibred category over the
fourth corner `Z` of a commutative square with the two-fibre product of the fibres over the two
middle corners `V` and `W`. This file reads its full faithfulness off the two chosen
restriction maps.

A morphism of the target of the comparison is a *pair* of morphisms, one in the fibre over `V`
and one in the fibre over `W`, subject to the compatibility with the two structure isomorphisms;
and the pair attached to a morphism `γ` of the fibre over `Z` is the pair of its chosen
restrictions `CategoryTheory.Functor.ChoiceOfPullbacks.homMap`. So the comparison is faithful
exactly when a morphism of the fibre over `Z` is determined by those two restrictions, and full
exactly when every compatible pair of morphisms is the pair of restrictions of one.

That is the content here: the two criteria, together with the four `rfl`-lemmas identifying the
components of the value of the comparison, at an object and at a morphism, with the chosen
pullbacks and the chosen restrictions.

## Main results

* `Deformation.Artin.fiberSquareComparison_obj_fst` and
  `Deformation.Artin.fiberSquareComparison_obj_snd` — the two components of the value of the
  comparison at an object are the two chosen pullbacks of that object.
* `Deformation.Artin.fiberSquareComparison_map_fst` and
  `Deformation.Artin.fiberSquareComparison_map_snd` — the two components of the value at a
  morphism are its two chosen restrictions.
* `Deformation.Artin.faithful_fiberSquareComparison_of_homMap_ext` — the comparison is faithful
  as soon as a morphism of the fibre over `Z` is determined by its two chosen restrictions.
* `Deformation.Artin.full_fiberSquareComparison_of_exists_homMap` — the comparison is full as
  soon as every pair of morphisms of the two middle fibres compatible with the structure
  isomorphisms is the pair of chosen restrictions of a morphism of the fibre over `Z`.

## Implementation notes

Nothing here is about the big fppf site, about thickenings or about pushouts: the two criteria
hold for the comparison at an arbitrary commutative square in the base of an arbitrary fibred
category, and the geometry of a particular square enters only when their hypotheses are
discharged. They are stated for an arbitrary `CategoryTheory.Functor.ChoiceOfPullbacks` for the
same reason.

The four component lemmas are `rfl`. They are nevertheless recorded, because the definitional
unfolding that makes them so needs
`CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback` and
the two projections of the categorical pullback to be reducible, which is arranged by a local
attribute; a consumer which does not set that attribute cannot see them.

The hypothesis of
`Deformation.Artin.full_fiberSquareComparison_of_exists_homMap` carries the compatibility
condition in the shape the morphisms of `CategoryTheory.Limits.CategoricalPullback` impose it,
namely against the structure isomorphism of the value of the comparison, rather than in an
unfolded form: that isomorphism is the canonical composite of the two pullback-composition
isomorphisms, and `Deformation.Artin.fiberSquareComparison` is where it is assembled.

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

variable {C : Type u} [Category.{v} C] {X : Type w} [Category X]
variable (q : X ⥤ C) (c : q.ChoiceOfPullbacks)
variable {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
variable (h : f ≫ i = g ≫ j)

/-- The first component of the value of the comparison at an object of the fibre over `Z` is its
chosen pullback along `i`. -/
public theorem fiberSquareComparison_obj_fst (x : q.Fiber Z) :
    ((fiberSquareComparison q c f g i j h).obj x).fst = c.obj i x :=
  rfl

/-- The second component of the value of the comparison at an object of the fibre over `Z` is
its chosen pullback along `j`. -/
public theorem fiberSquareComparison_obj_snd (x : q.Fiber Z) :
    ((fiberSquareComparison q c f g i j h).obj x).snd = c.obj j x :=
  rfl

/-- The first component of the value of the comparison at a morphism of the fibre over `Z` is
its chosen restriction along `i`. -/
public theorem fiberSquareComparison_map_fst {x y : q.Fiber Z} (α : x ⟶ y) :
    ((fiberSquareComparison q c f g i j h).map α).fst = c.homMap i α :=
  rfl

/-- The second component of the value of the comparison at a morphism of the fibre over `Z` is
its chosen restriction along `j`. -/
public theorem fiberSquareComparison_map_snd {x y : q.Fiber Z} (α : x ⟶ y) :
    ((fiberSquareComparison q c f g i j h).map α).snd = c.homMap j α :=
  rfl

/-- **The comparison at a square of fibres is faithful as soon as a morphism of the fibre over
the fourth corner is determined by its two chosen restrictions.** A morphism of the target of
the comparison is a compatible pair of morphisms of the two middle fibres, and the pair attached
to `α` is the pair of its chosen restrictions, so equality of the two images is exactly the
hypothesis of `hext`. -/
public theorem faithful_fiberSquareComparison_of_homMap_ext
    (hext : ∀ (x y : q.Fiber Z) (α β : x ⟶ y),
      c.homMap i α = c.homMap i β → c.homMap j α = c.homMap j β → α = β) :
    (fiberSquareComparison q c f g i j h).Faithful where
  map_injective {x y α β} e :=
    hext x y α β (congrArg CategoricalPullback.Hom.fst e)
      (congrArg CategoricalPullback.Hom.snd e)

/-- **The comparison at a square of fibres is full as soon as every compatible pair of
morphisms of the two middle fibres is a pair of chosen restrictions.** A morphism of the target
of the comparison is such a pair, its compatibility condition being the field
`CategoryTheory.Limits.CategoricalPullback.Hom.w`; the morphism of the fibre over `Z` supplied
by `hlift` has that pair as its image, by the two component lemmas and extensionality of
morphisms of a categorical pullback. -/
public theorem full_fiberSquareComparison_of_exists_homMap
    (hlift : ∀ (x y : q.Fiber Z) (α : c.obj i x ⟶ c.obj i y) (β : c.obj j x ⟶ c.obj j y),
      (c.pullbackFunctor f).map α ≫ ((fiberSquareComparison q c f g i j h).obj y).iso.hom =
          ((fiberSquareComparison q c f g i j h).obj x).iso.hom ≫
            (c.pullbackFunctor g).map β →
        ∃ γ : x ⟶ y, c.homMap i γ = α ∧ c.homMap j γ = β) :
    (fiberSquareComparison q c f g i j h).Full where
  map_surjective {x y} m := by
    obtain ⟨γ, hα, hβ⟩ := hlift x y m.fst m.snd m.w
    exact ⟨γ, CategoricalPullback.hom_ext hα hβ⟩

end Deformation.Artin

end
