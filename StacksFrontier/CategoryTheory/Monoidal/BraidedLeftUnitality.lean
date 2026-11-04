module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Left unitality of a braided tensorator is its right unitality

Let `C` and `D` be braided monoidal categories and `F : C ⥤ D` a functor equipped with a unit
comparison `εIso : 𝟙_ D ≅ F(𝟙_ C)` and a tensorator `μIso X Y : F X ⊗ F Y ≅ F (X ⊗ Y)`.  The two
unitality clauses of `CategoryTheory.Functor.CoreMonoidal` are then **not independent**: if the
tensorator carries the braiding of `C` to that of `D`, either one implies the other.

This file proves the implication that is used in practice, right to left.  For the derived
pullback of [Stacks, Tag 079U] the right-unit coherence is the one the projection formula of
[Stacks, Tag 08EU] already needed, so it is the one that is available; the left-unit coherence
is then free, and in particular needs no second descent through K-flat representatives.

The argument is four rewrites and uses neither the associativity clause of a tensorator nor the
naturality of `μIso`: in `C` the left unitor is the braiding followed by the right unitor
(`CategoryTheory.braiding_rightUnitor`), the braiding hypothesis moves that past the tensorator,
`CategoryTheory.BraidedCategory.braiding_naturality_left` moves the unit comparison from the left
factor to the right, and the same identity of unitors read in `D` finishes.

## Main results

* `Stacks.CategoryTheory.Monoidal.left_unitality_of_braided`: the left-unitality clause of
  `CategoryTheory.Functor.CoreMonoidal` from its right-unitality clause and the braiding
  compatibility of the tensorator.

## Implementation notes

The hypotheses and the conclusion are spelled exactly as the fields `left_unitality`,
`right_unitality` of `CategoryTheory.Functor.CoreMonoidal` are, so that the conclusion can be
supplied to that structure with no reshaping.  The braiding hypothesis is spelled in the *lax*
direction — out of `F X ⊗ F Y` and into `F (X ⊗ Y)` — because that is the direction `μIso`
points; a comparison presented in the opposite direction is composed with `μIso` on both sides
first.

Nothing here is specific to a derived category, an abelian category or a sheaf: `F` is an
arbitrary functor and `μIso`, `εIso` arbitrary isomorphisms.  In particular `F` is not assumed
monoidal, which is the point — this is one of the clauses that makes it so.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace Stacks.CategoryTheory.Monoidal

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  (F : C ⥤ D)

/-- **For a braided tensorator, left unitality follows from right unitality.**

`εIso` and `μIso` are a unit comparison and a tensorator for `F`, `hbraid` says the tensorator
carries the braiding of `C` to that of `D`, and `hright` is the right-unitality clause of
`CategoryTheory.Functor.CoreMonoidal`.  The conclusion is that structure's left-unitality clause,
at the same spelling.

Neither the associativity clause nor the naturality of `μIso` is used. -/
theorem left_unitality_of_braided
    (εIso : 𝟙_ D ≅ F.obj (𝟙_ C))
    (μIso : ∀ X Y : C, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y))
    (hbraid : ∀ X Y : C, (μIso X Y).hom ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ (μIso Y X).hom)
    (hright : ∀ X : C, (ρ_ (F.obj X)).hom =
      F.obj X ◁ εIso.hom ≫ (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom)
    (X : C) :
    (λ_ (F.obj X)).hom =
      εIso.hom ▷ F.obj X ≫ (μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom := by
  rw [← braiding_rightUnitor X, Functor.map_comp,
    ← Category.assoc ((μIso (𝟙_ C) X).hom), hbraid, Category.assoc,
    BraidedCategory.braiding_naturality_left_assoc, ← hright, braiding_rightUnitor]

end Stacks.CategoryTheory.Monoidal

end
