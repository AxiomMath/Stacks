module

public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Pasting two squares that transport an endomorphism along a composite

The multiplication identity of conclusion (c) of [Stacks, Tag 0EX3] is a square across a long
composite of isomorphisms, and it is proved by crossing one factor at a time. Each crossing is a
square, and the squares have to be pasted.

Pasting is `CategoryTheory.Category.assoc` and two rewrites, but the objects of the composite in
question are values of right derived functors at tensor products of module sheaves, and a goal
mentioning them is large enough that `rw` and `simp only` fail to locate even `Category.assoc`.
The pasting is therefore proved once here, for bare variables, and used as a term.

## Main results

* `…TopDegreeBaseChange.comp_two_squares`: **an endomorphism transported across `A` and then
  across `B` is transported across `A ≫ B`.** Pasting it against itself transports along a
  composite of any length.
* `…TopDegreeBaseChange.map_comp_square`: **a functor carries a square transporting an
  endomorphism to a square transporting its image.** This is the step that lifts a crossing
  proved at the sheaf level to the cohomology the composite is formed in.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **Two commuting squares pasted along a composite.** If `dY` transports the endomorphism `m`
across `A` and `n` transports `dY` across `B`, then `n` transports `m` across `A ≫ B`.

Applying this to its own conclusion transports an endomorphism along a composite of any length:
for `A ≫ B ≫ D` the inner instance is taken at `B` and `D`, whose conclusion is the hypothesis
the outer instance needs at `B ≫ D`. -/
theorem comp_two_squares {C : Type*} [Category C] {X Y Z : C}
    {m : X ⟶ X} {A : X ⟶ Y} {B : Y ⟶ Z} {dY : Y ⟶ Y} {n : Z ⟶ Z}
    (h1 : m ≫ A = A ≫ dY) (h2 : dY ≫ B = B ≫ n) :
    m ≫ A ≫ B = (A ≫ B) ≫ n := by
  rw [← Category.assoc, h1, Category.assoc, Category.assoc, h2]

/-- **A functor carries a square transporting an endomorphism to a square transporting its
image.** If `n` transports `m` across `A`, then `F.map n` transports `F.map m` across
`F.map A`.

Stated for bare variables for the reason given in the module docstring: the instances below are
at objects for which `rw` cannot locate `CategoryTheory.Functor.map_comp`. -/
theorem map_comp_square {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y : C}
    {m : X ⟶ X} {A : X ⟶ Y} {n : Y ⟶ Y} (hsq : m ≫ A = A ≫ n) :
    F.map m ≫ F.map A = F.map A ≫ F.map n := by
  rw [← F.map_comp, ← F.map_comp, hsq]

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
