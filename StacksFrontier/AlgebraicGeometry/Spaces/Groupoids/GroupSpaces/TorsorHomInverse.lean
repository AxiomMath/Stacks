module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Inverting a cartesian square over an invertible base map

A morphism of torsors is cartesian: its map of total spaces identifies the source with the base
change of the target. When the morphism of bases is invertible, so is the map of total spaces,
and the inverse square is again cartesian. These are the four facts every torsor category needs
in order to build the inverse of an isomorphism, and they depend on nothing about torsors: only
on a cartesian square whose base map is invertible, read through a functor.

## Main results

* `CategoryTheory.IsPullback.inv_fst_comp_hom`, `CategoryTheory.IsPullback.hom_comp_map_inv` and
  `CategoryTheory.IsPullback.inv_fst` -- the inverse square and its two triangles.
* `CategoryTheory.map_inv_comp_of_comp` -- a map over an invertible base map, inverted.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A morphism compatible with two maps to a common target stays compatible when the morphism is
inverted and read through a functor. -/
theorem map_inv_comp_of_comp (F : C ⥤ D) {U U' : C} (b : U ⟶ U') [IsIso b]
    {B : D} {s : F.obj U ⟶ B} {s' : F.obj U' ⟶ B} (h : F.map b ≫ s' = s) :
    F.map (inv b) ≫ s = s' := by
  rw [← h, ← Category.assoc, ← F.map_comp, IsIso.inv_hom_id, F.map_id, Category.id_comp]

variable (F : C ⥤ D) {U U' : C} (b : U ⟶ U') [IsIso b]
    {T : Over (F.obj U)} {T' : Over (F.obj U')} {m : T.left ⟶ T'.left}
    (hp : IsPullback m T.hom T'.hom (F.map b))

include hp in
/-- Inverting the map of total spaces: it intertwines the two structure morphisms with the
inverse of the base map. -/
theorem IsPullback.inv_fst_comp_hom [IsIso m] :
    inv m ≫ T.hom = T'.hom ≫ inv (F.map b) := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, hp.w, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

include hp in
/-- The same identity with the functor applied to the inverse rather than the inverse of the
functor's value. -/
theorem IsPullback.hom_comp_map_inv [IsIso m] :
    T'.hom ≫ F.map (inv b) = inv m ≫ T.hom := by
  rw [F.map_inv]
  exact (hp.inv_fst_comp_hom F b).symm

include hp in
/-- The inverse of a cartesian square over an invertible base map is cartesian. -/
theorem IsPullback.inv_fst [IsIso m] :
    IsPullback (inv m) T'.hom T.hom (F.map (inv b)) :=
  IsPullback.of_horiz_isIso ⟨(hp.hom_comp_map_inv F b).symm⟩

end CategoryTheory
