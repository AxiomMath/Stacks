module

public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Naturality of the projection-formula map for curried bifunctors

`CategoryTheory.adjunctionTensorMap_natural` states the naturality of the canonical map
`A (R G, H) ⟶ R (B (G, L H))` for bifunctors `C × C ⥤ C`. This file restates it for bifunctors
written in curried form `C ⥤ C ⥤ C`, one argument at a time.

## Main results

* `CategoryTheory.adjunctionTensorMap_natural_left_curried`: naturality of the canonical map in
  its first argument.
* `CategoryTheory.adjunctionTensorMap_natural_right_curried`: naturality of the canonical map in
  its second argument.
-/

@[expose] public section

namespace CategoryTheory

open scoped CategoryTheory.Prod

variable {C : Type*} {D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

section Curried

variable (TA : C ⥤ C ⥤ C) (TB : D ⥤ D ⥤ D)
  (β : Functor.uncurry.obj TA ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TB)

/-- The canonical map is natural in its first argument, the bifunctors written in curried form. -/
@[reassoc]
public lemma adjunctionTensorMap_natural_left_curried {G G' : D} (g : G ⟶ G') (H : C) :
    (TA.map (R.map g)).app H ≫
        adjunctionTensorMap adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) β G' H =
      adjunctionTensorMap adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) β G H ≫
        R.map ((TB.map g).app (L.obj H)) := by
  have h := adjunctionTensorMap_natural adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) β
    g (𝟙 H)
  simpa only [Functor.uncurry_obj_map, Functor.map_id, Category.comp_id] using h

/-- The canonical map is natural in its second argument, the bifunctors written in curried form. -/
@[reassoc]
public lemma adjunctionTensorMap_natural_right_curried (G : D) {H H' : C} (k : H ⟶ H') :
    (TA.obj (R.obj G)).map k ≫
        adjunctionTensorMap adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) β G H' =
      adjunctionTensorMap adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) β G H ≫
        R.map ((TB.obj G).map (L.map k)) := by
  have h := adjunctionTensorMap_natural adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) β
    (𝟙 G) k
  simpa only [Functor.uncurry_obj_map, Functor.map_id, NatTrans.id_app,
    Category.id_comp] using h

end Curried

end CategoryTheory

end
