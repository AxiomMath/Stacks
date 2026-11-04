module

public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# Images of admissible short exact sequences under a differential graded functor

A functor `F` of differential graded categories sends an admissible short exact sequence with a
chosen graded splitting to one, and the connecting morphism `π d(s)` of the image sequence is the
image `F(π d(s))` of the connecting morphism.

## Main definitions

* `DGCategory.DGFunctor.mapGradedSplitShortExact`: the image sequence.

## Main results

* `DGCategory.DGFunctor.connectingHom_mapGradedSplitShortExact`: the connecting morphism of the
  image sequence is the image of the connecting morphism.
* `DGCategory.DGFunctor.onComp_map_a` and `DGCategory.DGFunctor.onComp_map_b`: the two closed
  arrows of the image sequence are the images of the two closed arrows under the induced functor
  on the category of complexes.
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

variable {R : Type*} [CommRing R] {A B : DGCategory R}

/-- The image of an admissible short exact sequence with a chosen graded splitting under a
functor of differential graded categories, with the image splitting. -/
public def DGFunctor.mapGradedSplitShortExact (F : DGFunctor A B) {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    GradedSplitShortExact (A := B) (F.obj x) (F.obj y) (F.obj z) where
  a := F.mapCocycle E.a
  b := F.mapCocycle E.b
  π := F.map E.π
  s := F.map E.s
  π_a := by
    simp only [DGFunctor.mapCocycle]
    rw [← F.map_comp, E.π_a, F.map_id]
  b_s := by
    simp only [DGFunctor.mapCocycle]
    rw [← F.map_comp, E.b_s, F.map_id]
  π_s := by rw [← F.map_comp, E.π_s, F.map_zero]
  a_π_add_s_b := by
    simp only [DGFunctor.mapCocycle]
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, E.a_π_add_s_b, F.map_id]

/-- The connecting morphism of the image of an admissible short exact sequence is the image of
its connecting morphism. -/
public theorem DGFunctor.connectingHom_mapGradedSplitShortExact (F : DGFunctor A B)
    {x y z : A.Obj} (E : GradedSplitShortExact (A := A) x y z) :
    GradedSplitShortExact.connectingHom (F.mapGradedSplitShortExact E) =
      F.map (GradedSplitShortExact.connectingHom E) := by
  simp only [GradedSplitShortExact.connectingHom, DGFunctor.mapGradedSplitShortExact, F.map_comp,
    F.map_d]

/-- The inclusion of the image sequence is the image of the inclusion. -/
public theorem DGFunctor.onComp_map_a (F : DGFunctor A B) {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    (F.mapGradedSplitShortExact E).a =
      F.onComp.map (X := (x : A.Comp)) (Y := (y : A.Comp)) E.a := rfl

/-- The surjection of the image sequence is the image of the surjection. -/
public theorem DGFunctor.onComp_map_b (F : DGFunctor A B) {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    (F.mapGradedSplitShortExact E).b =
      F.onComp.map (X := (y : A.Comp)) (Y := (z : A.Comp)) E.b := rfl

end DGCategory
