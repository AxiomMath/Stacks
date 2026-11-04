module

public import Mathlib.CategoryTheory.Quotient.Preadditive
public import Mathlib.CategoryTheory.Shift.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.HasShift
public import StacksFrontier.Algebra.DGA.HomotopyCategoryShift

/-!
# The shift comparisons of the homotopy category of differential graded modules

For a differential graded algebra `(A, d)` over a commutative ring `R`, the homotopy category
`K(A, d)` of right differential graded `A`-modules is additive and carries the shift induced by
the shift `M ↦ M[k]` of differential graded modules. That structure is built in
`StacksDraft.Ch22.HomotopyCategoryShift`; this file records the *computations* of the resulting
comparison isomorphisms, in the spelling the pretriangulated structure consumes: the shift on
`K(A, d)` is the one `CategoryTheory.Quotient` induces from the shift downstairs, so the
quotient functor commutes with the shift on the nose and every component of its
`CategoryTheory.Functor.commShiftIso` is an `eqToHom`.

Those identities are what makes the pretriangulated structure of `K(A, d)` computable: a triangle
written with the comparison of `CategoryTheory.Quotient.functor_obj_shift` and one written with
`CategoryTheory.Functor.commShiftIso` are then the same triangle.

## Main results

* `DifferentialGradedModule.toHomotopyCategory_obj_shift`: the quotient functor commutes with the
  shift on objects on the nose.
* `DifferentialGradedModule.toHomotopyCategory_commShiftIso_hom_app` and
  `DifferentialGradedModule.toHomotopyCategory_commShiftIso_inv_app`: every component of the
  commutation isomorphism of the quotient functor with the shift is an `eqToHom`.
* `DifferentialGradedModule.toHomotopyCategory_shiftFunctor_map`: the shift of the homotopy class
  of a homomorphism is the homotopy class of its shift.
* `DifferentialGradedModule.toHomotopyCategory_map_shiftFunctorCompIsoId_hom_app` and
  `DifferentialGradedModule.toHomotopyCategory_map_shiftFunctorCompIsoId_inv_app`: the quotient
  functor carries the comparison `M[a][b] ≅ M` for `a + b = 0` to the corresponding comparison in
  the homotopy category.

## Implementation notes

The preadditive structure of `K(A, d)`, its zero object, the additivity of the quotient functor
and of the shift functors, and the shift itself all come from
`StacksDraft.Ch22.HomotopyCategoryShift`; nothing of that is repeated here.

The shift on the homotopy category is `CategoryTheory.HasShift.quotient`, obtained from
`DifferentialGradedModule.homotopyRelCompatibleWithShift`. Its objects and morphisms are those of
the shift of differential graded modules, but only after unfolding that construction, which the
elaborator does not do at default transparency; the identities below are therefore proved with
`with_unfolding_all rfl` and then used as rewrite rules, so that no later proof has to unfold
anything. The two statements about `shiftFunctorCompIsoId` are instead derived from
`CategoryTheory.Functor.map_shiftFunctorCompIsoId_hom_app` together with the computation of
`commShiftIso`, which keeps them cheap.

## References

* [Stacks Project, Tag 09JQ](https://stacks.math.columbia.edu/tag/09JQ)
* [Stacks Project, Tag 09K6](https://stacks.math.columbia.edu/tag/09K6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- The quotient functor to the homotopy category commutes with the shift on objects on the
nose. -/
theorem toHomotopyCategory_obj_shift (X : DifferentialGradedModule A) (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory A) n).obj ((toHomotopyCategory A).obj X) =
      (toHomotopyCategory A).obj
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) n).obj X) := by
  with_unfolding_all rfl

/-- Every component of the isomorphism expressing that the quotient functor commutes with the
shift is an `eqToHom`. -/
theorem toHomotopyCategory_commShiftIso_hom_app (X : DifferentialGradedModule A) (n : ℤ) :
    ((toHomotopyCategory A).commShiftIso n).hom.app X =
      eqToHom (toHomotopyCategory_obj_shift A X n).symm := by
  with_unfolding_all rfl

/-- Every component of the inverse of the isomorphism expressing that the quotient functor
commutes with the shift is an `eqToHom`. -/
theorem toHomotopyCategory_commShiftIso_inv_app (X : DifferentialGradedModule A) (n : ℤ) :
    ((toHomotopyCategory A).commShiftIso n).inv.app X =
      eqToHom (toHomotopyCategory_obj_shift A X n) := by
  rw [← cancel_epi (((toHomotopyCategory A).commShiftIso n).hom.app X), Iso.hom_inv_id_app,
    toHomotopyCategory_commShiftIso_hom_app, eqToHom_trans, eqToHom_refl]

/-- The shift of the homotopy class of a homomorphism is the homotopy class of its shift. -/
theorem toHomotopyCategory_shiftFunctor_map {X Y : DifferentialGradedModule A} (f : X ⟶ Y)
    (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory A) n).map ((toHomotopyCategory A).map f) =
      eqToHom (toHomotopyCategory_obj_shift A X n) ≫
        (toHomotopyCategory A).map (shiftMap f n) ≫
          eqToHom (toHomotopyCategory_obj_shift A Y n).symm := by
  with_unfolding_all rfl

/-- The comparison `M[a][b] = M[a][b]` for the quotient functor, iterated twice. -/
theorem toHomotopyCategory_obj_shift_shift (X : DifferentialGradedModule A) (a b : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory A) b).obj
        ((CategoryTheory.shiftFunctor (HomotopyCategory A) a).obj
          ((toHomotopyCategory A).obj X)) =
      (toHomotopyCategory A).obj
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) b).obj
          ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) a).obj X)) :=
  (congrArg (fun Z => (CategoryTheory.shiftFunctor (HomotopyCategory A) b).obj Z)
      (toHomotopyCategory_obj_shift A X a)).trans
    (toHomotopyCategory_obj_shift A
      ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) a).obj X) b)

/-- The quotient functor carries the comparison `M[a][b] ≅ M` for `a + b = 0` to the
corresponding comparison in the homotopy category. -/
theorem toHomotopyCategory_map_shiftFunctorCompIsoId_hom_app (X : DifferentialGradedModule A)
    (a b : ℤ) (h : a + b = 0) :
    (toHomotopyCategory A).map
        ((shiftFunctorCompIsoId (DifferentialGradedModule A) a b h).hom.app X) =
      eqToHom (toHomotopyCategory_obj_shift_shift A X a b).symm ≫
        (shiftFunctorCompIsoId (HomotopyCategory A) a b h).hom.app
          ((toHomotopyCategory A).obj X) := by
  rw [Functor.map_shiftFunctorCompIsoId_hom_app, toHomotopyCategory_commShiftIso_hom_app,
    toHomotopyCategory_commShiftIso_hom_app, eqToHom_map, ← Category.assoc, eqToHom_trans]

/-- The inverse form of
`DifferentialGradedModule.toHomotopyCategory_map_shiftFunctorCompIsoId_hom_app`. -/
theorem toHomotopyCategory_map_shiftFunctorCompIsoId_inv_app (X : DifferentialGradedModule A)
    (a b : ℤ) (h : a + b = 0) :
    (toHomotopyCategory A).map
        ((shiftFunctorCompIsoId (DifferentialGradedModule A) a b h).inv.app X) =
      (shiftFunctorCompIsoId (HomotopyCategory A) a b h).inv.app ((toHomotopyCategory A).obj X) ≫
        eqToHom (toHomotopyCategory_obj_shift_shift A X a b) := by
  rw [Functor.map_shiftFunctorCompIsoId_inv_app, toHomotopyCategory_commShiftIso_inv_app,
    toHomotopyCategory_commShiftIso_inv_app, eqToHom_map, eqToHom_trans]

/-- The comparison `M[a][b] ≅ M` of the homotopy category, computed in terms of the comparison of
differential graded modules. -/
theorem toHomotopyCategory_shiftFunctorCompIsoId_hom_app (X : DifferentialGradedModule A)
    (a b : ℤ) (h : a + b = 0) :
    (shiftFunctorCompIsoId (HomotopyCategory A) a b h).hom.app ((toHomotopyCategory A).obj X) =
      eqToHom (toHomotopyCategory_obj_shift_shift A X a b) ≫
        (toHomotopyCategory A).map
          ((shiftFunctorCompIsoId (DifferentialGradedModule A) a b h).hom.app X) := by
  rw [toHomotopyCategory_map_shiftFunctorCompIsoId_hom_app]
  simp

/-- The inverse form of
`DifferentialGradedModule.toHomotopyCategory_shiftFunctorCompIsoId_hom_app`. -/
theorem toHomotopyCategory_shiftFunctorCompIsoId_inv_app (X : DifferentialGradedModule A)
    (a b : ℤ) (h : a + b = 0) :
    (shiftFunctorCompIsoId (HomotopyCategory A) a b h).inv.app ((toHomotopyCategory A).obj X) =
      (toHomotopyCategory A).map
          ((shiftFunctorCompIsoId (DifferentialGradedModule A) a b h).inv.app X) ≫
        eqToHom (toHomotopyCategory_obj_shift_shift A X a b).symm := by
  rw [toHomotopyCategory_map_shiftFunctorCompIsoId_inv_app]
  simp

end DifferentialGradedModule
