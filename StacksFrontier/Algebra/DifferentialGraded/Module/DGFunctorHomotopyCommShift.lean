module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorToComplexes
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomComplexExtGeneral

/-!
# The induced functor on homotopy categories against the comparison with the shift

Let `R` be a commutative ring, let `(A, d)` be a differential graded `R`-algebra, let `B` be an
`R`-linear preadditive category and let `F : Mod^dg_(A, d) ⥤ Comp^dg(B)` be a functor of
differential graded categories over `R`. The functor
`K(A, d) ⥤ K(B)` it induces commutes with the translation, and this file records *what* that
commutation is at the class of a differential graded module: the comparison
`F(M[n]) ≅ F(M)[n]` of `DifferentialGradedModule.dgFunctorToComplexesShiftIso`, conjugated by the
commutations of the two quotient functors with the translation.

## Main results

* `DifferentialGradedModule.dgFunctorToHomotopyCategory_commShiftIso_hom_app`: the commutation of
  the induced functor on homotopy categories with the translation, at the class of a differential
  graded module.
* `DifferentialGradedModule.General.homAddEquivOfEq_apply` and
  `DifferentialGradedModule.General.homAddEquivOfEq_comp_commShiftIso_inv`: the transport of a
  morphism along the equality of objects
  `DifferentialGradedModule.General.toHomotopyCategory_obj_shift` is composition with the
  commutation of the quotient functor with the translation, so the two spellings of the shift of a
  class cancel.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
* [Stacks Project, Tag 09LW](https://stacks.math.columbia.edu/tag/09LW)
* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex

namespace DifferentialGradedModule

universe r u v w t

variable {R : Type r} [CommRing R] {A : DifferentialGradedAlgebra.{r, u} R}
  {B : Type v} [Category.{w} B] [Preadditive B] [Linear R B]
  (F : DGCategory.DGFunctor (dgCategory.{r, u, t} A) (CochainComplex.dgCategoryLinear B R))

/-- **The commutation of the induced functor `K(A, d) ⥤ K(B)` with the translation, at the class
of a differential graded module.** It is the comparison `F(M[n]) ≅ F(M)[n]` of
`DifferentialGradedModule.dgFunctorToComplexesShiftIso`, preceded by the commutation of
`DifferentialGradedModule.toHomotopyCategory` with the translation and followed by that of
`CategoryTheory.HomotopyCategory.quotient`. -/
alias dgFunctorToHomotopyCategory_commShiftIso_hom_app := homotopyCategory_commShiftIso_hom

namespace General

/-- The transport of a morphism along an equality of its targets is composition with the
corresponding `CategoryTheory.eqToHom`. -/
theorem homAddEquivOfEq_apply {C : Type*} [Category C] [Preadditive C] {Y Z : C} (h : Y = Z)
    {W : C} (f : W ⟶ Y) :
    homAddEquivOfEq h f = f ≫ eqToHom h := by
  subst h
  simp [homAddEquivOfEq]

/-- **The two spellings of the shift of the class of a differential graded module cancel.** The
transport of a morphism `L ⟶ [M[n]]` along the equality of objects
`DifferentialGradedModule.General.toHomotopyCategory_obj_shift`, followed by the inverse of the
commutation of the quotient functor with the translation, is the morphism itself. -/
theorem homAddEquivOfEq_comp_commShiftIso_inv {L M : DifferentialGradedModule.{r, u, u} A}
    (n : ℤ) (f : (toHomotopyCategory A).obj L ⟶ (toHomotopyCategory A).obj (shift M n)) :
    homAddEquivOfEq (toHomotopyCategory_obj_shift A M n) f ≫
        ((toHomotopyCategory A).commShiftIso n).inv.app M =
      f := by
  rw [homAddEquivOfEq_apply, Category.assoc,
    show ((toHomotopyCategory A).commShiftIso n).inv.app M =
      eqToHom (quotient_obj_shift (A := A) M n) from
      quotientShiftIso_inv_eq_eqToHom M n,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

end General

end DifferentialGradedModule

end
