module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoreRHS
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.LinkYonedaCompat

/-!
# Crossing the comparison of the homotopy categories, on the image of a chain map

`CochainComplex.coreRHS_mk` computes the right-hand side of step 3's elementwise equation for
[Stacks, Tag 09LK] at a cocycle, carrying the passage across
`CochainComplex.homotopyCategoryEquivalence` as the hypothesis `hf`: that

`Φ'(f) ≫ σ_n : Φ'(K) ⟶ Φ'(Y)⟦n⟧`

is the homotopy class of a degree-zero cocycle of `dgCategory A`, where `Φ'` is the comparison of
the homotopy category of complexes with the homotopy category of the differential graded category
of complexes and `σ_n` is its commutation with the translation. That hypothesis is discharged
here, for the `f` that [Tag 09LC] produces — the image `q(g)` of a chain map `g : K ⟶ Y[n]`
composed with the quotient functor's own commutation, which is the shape
`CochainComplex.homologyHomAddEquiv_quotient_obj_apply_mk` delivers.

## Why no heterogeneous equality appears

`CochainComplex.homotopyCategoryEquivalence_map` is an `HEq`, and unfolding it is what would drag
a transport through the computation. It is not unfolded. Instead `Φ'` is read through
`CochainComplex.quotientCompComparisonIso`, the identification of `q ⋙ Φ'` with
`CochainComplex.cochainToComplexFunctor ⋙ DGCategory.compToK` that
`CategoryTheory.Quotient.lift.isLift` provides — whose components are *identities*, and which is
compatible with the two translations by
`CochainComplex.quotientCompComparisonIso_natTrans_commShift`. So
`CategoryTheory.conj_map_comp_commShiftIso` applies verbatim, and with both of its conjugating
components the identity it says precisely that `Φ'(q(g)) ≫ σ_n` is the image of `g` under the
*other* composite — in which no equivalence and no quotient occurs, only the closed degree-zero
cochain of a chain map and the homotopy class of it.

That composite is then the class of a single cocycle: the degree-zero cocycle of `g` composed with
the comparison of the differential graded shift with Mathlib's shift.

## Main results

* `CochainComplex.map_comp_commShiftIso_eq`: **the seam, crossed** — `Φ'(q(g)) ≫ σ_n` is the
  image of `g` under `cochainToComplexFunctor ⋙ compToK`, composed with that functor's own
  commutation with the translation.
* `CochainComplex.map_comp_commShiftIso_mk`: **the same as the class of one cocycle**, which is
  the form the hypothesis `hf` of `CochainComplex.coreRHS_mk` asks for.

## Implementation notes

The instance `CategoryTheory.NatTrans.CommShift` that
`CategoryTheory.conj_map_comp_commShiftIso` demands is registered in the repository for
`CochainComplex.homotopyCategoryComparisonFunctor`, and the class's type *depends on* the
`CategoryTheory.Functor.CommShift` instances of its source and target. The instance on
`(CochainComplex.homotopyCategoryEquivalence A).functor` is `inferInstanceAs` of the comparison
functor's, hence the same value by a different path, and typeclass synthesis is syntactic: asking
for the transformation's compatibility at the equivalence's functor times out. So the
computation is performed at `CochainComplex.homotopyCategoryComparisonFunctor` and transferred to
the equivalence's functor by `CochainComplex.homotopyCategoryEquivalence_functor`, which is `rfl`.

Three `rw`s that the shape of the goal suggests cannot be used: `CategoryTheory.Functor.map_id`
does not match `F.map (𝟙 X)` here, and `CategoryTheory.Category.comp_id` does not match
`a ≫ b ≫ 𝟙`, for the transparency reason recorded in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomCoreRHS.lean`. Both are performed by
`CategoryTheory.id_comp_comp_endo` and `CategoryTheory.comp_comp_id`, in which every object is a
variable and which are applied by `exact`. No option is set and nothing is made reducible.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose step 3 the
  equation belongs to; [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), which produces the
  morphism `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex

universe u

/-- `𝟙 ≫ a ≫ b ≫ u = a ≫ b` for a `u` that is the identity. Every object is a variable. -/
private theorem CategoryTheory.id_comp_comp_endo {D : Type*} [Category D] {X Y Z : D}
    (a : X ⟶ Y) (b : Y ⟶ Z) {u : Z ⟶ Z} (hu : u = 𝟙 Z) :
    𝟙 X ≫ a ≫ b ≫ u = a ≫ b := by
  rw [hu, Category.comp_id, Category.id_comp]

/-- `a ≫ b ≫ 𝟙 = a ≫ b`, every object a variable. -/
private theorem CategoryTheory.comp_comp_id {D : Type*} [Category D] {X Y Z : D} (a : X ⟶ Y)
    (b : Y ⟶ Z) : a ≫ b ≫ 𝟙 Z = a ≫ b := by
  rw [Category.comp_id]

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Preadditive A] (K : CochainComplex A ℤ)

/-- **The comparison of the homotopy categories, crossed on the image of a chain map, for the
comparison functor.** -/
private theorem map_comp_commShiftIso_comparison (n : ℤ) (Y : CochainComplex A ℤ)
    (g : K ⟶ (CategoryTheory.shiftFunctor (CochainComplex A ℤ) n).obj Y) :
    (homotopyCategoryComparisonFunctor A).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g ≫
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso
              (A := ℤ) n).hom.app Y) ≫
        ((homotopyCategoryComparisonFunctor A).commShiftIso n).hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y) =
      (cochainToComplexFunctor A ⋙ DGCategory.compToK (dgCategory A)).map g ≫
        ((cochainToComplexFunctor A ⋙ DGCategory.compToK (dgCategory A)).commShiftIso
          n).hom.app Y := by
  have h := CategoryTheory.conj_map_comp_commShiftIso
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (cochainToComplexFunctor A ⋙ DGCategory.compToK (dgCategory A))
    (homotopyCategoryComparisonFunctor A) (quotientCompComparisonIso A) K Y n g
  rw [show (quotientCompComparisonIso A).inv.app K = 𝟙 _ from rfl,
    show (quotientCompComparisonIso A).hom.app Y = 𝟙 _ from rfl] at h
  refine Eq.trans (Eq.symm (CategoryTheory.id_comp_comp_endo _ _ ?_)) h
  exact CategoryTheory.Functor.map_id _ _

/-- **The seam, crossed.** -/
theorem map_comp_commShiftIso_eq (n : ℤ) (Y : CochainComplex A ℤ)
    (g : K ⟶ (CategoryTheory.shiftFunctor (CochainComplex A ℤ) n).obj Y) :
    (homotopyCategoryEquivalence A).functor.map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g ≫
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso
              (A := ℤ) n).hom.app Y) ≫
        ((homotopyCategoryEquivalence A).functor.commShiftIso n).hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y) =
      (cochainToComplexFunctor A ⋙ DGCategory.compToK (dgCategory A)).map g ≫
        ((cochainToComplexFunctor A ⋙ DGCategory.compToK (dgCategory A)).commShiftIso
          n).hom.app Y :=
  map_comp_commShiftIso_comparison A K n Y g

/-- **The seam, crossed, as the class of a single cocycle.** -/
theorem map_comp_commShiftIso_mk (n : ℤ) (Y : CochainComplex A ℤ)
    (g : K ⟶ (CategoryTheory.shiftFunctor (CochainComplex A ℤ) n).obj Y) :
    (homotopyCategoryEquivalence A).functor.map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g ≫
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso
              (A := ℤ) n).hom.app Y) ≫
        ((homotopyCategoryEquivalence A).functor.commShiftIso n).hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y) =
      Quotient.mk _ ((dgCategory A).compCocycle
        (((cochainToComplexFunctor A).commShiftIso n).hom.app Y)
        ((cochainToComplexFunctor A).map g)) := by
  refine (map_comp_commShiftIso_eq A K n Y g).trans ?_
  rw [CategoryTheory.Functor.commShiftIso_comp_hom_app,
    show ((DGCategory.compToK (dgCategory A)).commShiftIso n).hom.app
      ((cochainToComplexFunctor A).obj Y) = 𝟙 _ from rfl]
  exact (CategoryTheory.comp_comp_id _ _).trans rfl

end CochainComplex

end
