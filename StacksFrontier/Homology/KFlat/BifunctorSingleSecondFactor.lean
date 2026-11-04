module

public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-!
# A bifunctor against a second factor concentrated in degree zero

Let `F : A ⥤ B ⥤ D` be a bifunctor, additive in each variable, between abelian categories, and
let `K` be a cochain complex of objects of `A`. Applying `F` to `K` and to an object `M` of `B`
placed in degree `0` gives a double complex concentrated in the row `0`, so its total complex
is the termwise complex `p ↦ F(K^p, M)`, which is
`CochainComplex.KFlatBifunctor.rowComplex F K M`. This file records that identification and the
support bound it gives: `Tot(F(K, M[0]))` has no cohomology in a degree where `K` vanishes.

The statements are about an arbitrary bifunctor between abelian categories, so they serve the
tensor product of sheaves of modules on a ringed space and on a ringed site alike.

## Main definitions

* `CochainComplex.KFlatBifunctor.totalSingleIso`: `Tot(F(K, M[0])) ≅ (p ↦ F(K^p, M))`.

## Main results

* `CochainComplex.KFlatBifunctor.isZero_obj_obj_of_isZero`: an additive bifunctor kills a zero
  object in its first variable.
* `CochainComplex.KFlatBifunctor.isZero_homology_mapBifunctor_single`: the support bound on the
  total complex.

## Implementation notes

The double complex attached to `K` and `M[0]` is concentrated in the row `0`, where it is the
termwise complex, by the single-row comparison
`CochainComplex.KFlatBifunctor.mapBifunctorSingleIso`; the total complex of a double complex
concentrated in the row `0` is the shift by `-0` of that row, by
`StacksDraft.TotalSingleRow.totalSingleRowUnit`; and that shift is undone by
`CategoryTheory.shiftFunctorZero'`. No comparison of the degree-`n` term of a total complex with
a value of the bifunctor is built by hand.

The `IsIso` of `totalSingleRowUnit` is passed positionally to `asIso`, because an instance
supplied by `letI` is not seated for a term-mode application and the search does not terminate.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive]

omit [Abelian B] in
/-- **An additive bifunctor kills a zero object in its first variable.** `F(0, -)` is the zero
functor, because `𝟙 (F(0)) = F(𝟙 0) = F(0) = 0`, and the zero natural transformation has zero
components. -/
theorem isZero_obj_obj_of_isZero {Z : A} (hZ : IsZero Z) (M : B) :
    IsZero ((F.obj Z).obj M) := by
  have hFZ : IsZero (F.obj Z) := by
    rw [IsZero.iff_id_eq_zero, ← F.map_id, hZ.eq_of_src (𝟙 Z) 0, F.map_zero]
  rw [IsZero.iff_id_eq_zero]
  exact NatTrans.congr_app ((IsZero.iff_id_eq_zero _).1 hFZ) M

variable [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- **A second factor concentrated in degree zero makes the total complex the termwise one.**
`Tot(F(K, M[0]))` is the complex `p ↦ F(K^p, M)`. -/
def totalSingleIso (K : CochainComplex A ℤ) (M : B) :
    HomologicalComplex.mapBifunctor K
        ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ) ≅
      rowComplex F K M :=
  let e := mapBifunctorSingleIso F K M 0
  let _hT : (StacksDraft.TotalSingleRow.singleRow
      (rowComplex F K M) 0).HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso e _
  HomologicalComplex₂.total.mapIso e (ComplexShape.up ℤ) ≪≫
    (@asIso _ _ _ _ (StacksDraft.TotalSingleRow.totalSingleRowUnit
        (rowComplex F K M) 0)
      (StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit
        (rowComplex F K M) 0)).symm ≪≫
    (CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ) neg_zero).app
      (rowComplex F K M)

/-- **The degreewise description of `totalSingleIso`.**  In degree `n` its inverse is the
inclusion of the single summand indexed by `(n, 0)` — the only one that can be nonzero —
preceded by the identification of `M` with the degree-zero term of `M[0]`.  There is no sign:
the sign `(-1)^{qn}` of `StacksDraft.TotalSingleRow.totalSingleRowUnit` is trivial in the row
`q = 0` that this comparison uses.

This is the mirror, for a second factor concentrated in degree zero, of
`HomologicalComplex.singleLeftXIso_inv` for a first factor concentrated in degree zero. -/
theorem totalSingleIso_inv_f (K : CochainComplex A ℤ) (M : B) (n : ℤ) :
    (totalSingleIso F K M).inv.f n =
      (F.obj (K.X n)).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
        HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
          n 0 n (by dsimp; omega) := by
  let : (StacksDraft.TotalSingleRow.singleRow (rowComplex F K M) 0).HasTotal
      (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (mapBifunctorSingleIso F K M 0) _
  have h1 : ∀ p : ℤ,
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            ((F.obj (K.X p)).obj M)).inv ≫
          ((HomologicalComplex.singleMapHomologicalComplex (F.obj (K.X p))
            (ComplexShape.up ℤ) 0).inv.app M).f 0 =
        (F.obj (K.X p)).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv := by
    intro p
    rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Iso.inv_hom_id_assoc]
  have hsms : ∀ (p : ℤ) {Z : D}
      (z : (F.obj (K.X p)).obj
        (((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M).X 0) ⟶ Z),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((rowComplex F K M).X p)).inv ≫
          ((mapBifunctorSingleIso F K M 0).inv.f p).f 0 ≫ z =
        (F.obj (K.X p)).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
          z := by
    intro p Z z
    have h1' : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            ((rowComplex F K M).X p)).inv ≫
          ((mapBifunctorSingleIso F K M 0).inv.f p).f 0 =
        (F.obj (K.X p)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv := h1 p
    exact (Category.assoc _ _ _).symm.trans (h1' =≫ z)
  have hgen : ∀ (m : ℤ) (hm : n = m),
      ((HomologicalComplex.XIsoOfEq (rowComplex F K M) hm).hom ≫
            ((0 * n).negOnePow • ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                ((rowComplex F K M).X m)).inv ≫
              (StacksDraft.TotalSingleRow.singleRow (rowComplex F K M) 0).ιTotal
                (ComplexShape.up ℤ) m 0 n (by dsimp; omega)))) ≫
          (HomologicalComplex₂.total.mapIso (mapBifunctorSingleIso F K M 0)
            (ComplexShape.up ℤ)).inv.f n =
        (F.obj (K.X n)).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
          HomologicalComplex.ιMapBifunctor K
            ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
            n 0 n (by dsimp; omega) := by
    rintro m rfl
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, zero_mul,
      Int.negOnePow_zero, one_smul, Category.assoc,
      HomologicalComplex₂.total.mapIso_inv, HomologicalComplex₂.ιTotal_map]
    exact hsms n _
  have hs : ((CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ) neg_zero).app
        (rowComplex F K M)).inv.f n =
      (HomologicalComplex.XIsoOfEq (rowComplex F K M)
        (show n = n + -0 by omega)).hom := by
    simp [CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f]
  have h0 : (totalSingleIso F K M).inv.f n =
      (((CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ) neg_zero).app
              (rowComplex F K M)).inv.f n ≫
            ((0 * n).negOnePow • ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                ((rowComplex F K M).X (n + -0))).inv ≫
              (StacksDraft.TotalSingleRow.singleRow (rowComplex F K M) 0).ιTotal
                (ComplexShape.up ℤ) (n + -0) 0 n (by dsimp; omega)))) ≫
        (HomologicalComplex₂.total.mapIso (mapBifunctorSingleIso F K M 0)
          (ComplexShape.up ℤ)).inv.f n := rfl
  rw [h0, hs]
  exact hgen (n + -0) (by omega)

/-- **The degreewise description of `totalSingleIso` read forwards**: on the single summand
indexed by `(n, 0)` the comparison is the identification of the degree-zero term of `M[0]` with
`M`.  Together with `HomologicalComplex₂.total.hom_ext` this determines
`(totalSingleIso F K M).hom` in each degree, the other summands of degree `n` being zero. -/
@[reassoc]
theorem ι_totalSingleIso_hom_f (K : CochainComplex A ℤ) (M : B) (n : ℤ) :
    HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
          n 0 n (by dsimp; omega) ≫ (totalSingleIso F K M).hom.f n =
      (F.obj (K.X n)).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom := by
  have h0 : (totalSingleIso F K M).inv.f n ≫ (totalSingleIso F K M).hom.f n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  have hid : ((F.obj (K.X n)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
        HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
          n 0 n (by dsimp; omega)) ≫ (totalSingleIso F K M).hom.f n = 𝟙 _ :=
    (totalSingleIso_inv_f F K M n =≫ (totalSingleIso F K M).hom.f n).symm.trans h0
  have h2 : ((F.obj (K.X n)).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)).inv ≫
        (HomologicalComplex.ιMapBifunctor K
            ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
            n 0 n (by dsimp; omega) ≫ (totalSingleIso F K M).hom.f n) = 𝟙 _ :=
    (Category.assoc _ _ _).symm.trans hid
  exact ((Iso.inv_comp_eq _).mp h2).trans (Category.comp_id _)

/-- **The support bound on a total complex.** If the degree-`i` term of `K` is a zero object
then `Tot(F(K, M[0]))` has no cohomology in degree `i`. The total complex is the termwise
complex `p ↦ F(K^p, M)` by `totalSingleIso`, whose degree-`i` term is `F(K^i, M)`, a zero
object by `isZero_obj_obj_of_isZero`. -/
theorem isZero_homology_mapBifunctor_single (K : CochainComplex A ℤ) (M : B) (i : ℤ)
    (hK : IsZero (K.X i)) :
    IsZero ((HomologicalComplex.mapBifunctor K
      ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F
      (ComplexShape.up ℤ)).homology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((isZero_obj_obj_of_isZero F hK M).of_iso
      ((HomologicalComplex.eval D (ComplexShape.up ℤ) i).mapIso (totalSingleIso F K M)))

end CochainComplex.KFlatBifunctor

end
