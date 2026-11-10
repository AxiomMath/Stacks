module

public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor

/-!
# A bifunctor against a second factor concentrated in an arbitrary degree

Let `F : A ⥤ B ⥤ D` be a bifunctor, additive in each variable, between abelian categories, let
`K` be a cochain complex of objects of `A` and let `M` be an object of `B` placed in the degree
`q`.  The resulting double complex is concentrated in the row `q`, where it is the termwise
complex `p ↦ F(K^p, M)`, so its total complex is the shift by `-q` of that termwise complex.
This module records that identification together with its value on the one summand of each total
degree that does not vanish.

For `q = 0` the shift disappears and the identification is
`CochainComplex.KFlatBifunctor.totalSingleIso`; this module is the same statement for an
arbitrary `q`, which is what the dévissage of [Stacks, Tag 0944] needs in order to compare
`Tot(K ⊗_𝒪 𝒪[q])` with `K⟦-q⟧` rather than with `K`.

## Main definitions

* `CochainComplex.KFlatBifunctor.totalSingleShiftIso`: `Tot(F(K, M[q])) ≅ (p ↦ F(K^p, M))⟦-q⟧`.

## Main results

* `CochainComplex.KFlatBifunctor.totalSingleShiftIso_inv_f`: the inverse of the identification in
  a single degree.  It lands in the summand of bidegree `(n - q, q)`, the only one of total
  degree `n` that does not vanish, and carries the sign `(-1)^{qn}`.
* `CochainComplex.KFlatBifunctor.ι_totalSingleShiftIso_hom`: the identification itself on that
  summand.

## Implementation notes

**The sign.**  `StacksDraft.TotalSingleRow.totalSingleRowUnit` carries the sign `(-1)^{qn}` in
degree `n`, because the differential of a total complex concentrated in one row is that of the
row with no sign while the differential of a shift by `-q` carries `(-1)^q`; see the
implementation notes of `StacksFrontier/Algebra/Homology/TotalSingleRow.lean`.  That sign therefore
appears in both statements below.  It is harmless downstream: a coherence between two such
identifications in the same degree and the same `q` carries it on both sides, where
`Int.units_mul_self` cancels it.

**The index of the nonvanishing summand is written out.**  Both statements name the first index
of that summand as `n + -q`, which is the spelling the degree-`n` term of a shift by `-q` carries
on the nose (`CochainComplex.shiftFunctor_obj_X'`).  Taking it as a separate variable together
with the equation it satisfies, as `DerivedPullbackTensorRightUnitor.lean` (in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/`) does for the comparison of a
single row, is not possible here: the source of the identification
is the degree-`n` term of that shift, so a variable index makes the statement ill-typed.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

open StacksDraft.TotalSingleRow

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- **A second factor concentrated in the degree `q` makes the total complex a shift of the
termwise one.**  `Tot(F(K, M[q]))` is `(p ↦ F(K^p, M))⟦-q⟧`. -/
def totalSingleShiftIso (K : CochainComplex A ℤ) (M : B) (q : ℤ) :
    HomologicalComplex.mapBifunctor K
        ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M) F (ComplexShape.up ℤ) ≅
      (CategoryTheory.shiftFunctor (CochainComplex D ℤ) (-q)).obj (rowComplex F K M) :=
  letI e := mapBifunctorSingleIso F K M q
  letI _hT : (singleRow (rowComplex F K M) q).HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso e _
  HomologicalComplex₂.total.mapIso e (ComplexShape.up ℤ) ≪≫
    (@asIso _ _ _ _ (totalSingleRowUnit (rowComplex F K M) q)
      (isIso_totalSingleRowUnit (rowComplex F K M) q)).symm

/-- **The inverse of the identification `Tot(F(K, M[q])) ≅ (p ↦ F(K^p, M))⟦-q⟧` in a single
degree**: it lands in the one summand of total degree `n` that does not vanish, namely the one
of bidegree `(n - q, q)`, and carries the sign `(-1)^{qn}`. -/
lemma totalSingleShiftIso_inv_f (K : CochainComplex A ℤ) (M : B) (q n : ℤ) :
    (totalSingleShiftIso F K M q).inv.f n =
      (q * n).negOnePow •
        ((F.obj (K.X (n + -q))).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q M).inv ≫
          HomologicalComplex.ιMapBifunctor K
            ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M) F (ComplexShape.up ℤ)
            (n + -q) q n (by dsimp; omega)) := by
  have hT : (singleRow (rowComplex F K M) q).HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (mapBifunctorSingleIso F K M q) _
  have hI : IsIso (totalSingleRowUnit (rowComplex F K M) q) :=
    isIso_totalSingleRowUnit (rowComplex F K M) q
  have h1 : (totalSingleShiftIso F K M q).inv.f n =
      (totalSingleRowUnit (rowComplex F K M) q).f n ≫
        (HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M q).inv
          (ComplexShape.up ℤ)).f n := rfl
  have h2 : (totalSingleRowUnit (rowComplex F K M) q).f n =
      (q * n).negOnePow •
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
              ((rowComplex F K M).X (n + -q))).inv ≫
          (singleRow (rowComplex F K M) q).ιTotal (ComplexShape.up ℤ) (n + -q) q n
            (by dsimp; omega)) := rfl
  have h3 : (singleRow (rowComplex F K M) q).ιTotal (ComplexShape.up ℤ) (n + -q) q n
          (by dsimp; omega) ≫
        (HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M q).inv
          (ComplexShape.up ℤ)).f n =
      (((mapBifunctorSingleIso F K M q).inv.f (n + -q)).f q) ≫
        HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M) F (ComplexShape.up ℤ)
          (n + -q) q n (by dsimp; omega) := by
    rw [HomologicalComplex₂.ιTotal_map]
  have h4 : ((mapBifunctorSingleIso F K M q).inv.f (n + -q)).f q =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
          ((rowComplex F K M).X (n + -q))).hom ≫
        (F.obj (K.X (n + -q))).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q M).inv :=
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self (F.obj (K.X (n + -q)))
      (ComplexShape.up ℤ) q M
  rw [h1, h2, Linear.units_smul_comp]
  refine congrArg (fun z => (q * n).negOnePow • z) ?_
  rw [Category.assoc, h3, h4]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- **The identification `Tot(F(K, M[q])) ≅ (p ↦ F(K^p, M))⟦-q⟧` on the one summand of total
degree `n` that does not vanish**: on the summand of bidegree `(n - q, q)` it is the
identification of the degree-`q` term of `M[q]` with `M`, scaled by `(-1)^{qn}`. -/
lemma ι_totalSingleShiftIso_hom (K : CochainComplex A ℤ) (M : B) (q n : ℤ) :
    HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M) F (ComplexShape.up ℤ)
          (n + -q) q n (by dsimp; omega) ≫
        (totalSingleShiftIso F K M q).hom.f n =
      (q * n).negOnePow •
        (F.obj (K.X (n + -q))).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q M).hom := by
  have key : ((q * n).negOnePow •
        (F.obj (K.X (n + -q))).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q M).hom) ≫
        (totalSingleShiftIso F K M q).inv.f n =
      HomologicalComplex.ιMapBifunctor K
        ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M) F (ComplexShape.up ℤ)
        (n + -q) q n (by dsimp; omega) := by
    rw [totalSingleShiftIso_inv_f, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
      Int.units_mul_self, one_smul, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id]
    simp
  have : IsIso ((totalSingleShiftIso F K M q).inv.f n) :=
    ((HomologicalComplex.eval D (ComplexShape.up ℤ) n).mapIso
      (totalSingleShiftIso F K M q)).isIso_inv
  refine (cancel_mono ((totalSingleShiftIso F K M q).inv.f n)).1 (Eq.trans ?_ key.symm)
  rw [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.id_f, Category.comp_id]

end CochainComplex.KFlatBifunctor

end
