module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality

/-!
# Total complexes against a module placed in an arbitrary degree

Let `F : A ⥤ B ⥤ D` be a bifunctor of abelian categories, additive in each variable, and let
`M` be an object of `B`.  For a morphism of cochain complexes `φ : K ⟶ L` in `A`, the map of
total complexes `Tot(F(φ, M[j]))` is a quasi-isomorphism as soon as the map of row complexes
`F(φ, M)` is.  The case `j = 0` is the identification of the total complex with the row complex;
the general case is reduced to it through the shift of the second factor, whose comparison
isomorphism with the shift of the total complex is natural in the first factor.

## Main results

* `Stacks.TotalSingleShift.mapBifunctorShift₂Iso_hom_naturality_left`: the comparison
  `Tot(F(K, M⟦y⟧)) ≅ Tot(F(K, M))⟦y⟧` is natural in `K`.
* `Stacks.TotalSingleShift.quasiIso_mapBifunctorMap_single_of_rowQuasiIso`: the statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.TotalSingleShift

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- The comparison of the total complex against a shifted second factor with the shifted total
complex is natural in the first factor. -/
@[reassoc]
theorem mapBifunctorShift₂Iso_hom_naturality_left {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    (M : CochainComplex B ℤ) (y : ℤ) :
    HomologicalComplex.mapBifunctorMap φ (𝟙 (M⟦y⟧)) F (ComplexShape.up ℤ) ≫
        (CochainComplex.mapBifunctorShift₂Iso L M F y).hom =
      (CochainComplex.mapBifunctorShift₂Iso K M F y).hom ≫
        (HomologicalComplex.mapBifunctorMap φ (𝟙 M) F (ComplexShape.up ℤ))⟦y⟧' := by
  ext n p q h
  simp [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl,
    CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl]

/-- Being a quasi-isomorphism on total complexes transfers along an iso in the second factor. -/
private theorem quasiIso_mapBifunctorMap_of_iso {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    {X Y : CochainComplex B ℤ} (e : X ≅ Y)
    (h : QuasiIso (HomologicalComplex.mapBifunctorMap φ (𝟙 X) F (ComplexShape.up ℤ))) :
    QuasiIso (HomologicalComplex.mapBifunctorMap φ (𝟙 Y) F (ComplexShape.up ℤ)) := by
  have hsq := ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).map φ).naturality e.hom
  have hL : QuasiIso (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K).map e.hom ≫ ((F.map₂HomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map φ).app Y) := by
    rw [hsq]
    have : QuasiIso (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).map φ).app X) := h
    have : QuasiIso (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj L).map e.hom) := quasiIso_of_isIso _
    infer_instance
  have : QuasiIso (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K).map e.hom) := quasiIso_of_isIso _
  exact (quasiIso_iff_comp_left (((F.map₂HomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map e.hom) _).1 hL

/-- **A quasi-isomorphism of row complexes gives one of total complexes against `M[j]`.** -/
theorem quasiIso_mapBifunctorMap_single_of_rowQuasiIso {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    (M : B) (j : ℤ) (hrow : QuasiIso (CochainComplex.KFlatBifunctor.rowComplexMap F φ M)) :
    QuasiIso (HomologicalComplex.mapBifunctorMap φ
      (𝟙 ((HomologicalComplex.single B (ComplexShape.up ℤ) j).obj M)) F (ComplexShape.up ℤ)) := by
  have h0 : QuasiIso (HomologicalComplex.mapBifunctorMap φ
      (𝟙 ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M)) F (ComplexShape.up ℤ)) := by
    have h := CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality F φ M
    have h2 : QuasiIso (HomologicalComplex.mapBifunctorMap φ
        (𝟙 ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M)) F (ComplexShape.up ℤ) ≫
        (CochainComplex.KFlatBifunctor.totalSingleIso F L M).hom) := by
      rw [h]; infer_instance
    exact (quasiIso_iff_comp_right _ _).1 h2
  have h1 : QuasiIso (HomologicalComplex.mapBifunctorMap φ
      (𝟙 (((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M)⟦-j⟧)) F
        (ComplexShape.up ℤ)) := by
    have h := mapBifunctorShift₂Iso_hom_naturality_left F φ
      ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) (-j)
    have : QuasiIso ((HomologicalComplex.mapBifunctorMap φ
        (𝟙 ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M)) F
          (ComplexShape.up ℤ))⟦-j⟧') := (CochainComplex.quasiIso_shift_iff _ _).2 h0
    have h2 : QuasiIso (HomologicalComplex.mapBifunctorMap φ
        (𝟙 (((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M)⟦-j⟧)) F
          (ComplexShape.up ℤ) ≫
        (CochainComplex.mapBifunctorShift₂Iso L
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (-j)).hom) := by
      rw [h]; infer_instance
    exact (quasiIso_iff_comp_right _ _).1 h2
  exact quasiIso_mapBifunctorMap_of_iso F φ
    (((CochainComplex.singleFunctors B).shiftIso (-j) j 0 (by omega)).app M) h1

/-- **The same against any complex isomorphic to `M[j]`.** -/
theorem quasiIso_mapBifunctorMap_of_iso_single {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    (N : CochainComplex B ℤ) (M : B) (j : ℤ)
    (e : N ≅ (HomologicalComplex.single B (ComplexShape.up ℤ) j).obj M)
    (hrow : QuasiIso (CochainComplex.KFlatBifunctor.rowComplexMap F φ M)) :
    QuasiIso (HomologicalComplex.mapBifunctorMap φ (𝟙 N) F (ComplexShape.up ℤ)) := by
  exact quasiIso_mapBifunctorMap_of_iso F φ e.symm
    (quasiIso_mapBifunctorMap_single_of_rowQuasiIso F φ M j hrow)

end Stacks.TotalSingleShift

end
