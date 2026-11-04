module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexGeneral
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexAlgebra

/-!
# Finiteness and boundedness of the total complex of a cosimplicial double complex

Let `K : CochainComplex (CosimplicialObject (ModuleCat R)) ℕ` be a cochain complex of cosimplicial
modules over a Noetherian ring `R`, and `Tot` the total complex of its double complex
`Crystalline.CosimplicialDoubleComplex.functor` (columns: the Moore complexes of the `K^a`).
If `K^a = 0` for `a > D` and the cohomology of every column is a finite `R`-module, then so is the
cohomology of `Tot` in every degree; if moreover the columns are exact above degree `m`, the
cohomology of `Tot` vanishes above degree `D + m`.  These are the first spectral sequence of the
total complex (`Stacks.DeRhamDirectImage.weakSerre_homology_total`) and the truncation argument
`AlgebraicGeometry.DeRhamTypeComplex.isZero_homology_total_of_exactAt`, read through the
identification of the columns with the extended Moore complexes.

## Main results

* `Crystalline.CosimplicialDoubleComplex.moduleFinite_homology_total`
* `Crystalline.CosimplicialDoubleComplex.isZero_homology_total_of_bounded`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ComplexShape

universe v u

namespace Crystalline.CosimplicialDoubleComplex

variable {R : Type u} [CommRing R] (K : CochainComplex (CosimplicialObject (ModuleCat.{v} R)) ℕ)

/-- The column `a` of the double complex vanishes when `K^a` does. -/
theorem isZero_X_of_isZero {a : ℕ} (h : IsZero (K.X a)) :
    IsZero (((functor (ModuleCat.{v} R)).obj K).X (a : ℤ)) :=
  IsZero.of_iso ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R)).map_isZero
    ((alternatingCofaceMapComplex (ModuleCat.{v} R)).map_isZero h)) (columnIso K a)

/-- The cohomology of the column `a` of the double complex in a nonnegative degree is that of the
Moore complex of `K^a`. -/
def columnHomologyIso (a j : ℕ) :
    (((functor (ModuleCat.{v} R)).obj K).X (a : ℤ)).homology (j : ℤ) ≅
      ((alternatingCofaceMapComplex (ModuleCat.{v} R)).obj (K.X a)).homology j :=
  ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (j : ℤ)).mapIso
      (columnIso K a)).trans
    (((alternatingCofaceMapComplex (ModuleCat.{v} R)).obj (K.X a)).extendHomologyIso
      ComplexShape.embeddingUpNat (j := j) (j' := (j : ℤ)) rfl)

/-- The columns of the double complex vanish in negative degrees, hence so does their
cohomology. -/
theorem isZero_column_homology_of_neg (p : ℤ) {q : ℤ} (hq : q < 0) :
    IsZero ((((functor (ModuleCat.{v} R)).obj K).X p).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_X_X_of_neg K p hq)

/-- The cohomology of the column `p` of the double complex vanishes when `p` is negative. -/
private theorem isZero_column_homology_of_neg_fst {p : ℤ} (hp : p < 0) (q : ℤ) :
    IsZero ((((functor (ModuleCat.{v} R)).obj K).X p).homology q) :=
  Functor.map_isZero (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q)
    (isZero_X_of_neg K hp)

/-- The double complex vanishes off the first quadrant, so it has finite diagonals. -/
theorem finite_diagonal (D : ℕ) (hD : ∀ a, D < a → IsZero (K.X a)) (n : ℤ) :
    {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero ((((functor (ModuleCat.{v} R)).obj K).X pq.1).X pq.2)}.Finite := by
  refine ((Set.finite_Icc (0 : ℤ) D).image fun p ↦ (p, n - p)).subset ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  simp only at hpq
  refine ⟨p, ⟨?_, ?_⟩, by simp only [Prod.mk.injEq, true_and]; omega⟩
  · by_contra hp
    exact hz (Functor.map_isZero (HomologicalComplex.eval _ _ q)
      (isZero_X_of_neg K (by omega)))
  · by_contra hp
    lift p to ℕ using (by omega)
    exact hz (Functor.map_isZero (HomologicalComplex.eval _ _ q)
      (isZero_X_of_isZero K (hD p (by omega))))

/-- **The cohomology of the total complex is finite** when `K^a = 0` for `a > D` and the
cohomology of the Moore complex of every `K^a` is a finite `R`-module, `R` Noetherian. -/
theorem moduleFinite_homology_total [IsNoetherianRing R] (D : ℕ)
    (hD : ∀ a, D < a → IsZero (K.X a))
    (hfin : ∀ a j : ℕ,
      Module.Finite R (((alternatingCofaceMapComplex (ModuleCat.{v} R)).obj (K.X a)).homology j))
    (n : ℤ) :
    Module.Finite R
      ((((functor (ModuleCat.{v} R)).obj K).total (ComplexShape.up ℤ)).homology n) := by
  let P := AlgebraicGeometry.DeRhamTypeComplex.moduleFinite.{v} R
  refine Stacks.DeRhamDirectImage.weakSerre_homology_total _ (finite_diagonal K D hD) P
    (fun p q ↦ ?_) n
  by_cases hq : q < 0
  · exact P.prop_of_isZero (isZero_column_homology_of_neg K p hq)
  by_cases hp : 0 ≤ p
  · lift p to ℕ using (by omega)
    lift q to ℕ using (by omega)
    exact P.prop_of_iso (columnHomologyIso K p q).symm (hfin p q)
  · exact P.prop_of_isZero (isZero_column_homology_of_neg_fst K (by omega) q)

/-- **The cohomology of the total complex vanishes above `D + m`** when `K^a = 0` for `a > D` and
the Moore complex of every `K^a` is exact in degrees `> m`. -/
theorem isZero_homology_total_of_bounded (D m : ℕ) (hD : ∀ a, D < a → IsZero (K.X a))
    (hex : ∀ a j : ℕ, m < j →
      IsZero (((alternatingCofaceMapComplex (ModuleCat.{v} R)).obj (K.X a)).homology j))
    (n : ℤ) (hn : (D : ℤ) + m < n) :
    IsZero ((((functor (ModuleCat.{v} R)).obj K).total (ComplexShape.up ℤ)).homology n) := by
  refine AlgebraicGeometry.DeRhamTypeComplex.isZero_homology_total_of_exactAt _ 0 D m
    (fun p hp ↦ isZero_X_of_neg K hp) (fun p hp ↦ ?_) (fun p q hq ↦ isZero_X_X_of_neg K p hq)
    (fun p q hq ↦ ?_) n hn
  · lift p to ℕ using (by omega)
    exact isZero_X_of_isZero K (hD p (by omega))
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    by_cases hp : 0 ≤ p
    · lift p to ℕ using (by omega)
      lift q to ℕ using (by omega)
      exact IsZero.of_iso (hex p q (by omega)) (columnHomologyIso K p q)
    · exact isZero_column_homology_of_neg_fst K (by omega) q

end Crystalline.CosimplicialDoubleComplex
