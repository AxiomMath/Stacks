module

public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.ChartMatrix
public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Smooth
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.AlgebraicGeometry.ChartDictionary.Basic

/-!
# The Plücker morphism of the Grassmannian

A point of `G(k, n)` is a quotient `𝒪^n ⟶ 𝒬` of rank `m = n - k`. On the chart attached to an
embedding `ι : Fin m ↪ Fin n` the quotient is the matrix `chartMatrix ι x` of the chart, and its
*Plücker coordinates* are the maximal minors: for every embedding `λ : Fin m ↪ Fin n` the
determinant of the square submatrix on the columns `λ`. The minor at `λ = ι` is `1`, so the
minors span the unit ideal and define a morphism from the chart to projective space. Two charts
agreeing on a scheme have matrices differing by an invertible matrix on the left
(`AlgebraicGeometry.Grassmannian.exists_isUnit_det_chartMatrix_eq_mul`), so their minors differ
by the unit `det E`, and the chart morphisms glue to the **Plücker morphism**
`G(k, n) ⟶ ℙᴺ_ℤ`.

The projective space is indexed by *all* embeddings `Fin m ↪ Fin n`, not only the increasing
ones; the coordinates indexed by two embeddings with the same range agree up to a sign. This
costs nothing and saves the bookkeeping of ordered subsets.

## Main definitions

* `AlgebraicGeometry.Grassmannian.plucker`: the maximal minor of a matrix on the columns `λ`.
* `AlgebraicGeometry.Grassmannian.pluckerIndexEquiv`: the indexing of the coordinates of
  projective space by embeddings.
* `AlgebraicGeometry.Grassmannian.chartPluckerMap`: the Plücker morphism of a chart.
* `AlgebraicGeometry.Grassmannian.pluckerMap`: the Plücker morphism `G(k, n) ⟶ ℙᴺ_ℤ`.

## Main results

* `AlgebraicGeometry.Grassmannian.chart_comp_pluckerMap`: on each chart the Plücker morphism is
  the chart's.

## References

* [Stacks Project, Tag 089T](https://stacks.math.columbia.edu/tag/089T)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SectionsToProjectiveSpace Stacks.ProjGlobalSectionsAppTop

universe u

namespace AlgebraicGeometry.Grassmannian

/-! ### Maximal minors -/

section Minors

variable {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}

/-- **The maximal minor of an `m × n` matrix on the columns `λ`.** -/
def plucker (M : Matrix (Fin m) (Fin n) R) (c : Fin m ↪ Fin n) : R :=
  (M.submatrix id c).det

/-- Multiplying on the left by `E` multiplies every maximal minor by `det E`. -/
theorem plucker_mul (E : Matrix (Fin m) (Fin m) R) (M : Matrix (Fin m) (Fin n) R)
    (c : Fin m ↪ Fin n) : plucker (E * M) c = E.det * plucker M c := by
  rw [plucker, plucker, ← Matrix.det_mul]
  congr 1

/-- A ring homomorphism commutes with maximal minors. -/
theorem plucker_map (φ : R →+* S) (M : Matrix (Fin m) (Fin n) R) (c : Fin m ↪ Fin n) :
    plucker (M.map φ) c = φ (plucker M c) := by
  rw [plucker, plucker, RingHom.map_det]
  rfl

/-- The determinant of the identity matrix with its `i`-th column replaced by `w` is `w i`. -/
theorem det_one_updateCol (i : Fin m) (w : Fin m → R) :
    ((1 : Matrix (Fin m) (Fin m) R).updateCol i w).det = w i := by
  have h := Matrix.updateCol_transpose (M := (1 : Matrix (Fin m) (Fin m) R)) (i := i) (b := w)
  rw [Matrix.transpose_one] at h
  rw [h, Matrix.det_transpose]
  have hw : w = ∑ k, w k • (1 : Matrix (Fin m) (Fin m) R) k := by
    funext a
    simp [Finset.sum_apply, Matrix.one_apply]
  conv_lhs => rw [hw]
  rw [Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]

end Minors

/-! ### The minors of the chart matrices -/

section ChartMinors

variable {k n : ℕ} {R : Type*} [CommRing R]

/-- The minor of the chart matrix on the chart's own columns is `1`. -/
theorem plucker_chartMatrix_self (ι : Fin (n - k) ↪ Fin n) (v : ChartIndex.{u} ι → R) :
    plucker (chartMatrix ι v) ι = 1 := by
  rw [plucker]
  convert Matrix.det_one (R := R) (n := Fin (n - k)) using 2
  funext i i'
  rw [Matrix.submatrix_apply, id, chartMatrix_apply_self, Matrix.one_apply]

/-- **The chart coordinates are minors.** Replacing `ι i` by a column `j` outside the range of
`ι` gives the minor `x_{j,i}`. -/
theorem plucker_chartMatrix_setValue (ι : Fin (n - k) ↪ Fin n) (v : ChartIndex.{u} ι → R)
    {j : Fin n} (hj : j ∉ Set.range ι) (i : Fin (n - k)) :
    plucker (chartMatrix ι v) (ι.setValue i j) = v (ULift.up (⟨j, hj⟩, i)) := by
  classical
  rw [plucker]
  have hM : (chartMatrix ι v).submatrix id (ι.setValue i j) =
      (1 : Matrix (Fin (n - k)) (Fin (n - k)) R).updateCol i
        (fun r => v (ULift.up (⟨j, hj⟩, r))) := by
    funext r c
    rw [Matrix.submatrix_apply, id, Matrix.updateCol_apply]
    by_cases hc : c = i
    · subst hc
      rw [ite_eq_left rfl]
      have : ι.setValue c j c = j := Function.Embedding.setValue_eq _ _ _
      rw [this, chartMatrix_apply_of_notMem ι v r hj]
    · rw [ite_eq_right hc]
      have hne : ι c ≠ j := fun h => hj ⟨c, h⟩
      have : ι.setValue i j c = ι c := by
        simp [Function.Embedding.setValue, hc, hne]
      rw [this, chartMatrix_apply_self, Matrix.one_apply]
  rw [hM, det_one_updateCol]

end ChartMinors

/-! ### The Plücker morphism of a chart -/

variable (k n : ℕ)

/-- The number of embeddings `Fin (n - k) ↪ Fin n` is positive. -/
theorem card_embedding_pos : 0 < Fintype.card (Fin (n - k) ↪ Fin n) :=
  Fintype.card_pos_iff.mpr ⟨Fin.castLEEmb (Nat.sub_le n k)⟩

/-- The dimension `N` of the projective space receiving the Plücker morphism: one less than the
number of embeddings `Fin (n - k) ↪ Fin n`. -/
def pluckerDim : ℕ := Fintype.card (Fin (n - k) ↪ Fin n) - 1

/-- **The indexing of the coordinates of `ℙᴺ` by the embeddings `Fin (n - k) ↪ Fin n`.** -/
def pluckerIndexEquiv : (Fin (n - k) ↪ Fin n) ≃ Fin (pluckerDim k n + 1) :=
  Fintype.equivFinOfCardEq (Nat.succ_pred_eq_of_pos (card_embedding_pos k n)).symm

variable {k n}

/-- The coordinates of a chart, as global sections. -/
def chartCoords (ι : Fin (n - k) ↪ Fin n) :
    ChartIndex.{u} ι → Γ(Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))), ⊤) :=
  AffineSpace.toSpecMvPolyIntEquiv _ (𝟙 _)

/-- **The Plücker coordinates of a scheme mapping to a chart**: the maximal minors of the
pulled back chart matrix, indexed by the coordinates of `ℙᴺ`. -/
def pluckerSections {T : Scheme.{u}} (ι : Fin (n - k) ↪ Fin n)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)))) :
    Fin (pluckerDim k n + 1) → Γ(T, ⊤) :=
  fun t => plucker (chartMatrix ι (AffineSpace.toSpecMvPolyIntEquiv _ g))
    ((pluckerIndexEquiv k n).symm t)

/-- The Plücker coordinate indexed by the chart's own embedding `ι` is `1`. -/
theorem pluckerSections_self {T : Scheme.{u}} (ι : Fin (n - k) ↪ Fin n)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)))) :
    pluckerSections ι g (pluckerIndexEquiv k n ι) = 1 := by
  rw [pluckerSections, Equiv.symm_apply_apply, plucker_chartMatrix_self]

/-- The Plücker coordinates of a scheme mapping to a chart generate the unit ideal. -/
theorem span_pluckerSections {T : Scheme.{u}} (ι : Fin (n - k) ↪ Fin n)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)))) :
    Ideal.span (Set.range (pluckerSections ι g)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _
    (Ideal.subset_span ⟨pluckerIndexEquiv k n ι, rfl⟩)
    (by rw [pluckerSections_self]; exact isUnit_one)

/-- The Plücker sections pull back. -/
theorem appTop_pluckerSections {T T' : Scheme.{u}} (ι : Fin (n - k) ↪ Fin n) (f : T' ⟶ T)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))))
    (t : Fin (pluckerDim k n + 1)) :
    f.appTop (pluckerSections ι g t) = pluckerSections ι (f ≫ g) t := by
  rw [pluckerSections, pluckerSections, ← plucker_map]
  congr 1
  rw [← chartMatrix_map]
  rfl

/-- **The Plücker morphism of a chart.** -/
def chartPluckerMap (ι : Fin (n - k) ↪ Fin n) :
    Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))) ⟶
      projectiveSpaceAtUniverse.{u} (pluckerDim k n) :=
  toProjectiveSpaceAtUniverse (pluckerSections ι (𝟙 _)) (span_pluckerSections ι (𝟙 _))

/-- A morphism into a chart followed by the chart's Plücker morphism is the morphism of the
pulled back Plücker sections. -/
theorem comp_chartPluckerMap {T : Scheme.{u}} (ι : Fin (n - k) ↪ Fin n)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)))) :
    g ≫ chartPluckerMap ι =
      toProjectiveSpaceAtUniverse (pluckerSections ι g) (span_pluckerSections ι g) := by
  have hg : Ideal.span (Set.range fun t => g.appTop (pluckerSections ι (𝟙 _) t)) = ⊤ := by
    simp_rw [appTop_pluckerSections, Category.comp_id]
    exact span_pluckerSections ι g
  rw [chartPluckerMap, hasPullbackNaturality g _ _ hg]
  exact toProjectiveSpaceAtUniverse_congr
    (funext fun t => by rw [appTop_pluckerSections, Category.comp_id]) _ _

/-- **The chart Plücker morphisms agree where two charts meet.** -/
theorem chartPluckerMap_compat {T : Scheme.{u}} {ι κ : Fin (n - k) ↪ Fin n}
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))))
    (h : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} κ) (ULift.{u} ℤ))))
    (hgh : g ≫ chart k n ι = h ≫ chart k n κ) :
    g ≫ chartPluckerMap ι = h ≫ chartPluckerMap κ := by
  obtain ⟨E, hE, hM⟩ := exists_isUnit_det_chartMatrix_eq_mul g h hgh
  rw [comp_chartPluckerMap, comp_chartPluckerMap]
  have hs : pluckerSections ι g = fun t => (hE.unit : Γ(T, ⊤)) * pluckerSections κ h t := by
    funext t
    rw [pluckerSections, hM, plucker_mul, IsUnit.unit_spec]
    rfl
  have hus : Ideal.span (Set.range fun t => (hE.unit : Γ(T, ⊤)) * pluckerSections κ h t) = ⊤ := by
    rw [span_range_unit_smul]
    exact span_pluckerSections κ h
  rw [toProjectiveSpaceAtUniverse_congr hs (span_pluckerSections ι g) hus]
  exact hasUnitInvariance hE.unit _ _ hus

variable (k n)

/-- **The Plücker morphism `G(k, n) ⟶ ℙᴺ_ℤ`**, glued from the Plücker morphisms of the charts. -/
def pluckerMap : scheme.{u} k n ⟶ projectiveSpaceAtUniverse.{u} (pluckerDim k n) :=
  (chartCover k n).glueMorphisms (fun ι => chartPluckerMap ι) fun _ _ =>
    chartPluckerMap_compat _ _ (pullback.condition)

/-- **On each chart the Plücker morphism is the chart's.** -/
theorem chart_comp_pluckerMap (ι : Fin (n - k) ↪ Fin n) :
    chart k n ι ≫ pluckerMap k n = chartPluckerMap ι :=
  (chartCover k n).ι_glueMorphisms _ _ ι

end AlgebraicGeometry.Grassmannian

end
