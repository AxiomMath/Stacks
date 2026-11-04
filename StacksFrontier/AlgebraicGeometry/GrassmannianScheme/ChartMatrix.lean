module

public import StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSheafMatrix

/-!
# The coordinate charts of the Grassmannian in matrix form

On the chart of `G(k, n)` attached to an embedding `ι : Fin (n - k) ↪ Fin n` the universal
quotient `𝒪^n ⟶ 𝒪^{n - k}` sends `e_{ι i}` to `f_i` and `e_j`, for `j` outside the range of `ι`, to
`∑_i x_{j,i} f_i`. Its matrix is `AlgebraicGeometry.Grassmannian.chartMatrix`: the `(n - k) × n`
matrix whose columns on the range of `ι` are the standard basis vectors and whose other columns
are the chart coordinates.

## Main definitions

* `AlgebraicGeometry.Grassmannian.chartMatrix`: the matrix of the quotient on a chart.

## Main results

* `AlgebraicGeometry.Grassmannian.toMatrix_chartQuotientMap`: the quotient classified by a
  morphism into a chart has the chart matrix of the pulled back coordinates as its matrix.
* `AlgebraicGeometry.Grassmannian.exists_isUnit_det_chartMatrix_eq_mul`: **two charts that agree
  on a scheme have matrices differing by an invertible matrix on the left.**
* `AlgebraicGeometry.Grassmannian.exists_comp_chart_eq_of_isUnit_det`: **a point of one chart lies
  in the chart attached to `ι` as soon as the square submatrix on the columns `ι` is invertible.**

## References

* [Stacks Project, Tag 089T](https://stacks.math.columbia.edu/tag/089T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Grassmannian

open Classical in
/-- **The matrix of the normalised quotient on the chart attached to `ι`**, with coordinates
`v`: its `j`-th column is the `i`-th standard basis vector if `j = ι i`, and `(v (j, i))_i` if
`j` is outside the range of `ι`. -/
def chartMatrix {k n : ℕ} (ι : Fin (n - k) ↪ Fin n) {R : Type*} [CommRing R]
    (v : ChartIndex.{u} ι → R) : Matrix (Fin (n - k)) (Fin n) R :=
  Matrix.of fun i j =>
    if h : j ∈ Set.range ι then (if ι i = j then 1 else 0) else v (ULift.up (⟨j, h⟩, i))

/-- The column of `chartMatrix ι v` at `ι i'` is the `i'`-th standard basis vector. -/
theorem chartMatrix_apply_self {k n : ℕ} (ι : Fin (n - k) ↪ Fin n) {R : Type*} [CommRing R]
    (v : ChartIndex.{u} ι → R) (i i' : Fin (n - k)) :
    chartMatrix ι v i (ι i') = if i = i' then 1 else 0 := by
  classical
  simp only [chartMatrix, Matrix.of_apply, Set.mem_range_self, dif_pos]
  exact if_congr ⟨fun h => ι.injective h, fun h => h ▸ rfl⟩ rfl rfl

/-- For `j` outside the range of `ι`, the `(i, j)` entry of `chartMatrix ι v` is the coordinate
`v (j, i)`. -/
theorem chartMatrix_apply_of_notMem {k n : ℕ} (ι : Fin (n - k) ↪ Fin n) {R : Type*} [CommRing R]
    (v : ChartIndex.{u} ι → R) (i : Fin (n - k)) {j : Fin n} (hj : j ∉ Set.range ι) :
    chartMatrix ι v i j = v (ULift.up (⟨j, hj⟩, i)) := by
  classical
  simp only [chartMatrix, Matrix.of_apply, dif_neg hj]

/-- The matrix of a ring homomorphism applied to coordinates is the image of the matrix. -/
theorem chartMatrix_map {k n : ℕ} (ι : Fin (n - k) ↪ Fin n) {R S : Type*} [CommRing R]
    [CommRing S] (φ : R →+* S) (v : ChartIndex.{u} ι → R) :
    chartMatrix ι (fun a => φ (v a)) = (chartMatrix ι v).map φ := by
  classical
  ext i j
  simp only [chartMatrix, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp

/-- **The quotient classified by a morphism into a chart has the chart matrix of the pulled
back coordinates as its matrix.** -/
theorem toMatrix_chartQuotientMap {T : Scheme.{u}} {k n : ℕ} (ι : Fin (n - k) ↪ Fin n)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)))) :
    Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap k n ι g) =
      chartMatrix ι (AffineSpace.toSpecMvPolyIntEquiv _ g) := by
  funext i j
  rw [Stacks.FreeSheafMatrix.toMatrix_apply]
  by_cases hj : j ∈ Set.range ι
  · obtain ⟨i', rfl⟩ := hj
    rw [← Category.assoc, ιFree_comp_chartQuotientMap,
      Stacks.FreeSheafMatrix.ιFree_comp_freeProjection_value, chartMatrix_apply_self]
    exact if_congr eq_comm rfl rfl
  · rw [chartMatrix_apply_of_notMem ι _ i hj]
    exact chartQuotientMap_coeff k n ι g j hj i

/-- **Two charts that agree on a scheme have matrices differing by an invertible matrix.** If
`g ≫ chart ι = h ≫ chart κ` then `chartMatrix ι (g^*x) = E * chartMatrix κ (h^*x)` with `E`
invertible. -/
theorem exists_isUnit_det_chartMatrix_eq_mul {T : Scheme.{u}} {k n : ℕ}
    {ι κ : Fin (n - k) ↪ Fin n}
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))))
    (h : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} κ) (ULift.{u} ℤ))))
    (hgh : g ≫ chart k n ι = h ≫ chart k n κ) :
    ∃ E : Matrix (Fin (n - k)) (Fin (n - k)) Γ(T, ⊤), IsUnit E.det ∧
      chartMatrix ι (AffineSpace.toSpecMvPolyIntEquiv _ g) =
        E * chartMatrix κ (AffineSpace.toSpecMvPolyIntEquiv _ h) := by
  obtain ⟨e, he⟩ := exists_iso_chartQuotientMap_comp_eq g h hgh
  let a : Stacks.FreeSheafMatrix.F T (n - k) ⟶ Stacks.FreeSheafMatrix.F T (n - k) := e.hom
  let b : Stacks.FreeSheafMatrix.F T (n - k) ⟶ Stacks.FreeSheafMatrix.F T (n - k) := e.inv
  have hab : a ≫ b = 𝟙 _ := e.hom_inv_id
  refine ⟨Stacks.FreeSheafMatrix.toMatrix b, ?_, ?_⟩
  · exact (Stacks.FreeSheafMatrix.isIso_iff_isUnit_det b).mp ⟨⟨a, e.inv_hom_id, e.hom_inv_id⟩⟩
  · rw [← toMatrix_chartQuotientMap, ← toMatrix_chartQuotientMap, ← he,
      Stacks.FreeSheafMatrix.toMatrix_comp, ← Matrix.mul_assoc,
      ← Stacks.FreeSheafMatrix.toMatrix_comp, hab, Stacks.FreeSheafMatrix.toMatrix_id,
      Matrix.one_mul]

/-- **A point of the chart attached to `κ` lies in the chart attached to `ι` as soon as the
square submatrix of its matrix on the columns `ι` is invertible.** -/
theorem exists_comp_chart_eq_of_isUnit_det {T : Scheme.{u}} {k n : ℕ}
    {ι κ : Fin (n - k) ↪ Fin n}
    (h : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} κ) (ULift.{u} ℤ))))
    (hdet : IsUnit ((chartMatrix κ (AffineSpace.toSpecMvPolyIntEquiv _ h)).submatrix id ι).det) :
    ∃ g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))),
      g ≫ chart k n ι = h ≫ chart k n κ := by
  refine exists_comp_chart_eq_of_isIso h ?_
  rw [Stacks.FreeSheafMatrix.isIso_iff_isUnit_det, Stacks.FreeSheafMatrix.toMatrix_comp,
    toMatrix_chartQuotientMap, Stacks.FreeSheafMatrix.toMatrix_freeMap (X := T) ι]
  convert hdet using 2
  funext i j
  rw [Matrix.mul_apply, Matrix.submatrix_apply]
  simp only [Matrix.of_apply, id, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

end AlgebraicGeometry.Grassmannian

end
