module

public import Mathlib.RingTheory.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFields
public import StacksFrontier.LinearAlgebra.Matrix.HomogeneousDeterminant

/-!
# A finite extension of a \(C_1\) field is a \(C_1\) field

Let `L/K` be a finite field extension of degree `N`. A form of degree `d` in `n` variables over
`L` has a norm form over `K`, of degree `N * d` in `n * N` variables, whose values are the norms
of the values of the original form. As a consequence, a finite extension of a \(C_1\) field is a
\(C_1\) field.

## Main results

* `IsCField.exists_nonzero_zero`: the defining property of a \(C_r\) field for a form whose
  variables are indexed by an arbitrary finite type rather than by `Fin n`.
* `IsCField.of_ringEquiv`: the \(C_r\) condition is invariant under isomorphism of fields.
* `Algebra.exists_isHomogeneous_norm_form`: a form over a finite extension `L/K` admits a norm
  form over `K`, of degree multiplied by the degree of the extension.
* `isCField_one_of_module_finite`: a finite extension of a \(C_1\) field is a \(C_1\) field.

## References

* [Stacks Project, Tag 03R9](https://stacks.math.columbia.edu/tag/03R9)
* [Stacks Project, Tag 03RD](https://stacks.math.columbia.edu/tag/03RD)
-/

@[expose] public noncomputable section

/-- The defining property of a \(C_r\) field, for a form whose variables are indexed by an
arbitrary finite type: a form of degree `d > 0` in more than `d ^ r` variables has a
nontrivial zero. -/
theorem IsCField.exists_nonzero_zero {K : Type*} [Field K] {r : ℕ} (hK : IsCField K r)
    {ι : Type*} [Fintype ι] {d : ℕ} (hd : 0 < d) (hdn : d ^ r < Fintype.card ι)
    (f : MvPolynomial ι K) (hf : f.IsHomogeneous d) :
    ∃ α : ι → K, α ≠ 0 ∧ MvPolynomial.eval α f = 0 := by
  classical
  obtain ⟨σ⟩ := Fintype.truncEquivFin ι
  obtain ⟨α, hα0, hα⟩ := hK d (Fintype.card ι) ⟨hd, hdn⟩ (MvPolynomial.rename σ f)
    hf.rename_isHomogeneous
  refine ⟨α ∘ σ, ?_, ?_⟩
  · exact fun hcon ↦ hα0 (funext fun j ↦ by simpa using congrFun hcon (σ.symm j))
  · rwa [MvPolynomial.eval_rename] at hα

/-- Being a \(C_r\) field is invariant under isomorphism of fields. -/
theorem IsCField.of_ringEquiv {K L : Type*} [Field K] [Field L] {r : ℕ} (hK : IsCField K r)
    (φ : K ≃+* L) : IsCField L r := by
  rintro d n ⟨hd, hdn⟩ f hf
  obtain ⟨α, hα0, hα⟩ := hK d n ⟨hd, hdn⟩ (MvPolynomial.map (φ.symm : L →+* K) f)
    (hf.map (φ.symm : L →+* K))
  refine ⟨fun i ↦ φ (α i),
    fun hcon ↦ hα0 (funext fun i ↦ φ.injective (by simpa using congrFun hcon i)), ?_⟩
  have hid : (φ : K →+* L).comp (φ.symm : L →+* K) = RingHom.id L :=
    RingHom.ext fun a ↦ by simp
  have hcl := MvPolynomial.eval₂_comp_left (φ : K →+* L) (φ.symm : L →+* K) α f
  rw [MvPolynomial.eval_map] at hα
  rw [hid, MvPolynomial.eval₂_id, hα, map_zero] at hcl
  simpa [Function.comp_def] using hcl.symm

/-- Let `L/K` be a field extension with a basis indexed by `Fin N`. A form of degree `d` over
`L` admits a *norm form*: a form of degree `N * d` in the same variables, with coefficients in
`K`, whose value at a `K`-point is the norm of the value of the original form at that point. -/
theorem Algebra.exists_isHomogeneous_norm_form {K L : Type*} [Field K] [Field L] [Algebra K L]
    {N : ℕ} (e : Module.Basis (Fin N) K L) {σ : Type*} {d : ℕ} (p : MvPolynomial σ L)
    (hp : p.IsHomogeneous d) :
    ∃ g : MvPolynomial σ K, g.IsHomogeneous (N * d) ∧
      ∀ α : σ → K, MvPolynomial.eval α g
        = Algebra.norm K (MvPolynomial.eval (fun x => algebraMap K L (α x)) p) := by
  classical
  set M : Matrix (Fin N) (Fin N) (MvPolynomial σ K) := fun i j ↦
    ∑ ν ∈ p.support, MvPolynomial.monomial ν (Algebra.leftMulMatrix e (p.coeff ν) i j) with hM
  have hMhom : ∀ i j, (M i j).IsHomogeneous d := fun i j ↦
    MvPolynomial.IsHomogeneous.sum _ _ _ fun ν hν ↦
      MvPolynomial.isHomogeneous_monomial _
        (by rw [Finsupp.degree_apply]; exact (hp.degree_eq_sum_deg_support hν).symm)
  refine ⟨M.det, by simpa using Matrix.IsHomogeneous.det M hMhom, fun α ↦ ?_⟩
  have hz : MvPolynomial.eval (fun x ↦ algebraMap K L (α x)) p
      = ∑ ν ∈ p.support, (∏ x ∈ ν.support, α x ^ ν x) • p.coeff ν := by
    rw [MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun ν _ ↦ ?_
    rw [Algebra.smul_def, map_prod]
    simp [mul_comm]
  rw [Algebra.norm_eq_matrix_det e, RingHom.map_det (MvPolynomial.eval α) M, hz, map_sum]
  congr 1
  ext i j
  have hleft : (M.map (MvPolynomial.eval α)) i j
      = ∑ ν ∈ p.support,
          (∏ x ∈ ν.support, α x ^ ν x) * Algebra.leftMulMatrix e (p.coeff ν) i j := by
    rw [Matrix.map_apply, hM, map_sum]
    exact Finset.sum_congr rfl fun ν _ ↦ by
      rw [MvPolynomial.eval_monomial, mul_comm]; rfl
  have hright : (∑ ν ∈ p.support,
        Algebra.leftMulMatrix e ((∏ x ∈ ν.support, α x ^ ν x) • p.coeff ν)) i j
      = ∑ ν ∈ p.support,
          (∏ x ∈ ν.support, α x ^ ν x) * Algebra.leftMulMatrix e (p.coeff ν) i j := by
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun ν _ ↦ by rw [map_smul, Matrix.smul_apply, smul_eq_mul]
  rw [RingHom.mapMatrix_apply, hleft, hright]

/-- A finite extension of a \(C_1\) field is a \(C_1\) field. -/
theorem isCField_one_of_module_finite (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (hK : IsCField K 1) : IsCField L 1 := by
  classical
  rintro d n ⟨hd, hdn⟩ f hf
  rw [pow_one] at hdn
  set N := Module.finrank K L
  set e : Module.Basis (Fin N) K L := Module.finBasis K L
  have hNpos : 0 < N := Fin.pos_iff_nonempty.mpr e.index_nonempty
  set sub : Fin n → MvPolynomial (Fin n × Fin N) L := fun i ↦
    ∑ j, MvPolynomial.C (e j) * MvPolynomial.X (i, j) with hsub
  have hsubhom : ∀ i, (sub i).IsHomogeneous 1 := fun i ↦
    MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ ↦ MvPolynomial.isHomogeneous_C_mul_X _ _
  have hCsub : (MvPolynomial.eval₂ MvPolynomial.C sub f).IsHomogeneous d := by
    simpa using hf.eval₂ (MvPolynomial.C (σ := Fin n × Fin N) (R := L)) sub
      (fun r ↦ MvPolynomial.isHomogeneous_C _ r) hsubhom
  obtain ⟨g, hg, hgeval⟩ := Algebra.exists_isHomogeneous_norm_form e
    (MvPolynomial.eval₂ MvPolynomial.C sub f) hCsub
  have hcount : (N * d) ^ 1 < Fintype.card (Fin n × Fin N) := by
    simp only [pow_one, Fintype.card_prod, Fintype.card_fin]
    calc N * d < N * n := mul_lt_mul_of_pos_left hdn hNpos
      _ = n * N := Nat.mul_comm _ _
  obtain ⟨α, hα0, hα⟩ := hK.exists_nonzero_zero (Nat.mul_pos hNpos hd) hcount g hg
  refine ⟨fun i ↦ ∑ j, α (i, j) • e j, fun hcon ↦ hα0 (funext fun x ↦
    Fintype.linearIndependent_iff.mp e.linearIndependent (fun j ↦ α (x.1, j))
      (congrFun hcon x.1) x.2), ?_⟩
  have hid : (MvPolynomial.eval fun x ↦ algebraMap K L (α x)).comp
      (MvPolynomial.C : L →+* MvPolynomial (Fin n × Fin N) L) = RingHom.id L :=
    RingHom.ext fun a ↦ by simp
  have hcl := MvPolynomial.eval₂_comp_left
    (MvPolynomial.eval fun x ↦ algebraMap K L (α x))
    (MvPolynomial.C : L →+* MvPolynomial (Fin n × Fin N) L) sub f
  rw [hid, MvPolynomial.eval₂_id] at hcl
  have hsubeval : (fun i ↦ MvPolynomial.eval (fun x ↦ algebraMap K L (α x)) (sub i))
      = fun i ↦ ∑ j, α (i, j) • e j := by
    funext i
    simp [hsub, Algebra.smul_def, mul_comm]
  rw [hgeval α, hcl] at hα
  simp only [Function.comp_def, hsubeval] at hα
  exact (Algebra.norm_eq_zero_iff_of_basis e).mp hα

end
