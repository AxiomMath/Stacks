module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# The top exterior power of an endomorphism is its determinant

Let `M` be a free module of rank `n` over a commutative ring `R`. The top exterior power
`⋀ⁿ M` is then free of rank one, and the functorial map `⋀ⁿ φ = exteriorPower.map n φ` induced
by an endomorphism `φ` of `M` is multiplication by the scalar `det φ`.

This is the comparison that identifies the degree-`n` component of a map of Koszul complexes
`K_•(f₁, …, f_n) → K_•(g₁, …, g_n)` coming from a relation `fᵢ = ∑ⱼ gᵢⱼ gⱼ` with the
determinant `det (gᵢⱼ)`: by [Stacks, Tag 0624] the map of complexes is `⋀(ψ)` for the linear map
`ψ` with matrix `(gᵢⱼ)`, and in top degree `⋀ⁿ ψ` is multiplication by `det (gᵢⱼ)`.

Mathlib's `exteriorPower` API has no determinant lemma; `Mathlib.LinearAlgebra.Determinant`
relates determinants to the alternating form `Basis.det` but not to `exteriorPower.map`. The
bridge below is `exteriorPower.ιMultiDual`, which for the top power is the single coordinate of
the rank-one basis `Module.Basis.exteriorPower` and sends `ιMulti R n v` to `b.det v`.

## Main results

* `exteriorPower.ιMultiDual_top_ιMulti`: for the top power, `ιMultiDual` evaluated on a wedge
  `v₁ ∧ ⋯ ∧ vₙ` is the alternating form `Module.Basis.det`.
* `exteriorPower.map_top_eq_det_smul`: `⋀ⁿ φ` acts on `⋀ⁿ M` as `det φ • id`.
* `exteriorPower.map_top_pi_eq_det_smul`: the same statement for `M = Rⁿ` and `φ` the linear map
  of a matrix, with the scalar `Matrix.det`.
* `exteriorPower.map_top_ιMulti_eq_det_smul`: for a map `φ : M →ₗ[R] N` between two free modules
  of rank `n`, `⋀ⁿ φ` carries the wedge of a basis of `M` to the determinant of the matrix of
  `φ` times the wedge of a basis of `N`.

## References

* [Stacks Project, Tag 0624](https://stacks.math.columbia.edu/tag/0624)
-/

@[expose] public noncomputable section

universe u v

namespace exteriorPower

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/-- The only subset of `Fin n` of cardinality `n` is `Finset.univ`. -/
theorem eq_univ_powersetCard (t : Set.powersetCard (Fin n) n) :
    t = (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin n) n) :=
  Set.powersetCard.eq_iff_subset.mpr (Finset.subset_univ _)

/-- The enumeration of `Finset.univ : Finset (Fin n)` in increasing order is the identity. -/
theorem ofFinEmbEquiv_symm_univ_apply (i : Fin n) :
    Set.powersetCard.ofFinEmbEquiv.symm
      (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin n) n) i = i := by
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact congrFun
    (Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin n)))
      (by simp) (fun _ => Finset.mem_univ _) strictMono_id).symm i

/-- **The top exterior power pairs to `Basis.det`.** For `b` a basis of `M` indexed by `Fin n`,
the linear form `exteriorPower.ιMultiDual R n b t` on the top exterior power `⋀ⁿ M` sends the
wedge `v₁ ∧ ⋯ ∧ vₙ` to `b.det v`. -/
theorem ιMultiDual_top_ιMulti (b : Module.Basis (Fin n) R M)
    (t : Set.powersetCard (Fin n) n) (v : Fin n → M) :
    ιMultiDual R n b t (ιMulti R n v) = b.det v := by
  rw [ιMultiDual_apply_ιMulti, Module.Basis.det_apply, ← Matrix.det_transpose]
  congr 1 with i j
  rw [Matrix.transpose_apply, Matrix.of_apply, eq_univ_powersetCard t,
    ofFinEmbEquiv_symm_univ_apply, Module.Basis.coord_apply, Module.Basis.toMatrix_apply]

/-- The single coordinate of the rank-one basis of the top exterior power is injective. -/
theorem ιMultiDual_top_injective (b : Module.Basis (Fin n) R M)
    (t : Set.powersetCard (Fin n) n) :
    Function.Injective (ιMultiDual R n b t) := by
  intro x y hxy
  apply (b.exteriorPower n).repr.injective
  refine Finsupp.ext fun s => ?_
  have hs : s = t := (eq_univ_powersetCard s).trans (eq_univ_powersetCard t).symm
  subst hs
  have hco := LinearMap.congr_fun (basis_coord (R := R) (M := M) n b s)
  exact (hco x).trans (hxy.trans (hco y).symm)

/-- **The top exterior power of an endomorphism is multiplication by its determinant.** If `M`
is free of rank `n` with basis `b` indexed by `Fin n`, then for every `φ : M →ₗ[R] M` the map
`⋀ⁿ φ` on `⋀ⁿ M` is `det φ • id`. -/
theorem map_top_eq_det_smul (b : Module.Basis (Fin n) R M) (φ : M →ₗ[R] M) (x : ⋀[R]^n M) :
    map n φ x = LinearMap.det φ • x := by
  classical
  refine ιMultiDual_top_injective b ⟨Finset.univ, by simp⟩ ?_
  have hspan : x ∈ Submodule.span R (Set.range (ιMulti R n (M := M))) := by
    rw [ιMulti_span]
    exact Submodule.mem_top
  induction hspan using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [map_apply_ιMulti, map_smul, ιMultiDual_top_ιMulti b _,
      ιMultiDual_top_ιMulti b _, Module.Basis.det_comp, smul_eq_mul]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, smul_add, map_add, hy, hz]
  | smul c y _ hy => rw [map_smul, map_smul, smul_comm, map_smul, hy]

/-- **The top exterior power of a map of free modules of equal rank is its determinant.** For
`b` a basis of `M` and `c` a basis of `N`, both indexed by `Fin n`, and `φ : M →ₗ[R] N`, the map
`⋀ⁿ φ` carries the wedge of `b` to `det (LinearMap.toMatrix b c φ)` times the wedge of `c`.

Both top exterior powers are free of rank one on those wedges, so this computes `⋀ⁿ φ`
completely; `exteriorPower.map_top_eq_det_smul` is the case `N = M`, `c = b`. -/
theorem map_top_ιMulti_eq_det_smul {N : Type*} [AddCommGroup N] [Module R N]
    (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin n) R N) (φ : M →ₗ[R] N) :
    map n φ (ιMulti R n b) = (LinearMap.toMatrix b c φ).det • ιMulti R n c := by
  classical
  refine ιMultiDual_top_injective c ⟨Finset.univ, by simp⟩ ?_
  rw [map_apply_ιMulti, map_smul, ιMultiDual_top_ιMulti c _, ιMultiDual_top_ιMulti c _,
    Module.Basis.det_self, smul_eq_mul, mul_one, Module.Basis.det_apply]
  congr 1 with i j
  rw [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply, Function.comp_apply]

/-- **The top exterior power of a free module of rank `n` is free of rank one on the wedge of a
basis.**  The single coordinate of `Module.Basis.exteriorPower` is a linear equivalence
`⋀ⁿ M ≃ₗ[R] R` carrying `b 0 ∧ ⋯ ∧ b (n-1)` to `1`. -/
def topLinearEquivOfBasis (b : Module.Basis (Fin n) R M) : (⋀[R]^n M) ≃ₗ[R] R :=
  LinearEquiv.ofBijective (ιMultiDual R n b ⟨Finset.univ, by simp⟩)
    ⟨ιMultiDual_top_injective b _, fun r =>
      ⟨r • ιMulti R n b, by
        rw [map_smul, ιMultiDual_top_ιMulti b _ b, Module.Basis.det_self, smul_eq_mul, mul_one]⟩⟩

/-- The trivialization of the top exterior power carries the wedge of the basis to `1`. -/
@[simp] theorem topLinearEquivOfBasis_ιMulti (b : Module.Basis (Fin n) R M) :
    topLinearEquivOfBasis b (ιMulti R n b) = 1 :=
  (ιMultiDual_top_ιMulti b _ b).trans (Module.Basis.det_self b)

/-- **The top exterior power of a square matrix acts by its determinant.** For `M = Rⁿ` with the
standard basis and `φ` the linear map of an `n × n` matrix `A`, the map `⋀ⁿ φ` on `⋀ⁿ(Rⁿ)` is
multiplication by `Matrix.det A`. -/
theorem map_top_pi_eq_det_smul (A : Matrix (Fin n) (Fin n) R) (x : ⋀[R]^n (Fin n → R)) :
    map n (Matrix.toLin' A) x = A.det • x := by
  classical
  rw [map_top_eq_det_smul (Pi.basisFun R (Fin n)) (Matrix.toLin' A) x,
    LinearMap.det_toLin']

end exteriorPower

end
