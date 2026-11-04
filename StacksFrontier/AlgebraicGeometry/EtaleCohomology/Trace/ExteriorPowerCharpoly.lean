module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Combinatorics.Colex
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The characteristic polynomial of an exterior power

Let `f` be an endomorphism of a finite-dimensional vector space `V` over a field `K`, and let
`ι : K →+* L` be a ring homomorphism into an algebraically closed field, so that the
characteristic polynomial of `f` has roots `α₁, …, αₙ` (with multiplicity) in `L`.  Then the
characteristic polynomial of `⋀ᵏ f` has, under `ι`, the roots `αₛ = ∏_{i ∈ s} αᵢ` for the
`k`-element sub-multisets `s` of `{α₁, …, αₙ}`.

## Main results

* `Stacks.EtaleCohomology.exists_basis_isUpperTriangular_toMatrix`: an endomorphism of a
  finite-dimensional vector space over an algebraically closed field is triangularizable.
* `Stacks.EtaleCohomology.toMatrix_exteriorPower_map`: the matrix of `⋀ᵏ f` is the matrix of
  `k × k` minors of the matrix of `f`.
* `Stacks.EtaleCohomology.charpoly_exteriorPower_map_map`: the characteristic polynomial of
  `⋀ᵏ f` is `∏_s (X - ∏ s)`, over the `k`-element sub-multisets `s` of the roots of the
  characteristic polynomial of `f`.
* `Stacks.EtaleCohomology.norm_le_div_of_cons_le_roots`: the resulting bound on `|ι λ|` (Weil II
  1.5.1, linear algebra).

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.5.1.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

open Module Polynomial Set.powersetCard

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Triangularization.**  An endomorphism of a finite-dimensional vector space over an
algebraically closed field has an upper triangular matrix in some basis. -/
@[sga "4½ Fonctions_L 1.12"]
theorem exists_basis_isUpperTriangular_toMatrix [IsAlgClosed K] [FiniteDimensional K V]
    (f : Module.End K V) :
    ∃ b : Basis (Fin (finrank K V)) K V, (LinearMap.toMatrix b b f).IsUpperTriangular := by
  suffices h : ∀ (n : ℕ) (V : Type _) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (f : Module.End K V), finrank K V = n →
      ∃ b : Basis (Fin n) K V, (LinearMap.toMatrix b b f).IsUpperTriangular from
    h _ V f rfl
  intro n
  induction n with
  | zero =>
    intro V _ _ _ f hV
    exact ⟨Module.finBasisOfFinrankEq K V hV, fun i => i.elim0⟩
  | succ n ih =>
    intro V _ _ _ f hV
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl (K ∙ v)
    have hfin : finrank K W = n := by
      have := Submodule.finrank_add_eq_of_isCompl hW
      rw [finrank_span_singleton hv.2, hV] at this
      lia
    let p := W.projectionOnto (K ∙ v) hW.symm
    have hdec : ∀ z : V, ∃ a : K, z = (p z : V) + a • v := by
      intro z
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
        ((K ∙ v).projectionOnto W hW z).2
      refine ⟨a, ?_⟩
      rw [ha]
      exact (Submodule.projection_add_projection_eq_self hW.symm z).symm
    obtain ⟨c, hc⟩ := ih W (p ∘ₗ f ∘ₗ W.subtype) hfin
    have hli : ∀ (a : K), ∀ x ∈ W, a • v + x = 0 → a = 0 := by
      intro a x hx hax
      have h1 : a • v ∈ W := by
        rw [eq_neg_of_add_eq_zero_left hax]
        exact W.neg_mem hx
      have h2 : a • v = 0 :=
        Submodule.disjoint_def.mp hW.disjoint _ (Submodule.smul_mem _ a
          (Submodule.mem_span_singleton_self v)) h1
      exact (smul_eq_zero.mp h2).resolve_right hv.2
    have hsp : ∀ z : V, ∃ a : K, z + a • v ∈ W := by
      intro z
      obtain ⟨a, ha⟩ := hdec z
      refine ⟨-a, ?_⟩
      rw [ha, neg_smul, add_neg_cancel_right]
      exact (p z).2
    let b := Basis.mkFinCons v c hli hsp
    have hb : ⇑b = Fin.cons v ((↑) ∘ c) := Basis.coe_mkFinCons _ _ _ _
    refine ⟨b, fun i j hij => ?_⟩
    rw [LinearMap.toMatrix_apply]
    induction j using Fin.cases with
    | zero =>
      have h0 : b 0 = v := by rw [hb]; rfl
      rw [h0, hv.apply_eq_smul, ← h0, map_smul, b.repr_self, Finsupp.smul_apply,
        Finsupp.single_apply, if_neg (Fin.pos_iff_ne_zero.mp (id hij : (0 : Fin _) < i)).symm,
        smul_zero]
    | succ j =>
      induction i using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ i =>
        have hji : j < i := Fin.succ_lt_succ_iff.mp hij
        have hj : b j.succ = c j := by rw [hb]; rfl
        obtain ⟨a, ha⟩ := hdec (f (c j))
        have hpc : p (f (c j)) = ∑ k, c.repr (p (f (c j))) k • c k := (c.sum_repr _).symm
        have hexp : f (b j.succ) = a • b 0 + ∑ k, c.repr (p (f (c j))) k • b k.succ := by
          have e1 : f (b j.succ) = (p (f (c j)) : V) + a • v := by rw [hj]; exact ha
          rw [e1, add_comm]
          congr 1
          · rw [hb]; rfl
          · conv_lhs => rw [hpc]
            rw [Submodule.coe_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Submodule.coe_smul, hb]
            rfl
        have hentry : c.repr (p (f (c j))) i = 0 := by
          have := hc hji
          rwa [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearMap.comp_apply,
            Submodule.subtype_apply] at this
        rw [hexp, map_add, map_smul, map_sum, Finsupp.add_apply, Finsupp.smul_apply,
          b.repr_self, Finsupp.single_eq_of_ne (Fin.succ_ne_zero i), smul_zero, zero_add,
          Finsupp.finset_sum_apply]
        simp_rw [map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
          Fin.succ_inj, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
          smul_eq_mul, mul_one, hentry]

section Minors

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The matrix of `⋀ᵏ f` in the basis `e_S = e_{s₁} ∧ ⋯ ∧ e_{sₖ}` is the matrix of `k × k`
minors of the matrix of `f`. -/
theorem toMatrix_exteriorPower_map {I : Type*} [LinearOrder I] [Fintype I] (b : Basis I R M)
    (f : Module.End R M) (k : ℕ) (T S : Set.powersetCard I k) :
    LinearMap.toMatrix (b.exteriorPower k) (b.exteriorPower k) (exteriorPower.map k f) T S =
      ((LinearMap.toMatrix b b f).submatrix (ofFinEmbEquiv.symm T)
        (ofFinEmbEquiv.symm S)).det := by
  rw [LinearMap.toMatrix_apply, exteriorPower.coe_basis, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.basis_repr_apply, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]

end Minors

/-- The binary encoding of a `k`-subset of `Fin n`. -/
private def binaryCode {n k : ℕ} (S : Set.powersetCard (Fin n) k) : ℕ :=
  ∑ x ∈ (S : Finset (Fin n)), 2 ^ (x : ℕ)

private theorem binaryCode_injective {n k : ℕ} :
    Function.Injective (binaryCode (n := n) (k := k)) := by
  intro S T h
  have h' : ∑ x ∈ (S : Finset (Fin n)).map Fin.valEmbedding, 2 ^ x =
      ∑ x ∈ (T : Finset (Fin n)).map Fin.valEmbedding, 2 ^ x := by
    simpa [binaryCode] using h
  exact Subtype.ext (Finset.map_injective _ (Finset.geomSum_injective le_rfl h'))

private theorem binaryCode_eq_sum {n k : ℕ} (S : Set.powersetCard (Fin n) k) :
    binaryCode S = ∑ i, 2 ^ ((ofFinEmbEquiv.symm S i : Fin n) : ℕ) := by
  rw [binaryCode, ofFinEmbEquiv_symm_apply]
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ (S : Finset (Fin n)) S.prop]
  rw [Finset.sum_map]
  rfl

/-- If `A` is upper triangular, then a nonzero `k × k` minor of `A`, with rows `T` and columns
`S`, has `T` below `S` in the binary order. -/
private theorem binaryCode_le_of_det_ne_zero {n k : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (hA : A.IsUpperTriangular) {T S : Set.powersetCard (Fin n) k}
    (h : (A.submatrix (ofFinEmbEquiv.symm T) (ofFinEmbEquiv.symm S)).det ≠ 0) :
    binaryCode T ≤ binaryCode S := by
  rw [Matrix.det_apply] at h
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hσ' : ∀ i, (ofFinEmbEquiv.symm T (σ i)) ≤ ofFinEmbEquiv.symm S i := by
    intro i
    by_contra hlt
    refine hσ ?_
    rw [Units.smul_def, Finset.prod_eq_zero (Finset.mem_univ i), smul_zero]
    exact hA (not_le.mp hlt)
  rw [binaryCode_eq_sum, binaryCode_eq_sum, ← Equiv.sum_comp σ]
  exact Finset.sum_le_sum fun i _ => Nat.pow_le_pow_right two_pos (hσ' i)

/-- If the matrix of `f` in a basis `b` is upper triangular with diagonal `d`, then the
characteristic polynomial of `⋀ᵏ f` is `∏_S (X - ∏_{i ∈ S} dᵢ)`, over the `k`-subsets `S` of the
index set. -/
theorem charpoly_exteriorPower_map_of_isUpperTriangular [FiniteDimensional K V] {n : ℕ}
    (b : Basis (Fin n) K V) (f : Module.End K V)
    (hf : (LinearMap.toMatrix b b f).IsUpperTriangular) (k : ℕ) :
    (exteriorPower.map k f).charpoly =
      ∏ S : Set.powersetCard (Fin n) k,
        (X - C (∏ i ∈ (S : Finset (Fin n)), LinearMap.toMatrix b b f i i)) := by
  set A := LinearMap.toMatrix b b f
  rw [← LinearMap.charpoly_toMatrix (exteriorPower.map k f) (b.exteriorPower k)]
  let lo : LinearOrder (Set.powersetCard (Fin n) k) :=
    LinearOrder.lift' binaryCode binaryCode_injective
  have hU : (LinearMap.toMatrix (b.exteriorPower k) (b.exteriorPower k)
      (exteriorPower.map k f)).BlockTriangular binaryCode := by
    intro T S hST
    rw [toMatrix_exteriorPower_map]
    by_contra h
    exact absurd (binaryCode_le_of_det_ne_zero hf h) (not_le.mpr hST)
  have hdiag : ∀ S : Set.powersetCard (Fin n) k,
      LinearMap.toMatrix (b.exteriorPower k) (b.exteriorPower k) (exteriorPower.map k f) S S =
        ∏ i ∈ (S : Finset (Fin n)), A i i := by
    intro S
    rw [toMatrix_exteriorPower_map, Matrix.det_of_isUpperTriangular]
    · conv_rhs => rw [← Finset.map_orderEmbOfFin_univ (S : Finset (Fin n)) S.prop]
      rw [Finset.prod_map]
      rfl
    · intro i j hij
      exact hf ((ofFinEmbEquiv.symm S).strictMono hij)
  rw [@Matrix.charpoly_of_isUpperTriangular K _ _ _ _ lo _ hU]
  exact Finset.prod_congr rfl fun S _ => by rw [hdiag]

/-- The roots of `∏ i ∈ m, (X - gᵢ)` are the `gᵢ`. -/
private theorem roots_prod_X_sub_C_map {L ι : Type*} [Field L] (m : Multiset ι) (g : ι → L) :
    (m.map fun i => X - C (g i)).prod.roots = m.map g := by
  simpa [Multiset.map_map, Function.comp_def] using roots_multiset_prod_X_sub_C (m.map g)

/-- Over an algebraically closed field, the characteristic polynomial of `⋀ᵏ f` is
`∏_s (X - ∏ s)` over the `k`-element sub-multisets `s` of the roots of the characteristic
polynomial of `f`. -/
theorem charpoly_exteriorPower_map [IsAlgClosed K] [FiniteDimensional K V]
    (f : Module.End K V) (k : ℕ) :
    (exteriorPower.map k f).charpoly =
      ((f.charpoly.roots.powersetCard k).map fun s => X - C s.prod).prod := by
  obtain ⟨b, hb⟩ := exists_basis_isUpperTriangular_toMatrix f
  set A := LinearMap.toMatrix b b f
  have hroots : f.charpoly.roots = (Finset.univ : Finset (Fin (finrank K V))).val.map
      fun i => A i i := by
    rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_of_isUpperTriangular _ hb,
      Finset.prod_eq_multiset_prod,
      roots_prod_X_sub_C_map]
  rw [charpoly_exteriorPower_map_of_isUpperTriangular b f hb, hroots,
    Multiset.powersetCard_map, Multiset.map_map,
    ← Finset.prod_subtype (Finset.powersetCard k Finset.univ)
      (fun s => by simp)
      (fun s => X - C (∏ i ∈ s, A i i)),
    Finset.prod_eq_multiset_prod, ← Finset.map_val_val_powersetCard, Multiset.map_map]
  rfl

/-- **The characteristic polynomial of an exterior power.**  For `ι : K →+* L` into an
algebraically closed field, the image under `ι` of the characteristic polynomial of `⋀ᵏ f` is
`∏_s (X - ∏ s)` over the `k`-element sub-multisets `s` of the roots of the image under `ι` of
the characteristic polynomial of `f`. -/
theorem charpoly_exteriorPower_map_map [FiniteDimensional K V] {L : Type*} [Field L]
    [IsAlgClosed L] (ι : K →+* L) (f : Module.End K V) (k : ℕ) :
    (exteriorPower.map k f).charpoly.map ι =
      (((f.charpoly.map ι).roots.powersetCard k).map fun s => X - C s.prod).prod := by
  set b := Module.finBasis K V
  set A := LinearMap.toMatrix b b f
  set g : Module.End L (Fin (finrank K V) → L) := Matrix.toLin' (A.map ι)
  have hg : LinearMap.toMatrix (Pi.basisFun L _) (Pi.basisFun L _) g = A.map ι := by
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have hgc : g.charpoly = f.charpoly.map ι := by
    rw [← LinearMap.charpoly_toMatrix g (Pi.basisFun L _), hg, Matrix.charpoly_map,
      LinearMap.charpoly_toMatrix]
  rw [← hgc, ← charpoly_exteriorPower_map g k,
    ← LinearMap.charpoly_toMatrix (exteriorPower.map k f) (b.exteriorPower k),
    ← LinearMap.charpoly_toMatrix (exteriorPower.map k g) ((Pi.basisFun L _).exteriorPower k),
    ← Matrix.charpoly_map]
  congr 1
  ext T S
  rw [Matrix.map_apply, toMatrix_exteriorPower_map, toMatrix_exteriorPower_map, hg,
    RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

/-- A product of `k` roots (with multiplicity) of the image of the characteristic polynomial of
`f` is a root of the image of the characteristic polynomial of `⋀ᵏ f`. -/
theorem prod_mem_roots_charpoly_exteriorPower_map [FiniteDimensional K V] {L : Type*} [Field L]
    [IsAlgClosed L] (ι : K →+* L) (f : Module.End K V) {s : Multiset L}
    (hs : s ≤ (f.charpoly.map ι).roots) :
    s.prod ∈ ((exteriorPower.map (Multiset.card s) f).charpoly.map ι).roots := by
  rw [charpoly_exteriorPower_map_map, roots_prod_X_sub_C_map]
  exact Multiset.mem_map_of_mem _ (Multiset.mem_powersetCard.mpr ⟨hs, rfl⟩)

/-- **The realpure inequality** (Weil II 1.5.1, linear algebra).  Let `λ, β₁, …, β_N` be roots
(with multiplicity) of the image under `ι` of the characteristic polynomial of `f`.  If every
root of the image of the characteristic polynomial of `⋀^{N+1} f` has absolute value at most
`C`, and `β = β₁ ⋯ β_N` is nonzero, then `|λ| ≤ C / |β|`. -/
theorem norm_le_div_of_cons_le_roots [FiniteDimensional K V] (ι : K →+* ℂ)
    (f : Module.End K V) {lam : ℂ} {B : Multiset ℂ}
    (hs : lam ::ₘ B ≤ (f.charpoly.map ι).roots) {C : ℝ}
    (hC : ∀ z ∈ ((exteriorPower.map (Multiset.card B + 1) f).charpoly.map ι).roots, ‖z‖ ≤ C)
    (hB : 0 < ‖B.prod‖) :
    ‖lam‖ ≤ C / ‖B.prod‖ := by
  have hmem := prod_mem_roots_charpoly_exteriorPower_map ι f hs
  rw [Multiset.card_cons] at hmem
  have h := hC _ hmem
  rw [Multiset.prod_cons, norm_mul] at h
  rwa [le_div_iff₀ hB]

/-- **The realpure inequality in terms of weights** (Weil II 1.5.1).  If the roots of the
characteristic polynomial of `⋀^{N+1} f` have weight at most `β + γ` (absolute value at most
`Q^{(β+γ)/2}`), and `N` roots of the characteristic polynomial of `f` have product of weight
`γ`, then every further root `λ` has weight at most `β`. -/
theorem norm_le_rpow_of_cons_le_roots [FiniteDimensional K V] (ι : K →+* ℂ)
    (f : Module.End K V) {lam : ℂ} {B : Multiset ℂ}
    (hs : lam ::ₘ B ≤ (f.charpoly.map ι).roots) {Q β γ : ℝ} (hQ : 0 < Q)
    (hC : ∀ z ∈ ((exteriorPower.map (Multiset.card B + 1) f).charpoly.map ι).roots,
      ‖z‖ ≤ Q ^ ((β + γ) / 2))
    (hB : ‖B.prod‖ = Q ^ (γ / 2)) :
    ‖lam‖ ≤ Q ^ (β / 2) := by
  have h := norm_le_div_of_cons_le_roots ι f hs hC (by rw [hB]; exact Real.rpow_pos_of_pos hQ _)
  rwa [hB, ← Real.rpow_sub hQ, add_div, add_sub_cancel_right] at h

omit [Field K] [AddCommGroup V] [Module K V] in
/-- If finitely many complex numbers, `n` of them, all have absolute value at most `R` and their
product has absolute value `R ^ n`, they all have absolute value `R`. -/
theorem norm_eq_of_forall_norm_le_of_norm_prod_eq {s : Multiset ℂ} {R : ℝ}
    (hle : ∀ z ∈ s, ‖z‖ ≤ R) (hprod : ‖s.prod‖ = R ^ Multiset.card s) :
    ∀ z ∈ s, ‖z‖ = R := by
  intro z hz
  refine le_antisymm (hle z hz) (not_lt.mp fun hlt => ?_)
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hz
  have hR : 0 < R := (norm_nonneg z).trans_lt hlt
  have key : ∀ u : Multiset ℂ, (∀ x ∈ u, ‖x‖ ≤ R) → ‖u.prod‖ ≤ R ^ Multiset.card u := by
    intro u
    induction u using Multiset.induction_on with
    | empty => intro _; simp
    | cons a u ih =>
      intro hu
      rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
      exact mul_le_mul (hu a (Multiset.mem_cons_self a u))
        (ih fun x hx => hu x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _) hR.le
  have ht := key t fun x hx => hle x (Multiset.mem_cons_of_mem hx)
  rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ'] at hprod
  have : ‖z‖ * ‖t.prod‖ < R * R ^ Multiset.card t :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht (norm_nonneg z))
      (mul_lt_mul_of_pos_right hlt (pow_pos hR _))
  exact this.ne hprod

/-- **The last step of Weil II 1.5.1.**  If every root of the characteristic polynomial of `f`
(mapped by `ι` to `ℂ`) has absolute value at most `R` and `‖ι det f‖ = R ^ dim V`, then every
root has absolute value exactly `R`. -/
theorem norm_eq_of_forall_norm_le_of_norm_det_eq [FiniteDimensional K V] (ι : K →+* ℂ)
    (f : Module.End K V) {R : ℝ}
    (hle : ∀ z ∈ (f.charpoly.map ι).roots, ‖z‖ ≤ R)
    (hdet : ‖ι (LinearMap.det f)‖ = R ^ Module.finrank K V) :
    ∀ z ∈ (f.charpoly.map ι).roots, ‖z‖ = R := by
  have hmon : (f.charpoly.map ι).Monic := (LinearMap.charpoly_monic f).map ι
  have hspl : (f.charpoly.map ι).Splits := IsAlgClosed.splits _
  have hdeg : (f.charpoly.map ι).natDegree = Module.finrank K V := by
    rw [(LinearMap.charpoly_monic f).natDegree_map, LinearMap.charpoly_natDegree]
  have hcard : Multiset.card (f.charpoly.map ι).roots = Module.finrank K V := by
    rw [← Polynomial.Splits.natDegree_eq_card_roots hspl, hdeg]
  refine norm_eq_of_forall_norm_le_of_norm_prod_eq hle ?_
  have hc := Polynomial.Splits.coeff_zero_eq_prod_roots_of_monic hspl hmon
  rw [Polynomial.coeff_map, hdeg] at hc
  rw [hcard, ← hdet, LinearMap.det_eq_sign_charpoly_coeff, map_mul, hc, map_pow, map_neg,
    map_one, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, one_mul]

end Stacks.EtaleCohomology
