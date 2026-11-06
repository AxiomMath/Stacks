module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Gram matrices of Frobenius-equivariant pairings, from finite levels to `ℚ_ℓ`

Let `M` be a free `ℤ_ℓ`-module of finite rank with an endomorphism `φ`, and suppose that for
every `n` there is a left-nondegenerate pairing `e` on `M / ℓⁿ M` with `e(φ a, φ b) = q e(a, b)`;
the pairings need not be compatible with each other. Then in every basis of `M ⊗ ℚ_ℓ` there is a
Gram matrix `J` with `det J` a unit and `Aᵀ J A = q J`, `A` the matrix of `φ`.

* At a finite level, a left-nondegenerate equivariant pairing on `M / ℓⁿ M`, `M` free over
  `ℤ_ℓ`, has a Gram matrix with unit determinant satisfying the identity modulo `ℓⁿ`
  (`Stacks.EtaleCohomology.exists_gram_zmodPow_of_pairing`).
* Solutions modulo every `ℓⁿ` give a solution over `ℤ_ℓ`
  (`Stacks.EtaleCohomology.exists_isUnit_det_transpose_mul_mul_eq_smul_of_forall_zmodPow`):
  the sets of matrices over `ℤ_ℓ` solving the identity modulo `ℓⁿ` with unit determinant are
  closed, nonempty and decreasing in the compact space `M_r(ℤ_ℓ)`, so they have a common point.
  No compatibility between the levels is needed.
* Over a field, an equivariant left-nondegenerate pairing gives such a `J` in *every* basis
  (`Stacks.EtaleCohomology.isUnit_det_toMatrix₂_and_transpose_mul_mul_eq_smul`).
* Together: for a free `ℤ_ℓ`-module `M` with such pairings at every level, the Gram identity
  holds in every basis of `M ⊗ ℚ_ℓ`
  (`Stacks.EtaleCohomology.exists_isUnit_det_transpose_mul_mul_eq_smul_extendScalars`).
-/

@[expose] public noncomputable section

open Matrix

universe v

namespace Stacks.EtaleCohomology

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- **An equivariant pairing gives the Gram identity in every basis.** If `B` is a
left-nondegenerate bilinear form on a finite-dimensional space with `B (φ v) (φ w) = c B v w`,
then in every basis `b` the Gram matrix `J` of `B` has nonzero determinant and
`Aᵀ J A = c J` for the matrix `A` of `φ`. -/
theorem isUnit_det_toMatrix₂_and_transpose_mul_mul_eq_smul (b : Module.Basis ι K V)
    {B : V →ₗ[K] V →ₗ[K] K} (hB : B.SeparatingLeft) (φ : V →ₗ[K] V) (c : K)
    (hφ : ∀ v w, B (φ v) (φ w) = c * B v w) :
    IsUnit (LinearMap.toMatrix₂ b b B).det ∧
      (LinearMap.toMatrix b b φ)ᵀ * LinearMap.toMatrix₂ b b B * LinearMap.toMatrix b b φ =
        c • LinearMap.toMatrix₂ b b B := by
  refine ⟨((LinearMap.separatingLeft_iff_det_ne_zero b).1 hB).isUnit, ?_⟩
  rw [← LinearMap.toMatrix₂_compl₁₂, ← map_smul]
  congr 1
  ext v w
  simp [hφ]

/-- **A Gram identity in one basis gives one in every basis.** If in a basis `b₀` some matrix
`J₀` with unit determinant satisfies `A₀ᵀ J₀ A₀ = c J₀`, `A₀` the matrix of `φ`, then in every
basis `b` there is such a matrix: the Gram matrix in `b` of the form with Gram matrix `J₀` in
`b₀`. -/
theorem exists_isUnit_det_transpose_mul_mul_eq_smul_of_basis {ι' : Type*} [Fintype ι']
    [DecidableEq ι'] (b₀ : Module.Basis ι K V) (φ : V →ₗ[K] V) (c : K)
    (J₀ : Matrix ι ι K) (hJ₀ : IsUnit J₀.det)
    (h : (LinearMap.toMatrix b₀ b₀ φ)ᵀ * J₀ * LinearMap.toMatrix b₀ b₀ φ = c • J₀)
    (b : Module.Basis ι' K V) :
    ∃ J : Matrix ι' ι' K, IsUnit J.det ∧
      (LinearMap.toMatrix b b φ)ᵀ * J * LinearMap.toMatrix b b φ = c • J := by
  set B := Matrix.toLinearMap₂ b₀ b₀ J₀
  have hB : LinearMap.toMatrix₂ b₀ b₀ B = J₀ := LinearMap.toMatrix₂_toLinearMap₂ b₀ b₀ J₀
  have hsep : B.SeparatingLeft :=
    (LinearMap.separatingLeft_iff_det_ne_zero b₀).2 (by rw [hB]; exact hJ₀.ne_zero)
  have hcomp : B.compl₁₂ φ φ = c • B := by
    apply (LinearMap.toMatrix₂ b₀ b₀).injective
    rw [LinearMap.toMatrix₂_compl₁₂ b₀ b₀, hB, h, map_smul, hB]
  refine ⟨LinearMap.toMatrix₂ b b B,
    isUnit_det_toMatrix₂_and_transpose_mul_mul_eq_smul b hsep φ c fun v w => ?_⟩
  simpa using LinearMap.congr_fun₂ hcomp v w

end Field

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- `pⁿ` maps to zero in `ℤ/pⁿ`. -/
private theorem toZModPow_p_pow_self (n : ℕ) :
    PadicInt.toZModPow n ((p : ℤ_[p]) ^ n) = 0 := by
  rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]

/-- `ℤ/pⁿ` is nontrivial-sized: `pⁿ ≠ 0`. -/
private instance neZero_pow_of_prime (n : ℕ) : NeZero (p ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- A residue of a unit of `ℤ_p`: if the image of `x` modulo `p ^ (n + 1)` is a unit, so is
`x`. -/
theorem isUnit_of_isUnit_toZModPow_succ {x : ℤ_[p]} {n : ℕ}
    (hx : IsUnit (PadicInt.toZModPow (n + 1) x)) : IsUnit x := by
  by_contra hn
  have hm : x ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    exact (IsLocalRing.mem_maximalIdeal x).2 hn
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hm
  rw [map_mul] at hx
  have hpu := isUnit_of_mul_isUnit_right hx
  have h := hpu.pow (n + 1)
  rw [← map_pow, toZModPow_p_pow_self] at h
  have : Fact (1 < p ^ (n + 1)) :=
    ⟨Nat.one_lt_pow n.succ_ne_zero (Fact.out : p.Prime).one_lt⟩
  exact not_isUnit_zero h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Solutions modulo every `pⁿ` give a solution over `ℤ_p`.** If for every `n` there is a
matrix `Jₙ` over `ℤ/pⁿ` with unit determinant and `Aᵀ Jₙ A = c Jₙ` modulo `pⁿ`, there is a
matrix `J` over `ℤ_p` with unit determinant and `Aᵀ J A = c J`. The `Jₙ` need not be
compatible: the matrices over `ℤ_p` solving the identity modulo `pⁿ` with unit determinant form
a decreasing sequence of nonempty closed subsets of the compact space `M_r(ℤ_p)`. -/
theorem exists_isUnit_det_transpose_mul_mul_eq_smul_of_forall_zmodPow
    (A : Matrix ι ι ℤ_[p]) (c : ℕ)
    (h : ∀ n : ℕ, ∃ J : Matrix ι ι (ZMod (p ^ n)), IsUnit J.det ∧
      (A.map (PadicInt.toZModPow n))ᵀ * J * A.map (PadicInt.toZModPow n) = (c : ZMod (p ^ n)) • J) :
    ∃ J : Matrix ι ι ℤ_[p], IsUnit J.det ∧ Aᵀ * J * A = (c : ℤ_[p]) • J := by
  classical
  let E : Matrix ι ι ℤ_[p] → Matrix ι ι ℤ_[p] := fun J => Aᵀ * J * A - c • J
  let t : ℕ → Set (Matrix ι ι ℤ_[p]) := fun n =>
    {J | ∀ i j, ‖E J i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))} ∩ {J | ‖J.det‖ = 1}
  have hEc : Continuous E :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).sub
      (continuous_const_smul c)
  have hcl : ∀ n, IsClosed (t n) := by
    intro n
    refine IsClosed.inter ?_
      (isClosed_eq (continuous_norm.comp continuous_id.matrix_det) continuous_const)
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (continuous_norm.comp (hEc.matrix_elem i j)) continuous_const
  have hle : ∀ n : ℕ, (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) ≤ (p : ℝ) ^ (-(n : ℤ)) := fun n =>
    zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_le) (by omega)
  have hdec : ∀ n, t (n + 1) ⊆ t n := by
    rintro n J ⟨h1, h2⟩
    exact ⟨fun i j => (h1 i j).trans (hle n), h2⟩
  have hne : ∀ n, (t n).Nonempty := by
    intro n
    obtain ⟨J₀, hJ₀, hA₀⟩ := h (n + 1)
    set f := PadicInt.toZModPow (p := p) (n + 1)
    have hs := ZMod.ringHom_surjective f
    let J : Matrix ι ι ℤ_[p] := fun i j => Function.surjInv hs (J₀ i j)
    have hJ : J.map f = J₀ := by
      ext i j
      exact Function.surjInv_eq hs _
    refine ⟨J, fun i j => ?_, ?_⟩
    · have hmap : (E J).map f = 0 := by
        simp only [E]
        rw [Matrix.map_sub _ (map_sub f), Matrix.map_smul _ _ (fun a => map_nsmul f c a),
          Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJ, hA₀, Nat.cast_smul_eq_nsmul,
          sub_self]
      have hmem : E J i j ∈ (Ideal.span {(p : ℤ_[p]) ^ (n + 1)} : Ideal ℤ_[p]) := by
        rw [← PadicInt.ker_toZModPow]
        exact congrFun (congrFun hmap i) j
      exact ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 hmem).trans (hle n)
    · rw [Set.mem_setOf_eq, ← PadicInt.isUnit_iff]
      refine isUnit_of_isUnit_toZModPow_succ (n := n) ?_
      rw [RingHom.map_det]
      show IsUnit (J.map f).det
      rwa [hJ]
  have : CompactSpace (Matrix ι ι ℤ_[p]) := inferInstanceAs (CompactSpace (ι → ι → ℤ_[p]))
  obtain ⟨J, hJ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hJ
  refine ⟨J, PadicInt.isUnit_iff.2 (hJ 0).2, ?_⟩
  rw [← sub_eq_zero, Nat.cast_smul_eq_nsmul]
  ext i j : 1
  show E J i j = 0
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  rw [map_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  exact (hJ n).1 i j

/-- An additive map from a `ℤ_p`-module to `ℤ/pⁿ` is `ℤ_p`-linear: `x` acts on `ℤ/pⁿ` through its
residue, an integer modulo `pⁿ`. -/
theorem map_smul_eq_toZModPow_mul {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] {n : ℕ}
    (e : M →+ ZMod (p ^ n)) (x : ℤ_[p]) (a : M) :
    e (x • a) = PadicInt.toZModPow n x * e a := by
  set z : ℕ := (PadicInt.toZModPow n x).val with hzdef
  have hz : PadicInt.toZModPow n (x - (z : ℤ_[p])) = 0 := by
    rw [map_sub, map_natCast, hzdef, ZMod.natCast_zmod_val, sub_self]
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow] at hz
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hz
  have hx : x = (z : ℤ_[p]) + (p : ℤ_[p]) ^ n * y := by
    rw [mul_comm, hy]
    ring
  have hpn : e (((p : ℤ_[p]) ^ n * y) • a) = 0 := by
    rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul]
  calc e (x • a) = e ((z : ℤ_[p]) • a + ((p : ℤ_[p]) ^ n * y) • a) := by rw [← add_smul, ← hx]
    _ = (z : ZMod (p ^ n)) * e a := by
      rw [map_add, hpn, add_zero, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    _ = PadicInt.toZModPow n x * e a := by rw [hzdef, ZMod.natCast_zmod_val]

/-- **The Gram matrix of an equivariant pairing at a finite level.** Let `M` be a free
`ℤ_p`-module with basis `m`, `φ` an endomorphism with matrix `A`, and `e : M × M → ℤ/pⁿ` a
biadditive pairing, nondegenerate on the left modulo `pⁿ` (`e(a, -) = 0` only for
`a ∈ pⁿ M`) with `e(φ a, φ b) = c e(a, b)`. Its Gram matrix `J` has unit determinant over `ℤ/pⁿ`
and `Aᵀ J A = c J` modulo `pⁿ`. -/
theorem exists_gram_zmodPow_of_pairing {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (m : Module.Basis ι ℤ_[p] M) (φ : M →ₗ[ℤ_[p]] M) (c n : ℕ) (e : M →+ M →+ ZMod (p ^ n))
    (he0 : ∀ a, (∀ b, e a b = 0) → ∃ a', a = (p : ℤ_[p]) ^ n • a')
    (he : ∀ a b, e (φ a) (φ b) = (c : ZMod (p ^ n)) * e a b) :
    ∃ J : Matrix ι ι (ZMod (p ^ n)), IsUnit J.det ∧
      ((LinearMap.toMatrix m m φ).map (PadicInt.toZModPow n))ᵀ * J *
        (LinearMap.toMatrix m m φ).map (PadicInt.toZModPow n) = (c : ZMod (p ^ n)) • J := by
  classical
  set f := PadicInt.toZModPow (p := p) n
  have hs := ZMod.ringHom_surjective f
  let G : Matrix ι ι (ZMod (p ^ n)) := fun i j => e (m i) (m j)
  have hl : ∀ x a b, e (x • a) b = f x * e a b := fun x a b =>
    map_smul_eq_toZModPow_mul (e.flip b) x a
  have hr : ∀ x a b, e a (x • b) = f x * e a b := fun x a b =>
    map_smul_eq_toZModPow_mul (e a) x b
  have hexp : ∀ a b, e a b = ∑ i, ∑ j, f (m.repr a i) * f (m.repr b j) * G i j := by
    intro a b
    conv_lhs => rw [← m.sum_repr a, ← m.sum_repr b]
    simp only [map_sum, AddMonoidHom.finset_sum_apply, hl, hr]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [G]
    ring
  refine ⟨G, ?_, ?_⟩
  · have hinj0 : ∀ v : ι → ZMod (p ^ n), v ᵥ* G = 0 → v = 0 := by
      intro v hv
      let x : ι → ℤ_[p] := fun i => Function.surjInv hs (v i)
      have hx : ∀ i, f (x i) = v i := fun i => Function.surjInv_eq hs _
      set a : M := ∑ i, x i • m i
      have hra : ∀ i, m.repr a i = x i := by
        intro i
        simp [a, Finsupp.single_apply]
      have hzero : ∀ b, e a b = 0 := by
        intro b
        rw [hexp, Finset.sum_comm]
        refine Finset.sum_eq_zero fun j _ => ?_
        have hj : (v ᵥ* G) j = 0 := congrFun hv j
        simp only [vecMul, dotProduct] at hj
        calc ∑ i, f (m.repr a i) * f (m.repr b j) * G i j
            = f (m.repr b j) * ∑ i, v i * G i j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hra, hx]
              ring
          _ = 0 := by rw [hj, mul_zero]
      obtain ⟨a', ha'⟩ := he0 a hzero
      funext i
      rw [Pi.zero_apply, ← hx, ← hra, ha', map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
        toZModPow_p_pow_self, zero_mul]
    have hinj : Function.Injective fun v : ι → ZMod (p ^ n) => v ᵥ* G := by
      intro v w hvw
      exact sub_eq_zero.1 (hinj0 (v - w) (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 hvw))
    exact (Matrix.isUnit_iff_isUnit_det G).1
      (Matrix.vecMul_surjective_iff_isUnit.1 (Finite.injective_iff_surjective.1 hinj))
  · ext i j
    have h1 := he (m i) (m j)
    rw [hexp] at h1
    rw [Matrix.smul_apply, smul_eq_mul, ← h1]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      LinearMap.toMatrix_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring

omit [DecidableEq ι] in
/-- **From equivariant pairings at every finite level to the Gram identity on `M ⊗ ℚ_p`.** Let
`M` be a free `ℤ_p`-module with a finite basis and `φ` an endomorphism. If for every `n` there is
a biadditive pairing on `M` with values in `ℤ/pⁿ`, nondegenerate on the left modulo `pⁿ M` and
with `e(φ a, φ b) = c e(a, b)`, then for every basis `b` of `V = M ⊗ ℚ_p` there is a matrix `J`
with unit determinant and `Aᵀ J A = c J`, `A` the matrix of `φ ⊗ ℚ_p` in `b`. -/
theorem exists_isUnit_det_transpose_mul_mul_eq_smul_extendScalars {M : ModuleCat.{v} ℤ_[p]}
    (m : Module.Basis ι ℤ_[p] M) (φ : M ⟶ M) (c : ℕ)
    (h : ∀ n : ℕ, ∃ e : M →+ M →+ ZMod (p ^ n),
      (∀ a, (∀ b, e a b = 0) → ∃ a', a = (p : ℤ_[p]) ^ n • a') ∧
        ∀ a b, e (φ.hom a) (φ.hom b) = (c : ZMod (p ^ n)) * e a b)
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (bV : Module.Basis ι' ℚ_[p]
      ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).obj M)) :
    ∃ J : Matrix ι' ι' ℚ_[p], IsUnit J.det ∧
      (LinearMap.toMatrix bV bV
          ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map φ).hom)ᵀ *
          J * LinearMap.toMatrix bV bV
            ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map φ).hom =
        (c : ℚ_[p]) • J := by
  classical
  obtain ⟨J, hJ, hA⟩ := exists_isUnit_det_transpose_mul_mul_eq_smul_of_forall_zmodPow
    (LinearMap.toMatrix m m φ.hom) c fun n => by
      obtain ⟨e, he0, he⟩ := h n
      exact exists_gram_zmodPow_of_pairing m φ.hom c n e he0 he
  let b₀ : Module.Basis ι ℚ_[p]
      ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).obj M) :=
    Algebra.TensorProduct.basis ℚ_[p] m
  have hmat : LinearMap.toMatrix b₀ b₀
      ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map φ).hom =
      (LinearMap.toMatrix m m φ.hom).map (algebraMap ℤ_[p] ℚ_[p]) :=
    LinearMap.toMatrix_baseChange ℚ_[p] φ.hom m m
  have hdet : IsUnit (J.map (algebraMap ℤ_[p] ℚ_[p])).det := by
    have := hJ.map (algebraMap ℤ_[p] ℚ_[p])
    rwa [RingHom.map_det] at this
  have hid : (LinearMap.toMatrix b₀ b₀
      ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map φ).hom)ᵀ *
      J.map (algebraMap ℤ_[p] ℚ_[p]) * LinearMap.toMatrix b₀ b₀
        ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map φ).hom =
        (c : ℚ_[p]) • J.map (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [hmat, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hA]
    ext i j
    simp
  exact exists_isUnit_det_transpose_mul_mul_eq_smul_of_basis b₀
    ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map φ).hom (c : ℚ_[p])
    (J.map (algebraMap ℤ_[p] ℚ_[p])) hdet hid bV

end Padic

end Stacks.EtaleCohomology

end
