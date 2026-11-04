module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import StacksCore.Algebra.QuadraticAlgebra.Standard
public import StacksCore.FieldTheory.Separable
public import StacksCore.FieldTheory.SeparableDegree
import StacksCore.RingTheory.Polynomial.Resultant.Basic

/-! # Quadratic Extensions

In this file we prove that every quadratic extension (defined to be a free algebra of rank 2)
is isomorphic to some `QuadraticAlgebra R a b`.

-/

@[expose] public section

open Module TensorProduct Polynomial

namespace QuadraticAlgebra

/-- The power basis `{1, ω}` of `QuadraticAlgebra R a b` over `R`, with generator `ω`. -/
@[simps (isSimp := false) gen dim basis]
noncomputable abbrev powerBasis {R : Type*} [CommRing R] (a b : R) :
    PowerBasis R (QuadraticAlgebra R a b) where
  gen := omega
  dim := 2
  basis := basis a b
  basis_eq_pow := by simp [QuadraticAlgebra.ext_iff, basis]

attribute [simp] powerBasis_gen

variable {R : Type*} [CommRing R] (a b : R)

/-- The minimal-polynomial generator of `powerBasis a b` is `X ^ 2 - b * X - a`. -/
theorem minpolyGen_powerBasis : (powerBasis a b).minpolyGen = X ^ 2 - C b * X - C a := by
  unfold PowerBasis.minpolyGen
  rw [Fin.sum_univ_two]
  rw [basis_repr_apply]
  simp only [sq, Nat.succ_eq_add_one, Nat.reduceAdd, omega_mul_omega_eq_add, re_add, re_smul,
    re_one, smul_eq_mul, mul_one, re_omega, mul_zero, add_zero, im_add, im_smul, im_one, im_omega,
    zero_add, Fin.isValue, Matrix.cons_val_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.mod_succ, pow_one]
  ring

/-- The minimal polynomial of `ω` over `R` is `X ^ 2 - b * X - a`. -/
theorem minpoly_omega :
    minpoly R (omega : QuadraticAlgebra R a b) = X ^ 2 - C b * X - C a := by
  rw [← powerBasis_gen, ← PowerBasis.minpolyGen_eq, minpolyGen_powerBasis]

/-- The natural degree of the minimal polynomial of `ω` is `2`. -/
@[simp] theorem natDegree_minpoly_omega [Nontrivial R] :
    (minpoly R (omega : QuadraticAlgebra R a b)).natDegree = 2 := by
  rw [minpoly_omega]
  compute_degree!

/-- The degree of the minimal polynomial of `ω` is `2`. -/
@[simp] theorem degree_minpoly_omega [Nontrivial R] :
    (minpoly R (omega : QuadraticAlgebra R a b)).degree = 2 := by
  rw [minpoly_omega]
  compute_degree!

/-- If `QuadraticAlgebra R a b` is a domain, then no `x : R` satisfies `x^2 = a + b * x`,
i.e. the polynomial `X^2 - b*X - a` has no root in `R`. -/
theorem not_root_of_domain [IsDomain (QuadraticAlgebra R a b)] (x : R) : x ^ 2 ≠ a + b * x := by
  have := QuadraticAlgebra.algebraMap_injective.isDomain (algebraMap R (QuadraticAlgebra R a b))
  intro hx
  have key : (x • 1 - omega : QuadraticAlgebra R a b) * ((x - b) • 1 + omega) = 0 := by
    ext <;> simp; grind
  simp [mul_eq_zero, QuadraticAlgebra.ext_iff] at key

/-- In characteristic two, the generator `ω : QuadraticAlgebra R a b` is separable over `R`
iff `b` is a unit. -/
theorem isSeparable_omega_iff_of_char_two {R : Type*} [CommRing R] [CharP R 2] (a b : R) :
    IsSeparable R (omega : QuadraticAlgebra R a b) ↔ IsUnit b := by
  nontriviality R
  rw [IsSeparable, (minpoly.monic (Algebra.IsIntegral.isIntegral _)).separable_iff_isUnit_resultant,
    natDegree_minpoly_omega, minpoly_omega]
  simp_rw [map_sub, derivative_X_pow, Nat.cast_two, CharTwo.two_eq_zero]
  simp +contextual

/-- When `2 ≠ 0` in `R`, the generator `ω : QuadraticAlgebra R a b` is separable over `R`
iff the discriminant `b ^ 2 + 4 * a` is a unit. -/
theorem isSeparable_omega_iff_of_two_ne_zero {R : Type*} [CommRing R] [NeZero (2 : R)] (a b : R) :
    IsSeparable R (omega : QuadraticAlgebra R a b) ↔ IsUnit (b ^ 2 + 4 * a) := by
  nontriviality R
  rw [IsSeparable, (minpoly.monic (Algebra.IsIntegral.isIntegral _)).separable_iff_isUnit_discr,
    minpoly_omega, discr_of_degree_eq_two]
  · simp
  · compute_degree!
  · simp [NeZero.ne]

/-- Over a field `K`, the algebra `QuadraticAlgebra K a b` is separable iff the generator `ω`
is separable. -/
theorem isSeparable_iff_omega {K : Type*} [Field K] (a b : K) :
    Algebra.IsSeparable K (QuadraticAlgebra K a b) ↔
      IsSeparable K (omega : QuadraticAlgebra K a b) := by
  refine ⟨fun h ↦ h.isSeparable _ _, fun h ↦ ⟨fun ⟨x, y⟩ ↦ ?_⟩⟩
  rw [mk_eq_add_smul_omega, add_comm]
  exact (h.smul _).add_algebraMap _

/-- Over a field `K`, the algebra `QuadraticAlgebra K a b` is purely inseparable iff the
generator `ω` is not separable. -/
theorem isPurelyInseparable_iff_not_isSeparable_omega {K : Type*} [Field K] (a b : K) :
    IsPurelyInseparable K (QuadraticAlgebra K a b) ↔
      ¬IsSeparable K (omega : QuadraticAlgebra K a b) := by
  refine ⟨fun h hω ↦ by simpa [QuadraticAlgebra.ext_iff] using h.inseparable _ _ hω,
    fun hω ↦ ⟨inferInstance, fun ⟨x, y⟩ hz ↦ ?_⟩⟩
  suffices y = 0 from this ▸ ⟨x, rfl⟩
  by_contra! hy
  refine hω ?_
  convert (hz.add_algebraMap (-x)).smul y⁻¹
  ext <;> simp [hy]

end QuadraticAlgebra

open QuadraticAlgebra

namespace Algebra.IsQuadraticExtension

attribute [simp] finrank_eq_two

/-- Base change of a quadratic extension along `R → S` is again a quadratic extension. -/
instance baseChange (R S A : Type*)
    [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R S] [Algebra R A]
    [StrongRankCondition R] [StrongRankCondition S]
    [IsQuadraticExtension R A] : IsQuadraticExtension S (S ⊗[R] A) where
  finrank_eq_two' := by simp

/-- Each `QuadraticAlgebra R a b` over a nontrivial commutative ring is a quadratic extension
of `R`. -/
instance quadraticAlgebra (R : Type*) [CommRing R] [Nontrivial R] (a b : R) :
    IsQuadraticExtension R (QuadraticAlgebra R a b) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two a b

/-- Every quadratic extension `S` of a nontrivial commutative ring `R` is `R`-algebra
isomorphic to some `QuadraticAlgebra R a b`. -/
theorem exists_algEquiv
    (R S : Type*) [CommRing R] [Nontrivial R] [Ring S] [Algebra R S] [IsQuadraticExtension R S] :
    ∃ a b : R, Nonempty (S ≃ₐ[R] QuadraticAlgebra R a b) := by
  let b := finBasisOfFinrankEq R S (finrank_eq_two R S)
  let v := b.repr 1
  have hbv : v 0 • b 0 + v 1 • b 1 = 1 := by
    simpa [v, Fin.sum_univ_two, -Basis.sum_repr] using b.sum_repr 1
  have hv : IsCoprime (v 0) (v 1) := by
    rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq, ← Ideal.span_union,
      Set.singleton_union]
    by_contra! hv
    obtain ⟨M, _, hM⟩ := Ideal.exists_le_maximal _ hv
    have : Nontrivial ((R ⧸ M) ⊗[R] S) := (finrank_pos_iff_of_free (R ⧸ M) ..).mp (by simp)
    refine one_ne_zero (α := (R ⧸ M) ⊗[R] S) ?_
    rw [← (b.baseChange (R ⧸ M)).repr.injective.eq_iff, map_zero, TensorProduct.one_def]
    simp_rw [Finsupp.ext_iff, Finsupp.zero_apply, Fin.forall_fin_two,
      b.baseChange_repr_tmul (R ⧸ M), ← algebraMap_eq_smul_one,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨hM <| Ideal.subset_span (by simp [v]), hM <| Ideal.subset_span (by simp [v])⟩
  obtain ⟨p, q, hpq⟩ := hv
  let M := !![v 0, -q; v 1, p]
  let M' := !![p, q; -v 1, v 0]
  have hMM' : M * M' = 1 := by
    simp only [Fin.isValue, Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
      Matrix.vecMul_cons, Matrix.head_cons, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty,
      Matrix.tail_cons, neg_smul, mul_neg, Matrix.neg_cons, neg_neg, Matrix.neg_empty,
      Matrix.empty_vecMul, add_zero, Matrix.add_cons, Matrix.empty_add_empty, Matrix.empty_mul,
      Equiv.symm_apply_apply, Matrix.one_fin_two, EmbeddingLike.apply_eq_iff_eq, Matrix.vecCons_inj,
      and_true, M, M']
    grind
  have hM'M : M' * M = 1 := mul_eq_one_comm.mp hMM'
  let e := Matrix.toLin'OfInv hMM' hM'M
  let b' := Basis.ofEquivFun <| b.equivFun.trans e
  have hb' : b' 0 = 1 := by simp [b', e, M, hbv]
  let pb : PowerBasis R S := ⟨b' 1, 2, b', by simp [hb']⟩
  obtain ⟨hbm, hbd⟩ : (minpoly R (b' 1)).Monic ∧ (minpoly R (b' 1)).natDegree = 2 :=
    ⟨minpoly.monic <| Algebra.IsIntegral.isIntegral _, pb.natDegree_minpoly⟩
  obtain ⟨t, u, htu⟩ := isMonicOfDegree_two_iff.mp ⟨hbd, hbm⟩
  exact ⟨-u, -t, ⟨pb.equivOfMinpoly (powerBasis _ _) <| by
    simpa [pb, minpoly_omega]⟩⟩

/-- **Stacks 0BIN** (characteristic two case).
A quadratic field extension `L/K` of a field of characteristic two is either purely inseparable
of the form `K[√a]` for a non-square `a` (with `discr' K L = 0`), or separable of the form
`K[X]/(X^2 + X - a)` for some `a ∈ K` not of the form `x(x+1)` (with `discr' K L = 1`). -/
@[stacks 0BIN "characteristic two case"]
theorem of_field_char_two (K L : Type*) [Field K] [Field L] [Algebra K L]
    [CharP K 2] [IsQuadraticExtension K L] :
    (discr' K L = 0 ∧ IsPurelyInseparable K L ∧
      ∃ a : K, ¬IsSquare a ∧ Nonempty (L ≃ₐ[K] QuadraticAlgebra K a 0)) ∨
    (discr' K L = 1 ∧ Algebra.IsSeparable K L ∧
      ∃ a : K, (∀ x : K, x * (x + 1) ≠ a) ∧ Nonempty (L ≃ₐ[K] QuadraticAlgebra K a 1)) := by
  obtain ⟨a, b, ⟨e⟩⟩ := exists_algEquiv K L
  rw [e.discr'_eq, discr'_eq, show (4 : K) = 2 * 2 by grind,
    CharTwo.two_eq_zero (R := K), zero_mul, zero_mul, add_zero]
  refine (eq_or_ne b 0).imp ?_ fun hb ↦ ?_
  · rintro rfl
    have := e.symm.toMulEquiv.isDomain
    have := not_root_of_domain a 0
    refine ⟨by simp, ?_, a, ?_, ⟨e⟩⟩
    · simp [e.isPurelyInseparable_iff, isPurelyInseparable_iff_not_isSeparable_omega,
        isSeparable_omega_iff_of_char_two]
    · simpa [IsSquare, sq, eq_comm]
  · have e' := (scaleUnit a b (.mk0 (b⁻¹) (by simpa))).trans (congr rfl (show _ = 1 by simp [hb]))
    generalize _ * a = a at e'
    have := (e.trans e').symm.toMulEquiv.isDomain
    have := not_root_of_domain a 1
    refine ⟨?_, ?_, a, ?_, ⟨e.trans e'⟩⟩
    · rw [← Units.val_mk0 hb, map_pow, QuotSq.mk_unit_sq]
    · rw [AlgEquiv.Algebra.isSeparable_iff (e.trans e'), isSeparable_iff_omega]
      simp [isSeparable_omega_iff_of_char_two]
    · simp_rw [ne_eq, ← sub_eq_zero (b := _ + _)] at this
      simp_rw [ne_eq, ← sub_eq_zero (b := a)]
      convert this using 3
      simp only [CharTwo.sub_eq_add, one_mul]
      ring

/-- **Stacks 0BIN** (characteristic not two case).
A quadratic field extension `L/K` over a field with `2 ≠ 0` is automatically separable,
its discriminant class is neither `0` nor `1`, and `L` is `K`-isomorphic to `K[√a]` for some
non-square `a ∈ K`. -/
@[stacks 0BIN "characteristic not two case"]
theorem of_field_two_ne_zero (K L : Type*) [Field K] [Field L] [Algebra K L]
    [NeZero (2 : K)] [IsQuadraticExtension K L] :
    discr' K L ≠ 0 ∧ discr' K L ≠ 1 ∧ Algebra.IsSeparable K L ∧
      ∃ a : K, ¬IsSquare a ∧ Nonempty (L ≃ₐ[K] QuadraticAlgebra K a 0) := by
  obtain ⟨a, b, ⟨e⟩⟩ := exists_algEquiv K L
  have e' := (translate a b (b / 2)).trans (congr rfl (show _ = 0 by field_simp; simp))
  generalize (_ - _ : K) = a at e'
  replace e := e.trans e'
  rw [e.discr'_eq, discr'_eq, show 0 ^ 2 + 4 * a = (.mk0 2 (NeZero.ne 2) : Kˣ) ^ 2 * a by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, Units.val_mk0,
      mul_eq_mul_right_iff]
    grind, map_mul, map_pow, QuotSq.mk_unit_sq, one_mul, ne_eq,
    ← and_assoc, QuotSq.mk_ne_zero_and_one_iff_not_isSquare,
    AlgEquiv.Algebra.isSeparable_iff e, isSeparable_iff_omega, isSeparable_omega_iff_of_two_ne_zero,
    isUnit_iff_ne_zero]
  have := e.symm.toMulEquiv.isDomain
  have ha : ¬IsSquare a := by simpa [IsSquare, eq_comm, sq] using not_root_of_domain a 0
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  exact ⟨ha, by simp [ha0, show (4 : K) = 2 * 2 by grind, NeZero.ne], a, ha, ⟨e⟩⟩

end Algebra.IsQuadraticExtension
