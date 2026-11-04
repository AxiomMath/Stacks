module

public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.MonoidAlgebra.Ideal
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic

/-!
# An epimorphism of zero-dimensional local rings which is not surjective

Over `𝔽₂`, let `A = k[x₀, x₁, …, z₀, z₁, …]` modulo the relations `xᵢ^{4^i} = zᵢ^{4^i} = 0` and
let `B = k[x₀, x₁, …, y₀, y₁, …]` modulo `xᵢ^{4^i} = 0` and `yᵢ = x_{i+1} y_{i+1}^2`. Both are
local of Krull dimension zero, and the map `A → B` sending `xᵢ` to `xᵢ` and `zᵢ` to `xᵢ yᵢ` is a
local epimorphism of rings which is not surjective: `y₀` is not in its image.

That the map is an epimorphism is checked through the tensor criterion `1 ⊗ b = b ⊗ 1` in
`B ⊗_A B`: the relation `yᵢ = x_{i+1} y_{i+1}^2` lets one move `yᵢ` across the tensor sign using
that `x_{i+1}` and `x_{i+1} y_{i+1}` both come from `A`. That `y₀` is not in the image is seen in
a monomial model `WeightRing`: monomials are graded by a nonnegative rational recording
nilpotence together with an integer recording the grading in which `x` has degree `-1` and `y`
degree `1`, and monomials of rational weight at least `1` are set to zero. Every element coming
from `A` has all its integer weights `≤ 0`, whereas `y₀` has integer weight `1`.

## Main results

* `Stacks.Examples.exists_epi_localRing_not_surjective`: the two local rings and their
  nonsurjective epimorphism.

## Implementation notes

The epimorphism is categorical in `CommRingCat`; both rings have Krull dimension zero and the
homomorphism is local, and its failure to be surjective refers to the underlying function. The
construction lives in the namespace `Stacks.Examples.EpiNotSurjective`.

## References

* [Stacks Project, Tag 06RI](https://stacks.math.columbia.edu/tag/06RI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Examples.EpiNotSurjective

noncomputable section

private abbrev Poly (k : Type u) [CommRing k] := MvPolynomial (ℕ ⊕ ℕ) k

private abbrev Coeff : Type u := ULift.{u} (ZMod 2)

private def srcIdeal (k : Type u) [CommRing k] : Ideal (Poly k) :=
  Ideal.span
    (Set.range (fun i : ℕ => (MvPolynomial.X (Sum.inl i : ℕ ⊕ ℕ) : Poly k) ^ (4 ^ i)) ∪
      Set.range (fun i : ℕ => (MvPolynomial.X (Sum.inr i : ℕ ⊕ ℕ) : Poly k) ^ (4 ^ i)))

private def tgtIdeal (k : Type u) [CommRing k] : Ideal (Poly k) :=
  Ideal.span
    (Set.range (fun i : ℕ => (MvPolynomial.X (Sum.inl i : ℕ ⊕ ℕ) : Poly k) ^ (4 ^ i)) ∪
      Set.range (fun i : ℕ => (MvPolynomial.X (Sum.inr i : ℕ ⊕ ℕ) : Poly k) -
        MvPolynomial.X (Sum.inl (i + 1) : ℕ ⊕ ℕ) *
          (MvPolynomial.X (Sum.inr (i + 1) : ℕ ⊕ ℕ)) ^ 2))

private abbrev Source (k : Type u) [CommRing k] := (Poly k) ⧸ srcIdeal k
private abbrev Target (k : Type u) [CommRing k] := (Poly k) ⧸ tgtIdeal k

private def xSrc {k : Type u} [CommRing k] (i : ℕ) : Source k :=
  Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i : ℕ ⊕ ℕ))

private def zSrc {k : Type u} [CommRing k] (i : ℕ) : Source k :=
  Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr i : ℕ ⊕ ℕ))

private def xTgt {k : Type u} [CommRing k] (i : ℕ) : Target k :=
  Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i : ℕ ⊕ ℕ))

private def yTgt {k : Type u} [CommRing k] (i : ℕ) : Target k :=
  Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr i : ℕ ⊕ ℕ))

private def evalTargetZero {k : Type u} [CommRing k] : Poly k →+* k :=
  (MvPolynomial.aeval fun _ => (0 : k)).toRingHom

private def varIdeal (k : Type u) [CommRing k] : Ideal (Poly k) :=
  Ideal.span (Set.range fun i : ℕ ⊕ ℕ => (MvPolynomial.X i : Poly k))

private def constHom {k : Type u} [CommRing k] : k →+* Poly k :=
  MvPolynomial.C

private def constPoly {k : Type u} [CommRing k] (a : k) : Poly k := constHom a

private lemma poly_sub_const_eval_mem_varIdeal {k : Type u} [CommRing k] (p : Poly k) :
    p - constPoly (evalTargetZero (k := k) p) ∈ varIdeal k := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have heval : evalTargetZero (MvPolynomial.C (σ := ℕ ⊕ ℕ) a) = a := by
        simp [evalTargetZero]
      rw [heval]
      change (constHom a - constHom a) ∈ varIdeal k
      simp
  | add p q hp hq =>
      have heval : evalTargetZero p + evalTargetZero q =
          evalTargetZero (p + q) := (map_add _ _ _).symm
      have hC : constPoly (evalTargetZero (p + q)) =
          constPoly (evalTargetZero p) + constPoly (evalTargetZero q) := by
        simp [constPoly, constHom]
      rw [hC]
      convert (varIdeal k).add_mem hp hq using 1
      ring
  | mul_X p i hp =>
      have hXi : MvPolynomial.X i ∈ varIdeal k :=
        Ideal.subset_span ⟨i, rfl⟩
      simpa [evalTargetZero, constPoly, constHom] using (varIdeal k).mul_mem_left p hXi

private lemma prime_eq_varIdeal {k : Type u} [Field k] {P : Ideal (Poly k)}
    (hP : P.IsPrime) (hX : ∀ i : ℕ ⊕ ℕ, MvPolynomial.X i ∈ P) : P = varIdeal k := by
  have hvar : varIdeal k ≤ P := Ideal.span_le.mpr (Set.range_subset_iff.mpr hX)
  refine le_antisymm (fun p hp => ?_) hvar
  have hconst : constPoly (evalTargetZero p) ∈ P := by
    simpa using P.sub_mem hp (hvar (poly_sub_const_eval_mem_varIdeal p))
  have heval : evalTargetZero p = 0 := by
    by_contra hne
    have hu : IsUnit (constPoly (evalTargetZero p)) :=
      ((isUnit_iff_ne_zero).2 hne).map (constHom (k := k))
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hconst hu)
  simpa [heval, constPoly, constHom] using poly_sub_const_eval_mem_varIdeal p

private def evalQuotient {k : Type u} [CommRing k] (I : Ideal (Poly k))
    (hI : I ≤ RingHom.ker (evalTargetZero (k := k))) : (Poly k ⧸ I) →+* k :=
  Ideal.Quotient.lift I (evalTargetZero (k := k)) hI

private lemma quotient_nontrivial {k : Type u} [Field k] (I : Ideal (Poly k))
    (hI : I ≤ RingHom.ker (evalTargetZero (k := k))) : Nontrivial (Poly k ⧸ I) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h01
  have hmem : (1 : Poly k) ∈ I := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change Ideal.Quotient.mk I (1 : Poly k) = 0
    simpa using h01.symm
  simpa [evalTargetZero] using hI hmem

private lemma quotient_has_unique_prime {k : Type u} [Field k] (I : Ideal (Poly k))
    (hI : I ≤ RingHom.ker (evalTargetZero (k := k)))
    (hpow : ∀ i : ℕ ⊕ ℕ, ∃ n, 0 < n ∧ (MvPolynomial.X i : Poly k) ^ n ∈ I) :
    ∃! P : Ideal (Poly k ⧸ I), P.IsPrime := by
  let π : Poly k →+* (Poly k ⧸ I) := Ideal.Quotient.mk I
  let ev : (Poly k ⧸ I) →+* k := evalQuotient I hI
  have hcomap (Q : Ideal (Poly k ⧸ I)) (hQ : Q.IsPrime) : Ideal.comap π Q = varIdeal k := by
    refine prime_eq_varIdeal (Ideal.comap_isPrime π Q) fun i => ?_
    obtain ⟨n, -, hmem⟩ := hpow i
    refine (Ideal.comap_isPrime π Q).mem_of_pow_mem n ?_
    rw [Ideal.mem_comap, (Ideal.Quotient.eq_zero_iff_mem).2 hmem]
    exact Q.zero_mem
  refine ⟨RingHom.ker ev, RingHom.ker_isPrime ev, fun Q hQ => ?_⟩
  exact (Ideal.comap_injective_of_surjective π Ideal.Quotient.mk_surjective)
    ((hcomap Q hQ).trans (hcomap _ (RingHom.ker_isPrime ev)).symm)

private lemma tgtIdeal_le_ker_evalTargetZero {k : Type u} [CommRing k] :
    tgtIdeal k ≤ RingHom.ker (evalTargetZero (k := k)) := by
  change Ideal.span _ ≤ _
  apply Ideal.span_le.mpr
  rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> simp [evalTargetZero]

end

private lemma srcIdeal_le_ker_evalTargetZero {k : Type u} [CommRing k] :
    srcIdeal k ≤ RingHom.ker (evalTargetZero (k := k)) := by
  change Ideal.span _ ≤ _
  apply Ideal.span_le.mpr
  rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> simp [evalTargetZero]

private lemma src_powers_mem (k : Type u) [CommRing k] :
    ∀ i : ℕ ⊕ ℕ, ∃ n, 0 < n ∧ (MvPolynomial.X i : Poly k) ^ n ∈ srcIdeal k := by
  intro i
  cases i with
  | inl i => exact ⟨4 ^ i, by positivity, Ideal.subset_span (Or.inl ⟨i, rfl⟩)⟩
  | inr i => exact ⟨4 ^ i, by positivity, Ideal.subset_span (Or.inr ⟨i, rfl⟩)⟩

/-- In the target, `xᵢ ^ (4 ^ i)` vanishes. -/
private lemma xTgt_pow_eq_zero {k : Type u} [CommRing k] (i : ℕ) :
    (xTgt (k := k) i) ^ (4 ^ i) = 0 :=
  (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span (Or.inl ⟨i, rfl⟩))

/-- In the target, `yᵢ = x_{i+1} y_{i+1} ^ 2`. -/
private lemma yTgt_eq {k : Type u} [CommRing k] (i : ℕ) :
    yTgt (k := k) i = xTgt (k := k) (i + 1) * (yTgt (k := k) (i + 1)) ^ 2 :=
  (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := tgtIdeal k) _ _).2
    (Ideal.subset_span (Or.inr ⟨i, rfl⟩))

private lemma tgt_powers_mem (k : Type u) [CommRing k] :
    ∀ i : ℕ ⊕ ℕ, ∃ n, 0 < n ∧ (MvPolynomial.X i : Poly k) ^ n ∈ tgtIdeal k := by
  intro i
  cases i with
  | inl i => exact ⟨4 ^ i, by positivity, Ideal.subset_span (Or.inl ⟨i, rfl⟩)⟩
  | inr i =>
      refine ⟨4 ^ (i + 1), by positivity, ?_⟩
      have hyN : (yTgt (k := k) i) ^ (4 ^ (i + 1)) = 0 := by
        rw [yTgt_eq, mul_pow, xTgt_pow_eq_zero, zero_mul]
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hyN

private lemma source_has_unique_prime {k : Type u} [Field k] :
    ∃! P : Ideal (Source k), P.IsPrime :=
  quotient_has_unique_prime (srcIdeal k) (srcIdeal_le_ker_evalTargetZero (k := k))
    (src_powers_mem k)

private lemma target_has_unique_prime {k : Type u} [Field k] :
    ∃! P : Ideal (Target k), P.IsPrime :=
  quotient_has_unique_prime (tgtIdeal k) (tgtIdeal_le_ker_evalTargetZero (k := k))
    (tgt_powers_mem k)

private lemma source_local_dim {k : Type u} [Field k] :
    ringKrullDim (Source k) = 0 ∧ IsLocalRing (Source k) := by
  have : Nontrivial (Source k) :=
    quotient_nontrivial (srcIdeal k) (srcIdeal_le_ker_evalTargetZero (k := k))
  let hpair :=
    ((Ring.krullDimLE_zero_and_isLocalRing_tfae (Source k)).out 1 2 rfl rfl).mpr
      (source_has_unique_prime (k := k))
  exact ⟨(ringKrullDimZero_iff_ringKrullDim_eq_zero (R := Source k)).mp hpair.1, hpair.2⟩

private lemma target_local_dim {k : Type u} [Field k] :
    ringKrullDim (Target k) = 0 ∧ IsLocalRing (Target k) := by
  have : Nontrivial (Target k) :=
    quotient_nontrivial (tgtIdeal k) (tgtIdeal_le_ker_evalTargetZero (k := k))
  let hpair :=
    ((Ring.krullDimLE_zero_and_isLocalRing_tfae (Target k)).out 1 2 rfl rfl).mpr
      (target_has_unique_prime (k := k))
  exact ⟨(ringKrullDimZero_iff_ringKrullDim_eq_zero (R := Target k)).mp hpair.1, hpair.2⟩

private noncomputable def sourcePolyToTarget {k : Type u} [CommRing k] :
    Poly k →ₐ[k] Target k :=
  MvPolynomial.aeval fun i : ℕ ⊕ ℕ =>
    match i with
    | Sum.inl n => xTgt (k := k) n
    | Sum.inr n => xTgt (k := k) n * yTgt (k := k) n

private lemma srcIdeal_le_ker_sourcePolyToTarget {k : Type u} [CommRing k] :
    srcIdeal k ≤ RingHom.ker (sourcePolyToTarget (k := k)).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · change (sourcePolyToTarget (k := k)).toRingHom
      ((MvPolynomial.X (Sum.inl i : ℕ ⊕ ℕ) : Poly k) ^ (4 ^ i)) = 0
    rw [map_pow]
    simpa [sourcePolyToTarget] using xTgt_pow_eq_zero (k := k) i
  · change (sourcePolyToTarget (k := k)).toRingHom
      ((MvPolynomial.X (Sum.inr i : ℕ ⊕ ℕ) : Poly k) ^ (4 ^ i)) = 0
    rw [map_pow]
    simpa [sourcePolyToTarget] using (show
      (xTgt (k := k) i * yTgt (k := k) i) ^ (4 ^ i) = 0 by
        simp [mul_pow, xTgt_pow_eq_zero])

private lemma sourcePolyToTarget_C {k : Type u} [CommRing k] (a : k) :
    sourcePolyToTarget (k := k) (MvPolynomial.C (σ := ℕ ⊕ ℕ) a) =
      Ideal.Quotient.mk (tgtIdeal k) (MvPolynomial.C (σ := ℕ ⊕ ℕ) a) := by
  rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  simp [sourcePolyToTarget]

private noncomputable def epiExampleMap {k : Type u} [CommRing k] : Source k →+* Target k :=
  Ideal.Quotient.lift (srcIdeal k) (sourcePolyToTarget (k := k)).toRingHom
    (srcIdeal_le_ker_sourcePolyToTarget (k := k))

private lemma epiExampleMap_mk {k : Type u} [CommRing k] (p : Poly k) :
    epiExampleMap (k := k) (Ideal.Quotient.mk (srcIdeal k) p) =
      sourcePolyToTarget (k := k) p := by
  simp [epiExampleMap]

private lemma epiExampleMap_x {k : Type u} [CommRing k] (i : ℕ) :
    epiExampleMap (k := k) (xSrc (k := k) i) = xTgt (k := k) i := by
  simp [xSrc, epiExampleMap_mk, sourcePolyToTarget]

private lemma epiExampleMap_z {k : Type u} [CommRing k] (i : ℕ) :
    epiExampleMap (k := k) (zSrc (k := k) i) = xTgt (k := k) i * yTgt (k := k) i := by
  simp [zSrc, epiExampleMap_mk, sourcePolyToTarget]

private noncomputable instance exampleAlgebra {k : Type u} [CommRing k] :
    Algebra (Source k) (Target k) := (epiExampleMap (k := k)).toAlgebra

private lemma tensor_base_eq {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    (a : R) :
    (1 : B) ⊗ₜ[R] algebraMap R B a = algebraMap R B a ⊗ₜ[R] (1 : B) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (TensorProduct.smul_tmul a (1 : B) (1 : B)).symm

private lemma example_y_tensor_eq {k : Type u} [CommRing k] (i : ℕ) :
    (1 : Target k) ⊗ₜ[Source k] yTgt (k := k) i =
      yTgt (k := k) i ⊗ₜ[Source k] (1 : Target k) := by
  let x := xTgt (k := k) (i + 1)
  let y := yTgt (k := k) (i + 1)
  let z₀ := zSrc (k := k) (i + 1)
  let z := algebraMap (Source k) (Target k) z₀
  have hx : algebraMap (Source k) (Target k) (xSrc (k := k) (i + 1)) = x :=
    epiExampleMap_x (i + 1)
  have hz : z = x * y := epiExampleMap_z (i + 1)
  have hy : yTgt (k := k) i = x * y ^ 2 := yTgt_eq i
  have hbalz : (y * z) ⊗ₜ[Source k] (1 : Target k) = y ⊗ₜ[Source k] z := by
    simpa [Algebra.smul_def, z, mul_comm] using
      (TensorProduct.smul_tmul (R := Source k) z₀ y (1 : Target k))
  have hxy : y ⊗ₜ[Source k] x = (x * y) ⊗ₜ[Source k] (1 : Target k) := by
    simpa [Algebra.smul_def, hx, mul_comm] using
      (TensorProduct.smul_tmul (R := Source k) (xSrc (k := k) (i + 1)) y
        (1 : Target k)).symm
  have hmid : y ⊗ₜ[Source k] z = z ⊗ₜ[Source k] y := by
    calc
      y ⊗ₜ[Source k] z = y ⊗ₜ[Source k] (x * y) := by rw [hz]
      _ = (y ⊗ₜ[Source k] x) * ((1 : Target k) ⊗ₜ[Source k] y) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      _ = ((x * y) ⊗ₜ[Source k] (1 : Target k)) *
          ((1 : Target k) ⊗ₜ[Source k] y) := by rw [hxy]
      _ = z ⊗ₜ[Source k] y := by
        rw [hz]
        simp [Algebra.TensorProduct.tmul_mul_tmul]
  have hbalz' : z ⊗ₜ[Source k] y = (1 : Target k) ⊗ₜ[Source k] (z * y) := by
    calc
      z ⊗ₜ[Source k] y = (z ⊗ₜ[Source k] (1 : Target k)) *
          ((1 : Target k) ⊗ₜ[Source k] y) := by simp
      _ = ((1 : Target k) ⊗ₜ[Source k] z) *
          ((1 : Target k) ⊗ₜ[Source k] y) := by
            rw [tensor_base_eq (R := Source k) (B := Target k) z₀]
      _ = (1 : Target k) ⊗ₜ[Source k] (z * y) := by simp
  rw [hy, show x * y ^ 2 = y * z by rw [hz]; ring, hbalz, hmid, hbalz', mul_comm z y]


private lemma tensor_one_mul {R B : Type*} [CommSemiring R] [CommSemiring B]
    [Algebra R B] (a b : B) :
    (1 : B) ⊗ₜ[R] (a * b) = ((1 : B) ⊗ₜ[R] a) * ((1 : B) ⊗ₜ[R] b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  simp

private lemma tensor_mul_one {R B : Type*} [CommSemiring R] [CommSemiring B]
    [Algebra R B] (a b : B) :
    (a * b) ⊗ₜ[R] (1 : B) = (a ⊗ₜ[R] (1 : B)) * (b ⊗ₜ[R] (1 : B)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  simp

private lemma target_tensor_eq_all {k : Type u} [CommRing k] :
    ∀ b : Target k, (1 : Target k) ⊗ₜ[Source k] b = b ⊗ₜ[Source k] (1 : Target k) := by
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hC : Ideal.Quotient.mk (tgtIdeal k) (MvPolynomial.C (σ := ℕ ⊕ ℕ) a) =
          algebraMap (Source k) (Target k)
            (Ideal.Quotient.mk (srcIdeal k) (MvPolynomial.C (σ := ℕ ⊕ ℕ) a)) := by
        exact ((epiExampleMap_mk _).trans (sourcePolyToTarget_C a)).symm
      rw [hC]
      exact tensor_base_eq _
  | add p q hp hq =>
      rw [map_add, TensorProduct.tmul_add, TensorProduct.add_tmul, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, tensor_one_mul, tensor_mul_one, hp]
      congr 1
      cases i with
      | inl i =>
          have hX : algebraMap (Source k) (Target k) (xSrc (k := k) i) =
              Ideal.Quotient.mk (tgtIdeal k) (MvPolynomial.X (Sum.inl i)) := epiExampleMap_x i
          rw [← hX]
          exact tensor_base_eq _
      | inr i => simpa [yTgt] using example_y_tensor_eq (k := k) i

private lemma example_isEpi {k : Type u} [CommRing k] : Algebra.IsEpi (Source k) (Target k) :=
  (Algebra.isEpi_iff_forall_one_tmul_eq (Source k) (Target k)).mpr target_tensor_eq_all

private lemma exampleMap_isLocalHom {k : Type u} [Field k] :
    IsLocalHom (epiExampleMap (k := k)) := by
  let hs := source_local_dim (k := k)
  let ht := target_local_dim (k := k)
  have : IsLocalRing (Source k) := hs.2
  have : IsLocalRing (Target k) := ht.2
  have : Ring.KrullDimLE 0 (Source k) :=
    (ringKrullDimZero_iff_ringKrullDim_eq_zero (R := Source k)).mpr hs.1
  have : Ring.KrullDimLE 0 (Target k) :=
    (ringKrullDimZero_iff_ringKrullDim_eq_zero (R := Target k)).mpr ht.1
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  obtain ⟨n, hn⟩ := ((Ring.KrullDimLE.isNilpotent_iff_mem_nonunits (R := Source k)).2 hna).map
    (epiExampleMap (k := k))
  exact not_isUnit_zero (hn ▸ ha.pow n : IsUnit (0 : Target k))

private lemma example_cat_epi {k : Type u} [CommRing k] :
    Epi (CommRingCat.ofHom (epiExampleMap (k := k))) := by
  let : Algebra (Source k) (Target k) := exampleAlgebra (k := k)
  exact (CommRingCat.epi_iff_epi).2 example_isEpi

/-! A monomial model detects that `y₀` is not in the image.  The rational
weight records nilpotence, and the integer weight records the grading from
Stacks 06RH. -/

private abbrev Weight := {q : ℚ // 0 ≤ q} × ℤ

private noncomputable abbrev WeightAlg := AddMonoidAlgebra Coeff Weight

private def bigWeightSet : Set Weight := {w | (1 : ℚ) ≤ w.1.1}

private noncomputable def bigWeightIdeal : Ideal WeightAlg :=
  Ideal.span (AddMonoidAlgebra.of' Coeff Weight '' bigWeightSet)

private abbrev WeightRing := WeightAlg ⧸ bigWeightIdeal

private def xWeight (i : ℕ) : Weight :=
  (⟨((4 : ℚ) ^ i)⁻¹, by positivity⟩, -1)

private def yWeight (i : ℕ) : Weight :=
  (⟨(((4 : ℚ) ^ i)⁻¹) / 2, by positivity⟩, 1)

private noncomputable def weightMon (w : Weight) : WeightRing :=
  Ideal.Quotient.mk _ (AddMonoidAlgebra.single w (1 : Coeff))

private lemma bigWeight_monomial_mem {w : Weight} (hw : (1 : ℚ) ≤ w.1.1) :
    AddMonoidAlgebra.single w (1 : Coeff) ∈ bigWeightIdeal := by
  rw [← AddMonoidAlgebra.of'_apply]
  exact Ideal.subset_span (Set.mem_image_of_mem _ hw)

private lemma weightMon_eq_zero {w : Weight} (hw : (1 : ℚ) ≤ w.1.1) :
    weightMon w = 0 :=
  (Ideal.Quotient.eq_zero_iff_mem).2 (bigWeight_monomial_mem hw)

private lemma weightMon_mul (v w : Weight) :
    weightMon v * weightMon w = weightMon (v + w) := by
  change Ideal.Quotient.mk bigWeightIdeal
      (AddMonoidAlgebra.single v (1 : Coeff) * AddMonoidAlgebra.single w 1) = _
  rw [AddMonoidAlgebra.single_mul_single]
  simp [weightMon]

private lemma weightMon_pow (w : Weight) (n : ℕ) :
    (weightMon w) ^ n = weightMon (n • w) := by
  induction n with
  | zero =>
      simp only [pow_zero, zero_nsmul]
      change (1 : WeightRing) = Ideal.Quotient.mk bigWeightIdeal
        (AddMonoidAlgebra.single (0 : Weight) (1 : Coeff))
      rw [← map_one (Ideal.Quotient.mk bigWeightIdeal : WeightAlg →+* WeightRing)]
      rfl
  | succ n ih =>
      rw [pow_succ, ih, weightMon_mul]
      congr 1
      rw [succ_nsmul]

private noncomputable def targetWeightPoly : Poly Coeff →+* WeightRing :=
  (MvPolynomial.aeval fun i : ℕ ⊕ ℕ =>
    match i with
    | Sum.inl n => weightMon (xWeight n)
    | Sum.inr n => weightMon (yWeight n)).toRingHom

private lemma xWeight_power_killed (i : ℕ) :
    (weightMon (xWeight i)) ^ (4 ^ i) = 0 := by
  rw [weightMon_pow]
  apply weightMon_eq_zero
  change 1 ≤ (4 ^ i : ℕ) • (((4 : ℚ) ^ i)⁻¹)
  rw [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_inv_cancel₀ (pow_ne_zero i four_ne_zero)]

private lemma yWeight_relation (i : ℕ) :
    yWeight i = xWeight (i + 1) + yWeight (i + 1) + yWeight (i + 1) := by
  apply Prod.ext
  · apply Subtype.ext
    change ((4 : ℚ) ^ i)⁻¹ / 2 = ((4 : ℚ) ^ (i + 1))⁻¹ +
      (((4 : ℚ) ^ (i + 1))⁻¹ / 2) + (((4 : ℚ) ^ (i + 1))⁻¹ / 2)
    rw [pow_succ]
    field_simp
    ring
  · simp [xWeight, yWeight]

private lemma targetWeightPoly_kills_tgtIdeal :
    tgtIdeal Coeff ≤ RingHom.ker targetWeightPoly := by
  apply Ideal.span_le.mpr
  rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · change targetWeightPoly
      ((MvPolynomial.X (Sum.inl i : ℕ ⊕ ℕ) : Poly Coeff) ^ (4 ^ i)) = 0
    rw [map_pow]
    simpa [targetWeightPoly] using xWeight_power_killed i
  · change targetWeightPoly
      ((MvPolynomial.X (Sum.inr i : ℕ ⊕ ℕ) : Poly Coeff) -
        MvPolynomial.X (Sum.inl (i + 1) : ℕ ⊕ ℕ) *
          (MvPolynomial.X (Sum.inr (i + 1) : ℕ ⊕ ℕ)) ^ 2) = 0
    suffices hsub : weightMon (yWeight i) -
        weightMon (xWeight (i + 1)) * weightMon (yWeight (i + 1)) ^ 2 = 0 by
      simpa [targetWeightPoly] using hsub
    rw [weightMon_pow, two_nsmul, weightMon_mul, ← add_assoc, ← yWeight_relation,
      sub_self]

private noncomputable def targetWeightMap : Target Coeff →+* WeightRing :=
  Ideal.Quotient.lift (tgtIdeal Coeff) targetWeightPoly
    (targetWeightPoly_kills_tgtIdeal)

private lemma targetWeightMap_y (i : ℕ) :
    targetWeightMap (yTgt (k := Coeff) i) = weightMon (yWeight i) := by
  simp [targetWeightMap, yTgt, targetWeightPoly]

private lemma targetWeightMap_x (i : ℕ) :
    targetWeightMap (xTgt (k := Coeff) i) = weightMon (xWeight i) := by
  simp [targetWeightMap, xTgt, targetWeightPoly]

private noncomputable def sourceWeightPoly : Poly Coeff →+* WeightAlg :=
  (MvPolynomial.aeval fun i : ℕ ⊕ ℕ =>
    match i with
    | Sum.inl n => AddMonoidAlgebra.single (xWeight n) (1 : Coeff)
    | Sum.inr n => AddMonoidAlgebra.single (xWeight n + yWeight n) (1 : Coeff)).toRingHom

private lemma sourceWeightPoly_support (p : Poly Coeff) :
    ∀ w ∈ (sourceWeightPoly p).coeff.support, w.2 ≤ 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      intro w hw
      have hw' : (AddMonoidAlgebra.single (0 : Weight) a).coeff w ≠ 0 := by
        simpa [sourceWeightPoly] using hw
      have hw0 : w = 0 := by
        by_contra hne
        exact hw' (by simp [hne])
      subst w
      norm_num
  | add p q hp hq =>
      intro w hw
      rw [map_add] at hw
      rcases Finset.mem_union.mp (Finsupp.support_add hw) with h | h
      exacts [hp w h, hq w h]
  | mul_X p i hp =>
      intro w hw
      rw [map_mul] at hw
      have hsubset := AddMonoidAlgebra.support_coeff_mul_subset
        (sourceWeightPoly p)
        (sourceWeightPoly (MvPolynomial.X i))
      have hw' := hsubset hw
      rcases Finset.mem_image₂.mp hw' with ⟨a, ha, b, hb, rfl⟩
      have hpa := hp a ha
      cases i with
      | inl n =>
          simp [sourceWeightPoly] at hb
          subst b
          simp [xWeight] at *
          omega
      | inr n =>
          simp [sourceWeightPoly] at hb
          subst b
          have hdeg : (xWeight n + yWeight n).2 = 0 := by
            simp [xWeight, yWeight]
          simp [hdeg, hpa]

private lemma weightMon_y0_not_in_source (p : Poly Coeff) :
    weightMon (yWeight 0) ≠ Ideal.Quotient.mk bigWeightIdeal (sourceWeightPoly p) := by
  intro heq
  have hmem :
      AddMonoidAlgebra.single (yWeight 0) (1 : Coeff) - sourceWeightPoly p ∈
        bigWeightIdeal := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change Ideal.Quotient.mk bigWeightIdeal
      (AddMonoidAlgebra.single (yWeight 0) (1 : Coeff) - sourceWeightPoly p) = 0
    simpa [weightMon] using sub_eq_zero.mpr heq
  have hsupport := (AddMonoidAlgebra.mem_ideal_span_of'_image).mp hmem
  have he : yWeight 0 ∈
      (AddMonoidAlgebra.single (yWeight 0) (1 : Coeff) - sourceWeightPoly p).coeff.support := by
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.mem_support_iff]
    have hcoef : (sourceWeightPoly p).coeff (yWeight 0) = 0 := by
      by_contra h
      have hdeg := sourceWeightPoly_support p (yWeight 0) (Finsupp.mem_support_iff.mpr h)
      norm_num [yWeight] at hdeg
    simp [hcoef]
  obtain ⟨v, hv, d, hdecomp⟩ := hsupport (yWeight 0) he
  have hvq : (1 : ℚ) ≤ v.1.1 := hv
  have hq := congrArg (fun z : Weight => z.1.val) hdecomp
  change (yWeight 0).1.1 = d.1.1 + v.1.1 at hq
  have hdq : 0 ≤ d.1.1 := d.1.2
  have hyq : (yWeight 0).1.1 = 1 / 2 := by norm_num [yWeight, xWeight]
  rw [hyq] at hq
  linarith

private noncomputable def sourceWeightQuotientPoly : Poly Coeff →+* WeightRing :=
  (Ideal.Quotient.mk bigWeightIdeal).comp sourceWeightPoly

private lemma target_sourceWeight_agree (p : Poly Coeff) :
    targetWeightMap (sourcePolyToTarget (k := Coeff) p) =
      sourceWeightQuotientPoly p := by
  have h : targetWeightMap.comp (sourcePolyToTarget (k := Coeff)).toRingHom =
      sourceWeightQuotientPoly := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply]
      change targetWeightMap (sourcePolyToTarget (MvPolynomial.C a)) =
        sourceWeightQuotientPoly (MvPolynomial.C a)
      rw [sourcePolyToTarget_C]
      calc
        targetWeightMap (Ideal.Quotient.mk (tgtIdeal Coeff) (MvPolynomial.C a)) =
            targetWeightPoly (MvPolynomial.C a) := rfl
        _ = algebraMap Coeff WeightRing a := by
          simp only [targetWeightPoly, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            MvPolynomial.aeval_C]
        _ = sourceWeightQuotientPoly (MvPolynomial.C a) := by
          simp only [sourceWeightQuotientPoly, RingHom.comp_apply, sourceWeightPoly]
          rw [← Ideal.Quotient.mk_algebraMap (I := bigWeightIdeal) (x := a)]
          congr 1
          simp [AddMonoidAlgebra.coe_algebraMap]
    · intro i
      cases i with
      | inl n =>
          simp [sourceWeightQuotientPoly, sourceWeightPoly, sourcePolyToTarget,
            targetWeightMap_x, weightMon]
      | inr n =>
          simpa [sourceWeightQuotientPoly, sourceWeightPoly, sourcePolyToTarget,
            targetWeightMap_x, targetWeightMap_y, weightMon] using
            weightMon_mul (xWeight n) (yWeight n)
  exact RingHom.congr_fun h p

private lemma exampleMap_not_surjective :
    ¬ Function.Surjective (epiExampleMap (k := Coeff)) := by
  intro hs
  obtain ⟨a, ha⟩ := hs (yTgt (k := Coeff) 0)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have heq := congrArg targetWeightMap ha
  rw [epiExampleMap_mk, target_sourceWeight_agree, targetWeightMap_y] at heq
  exact weightMon_y0_not_in_source p heq.symm

end Stacks.Examples.EpiNotSurjective

namespace Stacks.Examples

open EpiNotSurjective

/-- **Stacks 06RI.** There is a nonsurjective epimorphism of zero-dimensional local
rings. -/
@[stacks 06RI]
theorem exists_epi_localRing_not_surjective :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : IsLocalRing A) (_ : IsLocalRing B) (f : A →+* B),
      ringKrullDim A = 0 ∧
        ringKrullDim B = 0 ∧
        IsLocalHom f ∧
        Epi (CommRingCat.ofHom f) ∧
        ¬ Function.Surjective f := by
  let k := Coeff
  let A := Source k
  let B := Target k
  exact ⟨A, B, inferInstance, inferInstance, (source_local_dim (k := k)).2,
    (target_local_dim (k := k)).2, epiExampleMap (k := k), (source_local_dim (k := k)).1,
    (target_local_dim (k := k)).1, exampleMap_isLocalHom (k := k), example_cat_epi (k := k),
    exampleMap_not_surjective⟩

end Stacks.Examples

end
