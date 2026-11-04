module

public import StacksFrontier.AlgebraicGeometry.Curves.Node.Multicross
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.TotalFractionRing
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Defs
public import StacksFrontier.RingTheory.PowerSeries.IntegrallyClosed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The delta invariant of a multicross ring

The delta invariant of the `n`-branch multicross ring over a field is `n - 1`.

## Main results

* `Stacks.Curves.deltaInvariant_multicross_eq_sub_one` computes the delta invariant of the
  `n`-branch multicross ring for every `n`.

## Implementation notes

The normalization of `multicross k n` is the full product `Fin n → k[[t]]`.  This is obtained
from the general description of the integral closure of a reduced ring in its total ring of
fractions as the product over the minimal primes (Tag 035P): the minimal primes of the
multicross ring are the kernels of the `n` coordinate projections, each quotient is `k[[t]]`,
which is already integrally closed, and reindexing the resulting product by `Fin n` gives the
claim.

With the normalization identified, the delta invariant is the length of
`(Fin n → k[[t]]) / multicross k n`.  For `n = m + 1` the constant-coefficient map identifies
that quotient with `(Fin (m + 1) → k) / k` for the diagonal copy of `k`, whose length is `m`
because the diagonal is a line in an `(m + 1)`-dimensional space; the base change from
`multicross k (m + 1)` to `k` is legitimate because the constant-coefficient map onto `k` is
surjective.  For `n = 0` the product is a subsingleton and both sides are zero.

Scalars are a recurring nuisance here: the quotient whose length is taken is a module over the
multicross ring, not over `k`, so each identification has to be made `multicross`-linearly and
the change of base ring performed explicitly by `Module.length_eq_of_surjective`.

## References

* [Stacks Project, Tag 0C1V](https://stacks.math.columbia.edu/tag/0C1V)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Curves

/-- The diagonal embedding of `k[[t]]` into the multicross ring: the same series in every
branch. -/
private def multicrossDiag (k : Type u) [Field k] (n : ℕ) :
    PowerSeries k →+* ↥(multicross k n) :=
  (RingHom.pi fun _ : Fin n => RingHom.id (PowerSeries k)).codRestrict
    (multicross k n) (by
      intro p
      rw [mem_multicross]
      simp)

/-- The `i`-th branch of an element of the multicross ring. -/
private def multicrossProjection (k : Type u) [Field k] (n : ℕ) (i : Fin n) :
    ↥(multicross k n) →+* PowerSeries k :=
  (Pi.evalRingHom (fun _ : Fin n => PowerSeries k) i).comp
    (multicross k n).subtype

private theorem multicrossProjection_surjective (k : Type u) [Field k] (n : ℕ)
    (i : Fin n) : Function.Surjective (multicrossProjection k n i) :=
  fun p => ⟨multicrossDiag k n p, rfl⟩

/-- The variable in one branch and zero in the others separates that branch's kernel from any
other. -/
private theorem exists_mem_multicrossProjection_ker_not (k : Type u) [Field k]
    (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    ∃ x : ↥(multicross k n),
      x ∈ RingHom.ker (multicrossProjection k n j) ∧
        x ∉ RingHom.ker (multicrossProjection k n i) := by
  let f : Fin n → PowerSeries k := fun l => if l = i then PowerSeries.X else 0
  have hf : f ∈ multicross k n := by
    rw [mem_multicross]
    intro a b
    dsimp [f]
    split_ifs <;> simp [PowerSeries.constantCoeff_X]
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · show f j = 0
    simp [f, hij.symm]
  · show f i ≠ 0
    simp [f]

/-- The minimal primes of the multicross ring are the kernels of the branch projections. -/
private theorem minimalPrimes_multicross_eq_range_projectionKernel
    (k : Type u) [Field k] (n : ℕ) :
    minimalPrimes ↥(multicross k n) =
      Set.range (fun i : Fin n => RingHom.ker (multicrossProjection k n i)) := by
  let P : Fin n → Ideal ↥(multicross k n) :=
    fun i => RingHom.ker (multicrossProjection k n i)
  have hprime (i : Fin n) : (P i).IsPrime := RingHom.ker_isPrime _
  have hinf : Finset.univ.inf P = (⊥ : Ideal ↥(multicross k n)) := by
    apply le_antisymm
    · intro x hx
      apply Subtype.ext
      funext i
      have hle : Finset.univ.inf P ≤ P i :=
        Finset.inf_le (s := Finset.univ) (f := P) (b := i) (Finset.mem_univ i)
      have hxi : x ∈ P i := hle hx
      have hxmap : (multicrossProjection k n i) x = 0 := RingHom.mem_ker.mp hxi
      simpa [P, multicrossProjection] using hxmap
    · exact bot_le
  have hminimal (i : Fin n) : P i ∈ minimalPrimes ↥(multicross k n) := by
    show (⊥ : Ideal ↥(multicross k n)).IsMinimalPrime (P i)
    refine ⟨⟨hprime i, bot_le⟩, ?_⟩
    intro q hq hqi
    have hle : Finset.univ.inf P ≤ q := by rw [hinf]; exact bot_le
    obtain ⟨j, -, hj⟩ := hq.1.inf_le'.mp hle
    by_cases hji : j = i
    · subst j
      exact hj
    · obtain ⟨x, hxj, hxi⟩ :=
        exists_mem_multicrossProjection_ker_not k n (i := i) (j := j) (Ne.symm hji)
      exact False.elim (hxi (hqi (hj hxj)))
  refine Set.Subset.antisymm (fun q hq => ?_) (Set.range_subset_iff.2 hminimal)
  have hle : Finset.univ.inf P ≤ q := by rw [hinf]; exact bot_le
  obtain ⟨i, -, hi⟩ := hq.1.1.inf_le'.mp hle
  exact ⟨i, le_antisymm hi (hq.2 ⟨hprime i, bot_le⟩ hi)⟩

private theorem minimalPrimes_multicross_finite (k : Type u) [Field k] (n : ℕ) :
    (minimalPrimes ↥(multicross k n)).Finite := by
  rw [minimalPrimes_multicross_eq_range_projectionKernel]
  exact Set.finite_range _

private theorem multicrossProjectionKernel_injective (k : Type u) [Field k]
    (n : ℕ) : Function.Injective
      (fun i : Fin n => RingHom.ker (multicrossProjection k n i)) := by
  intro i j hij
  by_contra hne
  obtain ⟨x, hxj, hxi⟩ :=
    exists_mem_multicrossProjection_ker_not k n (i := i) (j := j) hne
  exact hxi (by simpa only [hij] using hxj)

/-- The branches index the minimal primes of the multicross ring. -/
private def multicrossMinimalPrimesEquiv (k : Type u) [Field k]
    (n : ℕ) : Fin n ≃ minimalPrimes ↥(multicross k n) :=
  Equiv.ofBijective
    (fun i => (⟨RingHom.ker (multicrossProjection k n i), by
      rw [minimalPrimes_multicross_eq_range_projectionKernel]
      exact Set.mem_range_self i⟩ : minimalPrimes ↥(multicross k n)))
    (by
      constructor
      · intro i j hij
        exact multicrossProjectionKernel_injective k n (congrArg Subtype.val hij)
      · intro p
        obtain ⟨i, hi⟩ := (minimalPrimes_multicross_eq_range_projectionKernel k n).le p.2
        exact ⟨i, Subtype.ext hi⟩)

/-- Each branch quotient of the multicross ring is `k[[t]]`. -/
private def multicrossQuotientEquiv (k : Type u) [Field k]
    (n : ℕ) (i : Fin n) :
    ↥(multicross k n) ⧸ RingHom.ker (multicrossProjection k n i) ≃+*
      PowerSeries k :=
  RingHom.quotientKerEquivOfSurjective (multicrossProjection_surjective k n i)

/-- The same identification, indexed by the minimal prime rather than by the branch. -/
private def multicrossMinimalPrimeQuotientEquiv
    (k : Type u) [Field k] (n : ℕ)
    (p : minimalPrimes ↥(multicross k n)) :
    ↥(multicross k n) ⧸ (p : Ideal ↥(multicross k n)) ≃+*
      PowerSeries k := by
  let i := (multicrossMinimalPrimesEquiv k n).symm p
  have hi : (p : Ideal ↥(multicross k n)) =
      RingHom.ker (multicrossProjection k n i) :=
    (congrArg Subtype.val ((multicrossMinimalPrimesEquiv k n).apply_symm_apply p)).symm
  exact (Ideal.quotEquivOfEq hi).trans (multicrossQuotientEquiv k n i)

/-- `k[[t]]` is integrally closed, so the integral closure of a branch quotient in its fraction
field is the quotient itself. -/
private def multicrossMinimalPrimeIntegralClosureEquiv
    (k : Type u) [Field k] (n : ℕ)
    (p : minimalPrimes ↥(multicross k n)) :
    let Q := ↥(multicross k n) ⧸ (p : Ideal ↥(multicross k n))
    ↥(integralClosure Q (FractionRing Q)) ≃+* PowerSeries k := by
  let Q := ↥(multicross k n) ⧸ (p : Ideal ↥(multicross k n))
  let eQ := multicrossMinimalPrimeQuotientEquiv k n p
  let : IsIntegrallyClosed Q := IsIntegrallyClosed.of_equiv eQ.symm
  exact (IsIntegralClosure.equiv Q ↥(integralClosure Q (FractionRing Q))
    (FractionRing Q) Q).toRingEquiv.trans eQ

/-- **The normalization of the `n`-branch multicross ring is `Fin n → k[[t]]`.** -/
private def multicrossNormalizationEquiv
    (k : Type u) [Field k] (n : ℕ) :
    ↥(integralClosure ↥(multicross k n)
        (FractionRing ↥(multicross k n))) ≃+*
      (Fin n → PowerSeries k) := by
  let M := multicross k n
  let : IsReduced ↥M :=
    isReduced_of_injective M.subtype Subtype.val_injective
  let : (p : minimalPrimes ↥M) →
      Algebra ↥M
        ↥(integralClosure (↥M ⧸ (p : Ideal ↥M))
          (FractionRing (↥M ⧸ (p : Ideal ↥M)))) :=
    fun p =>
      ((algebraMap (↥M ⧸ (p : Ideal ↥M))
        ↥(integralClosure (↥M ⧸ (p : Ideal ↥M))
          (FractionRing (↥M ⧸ (p : Ideal ↥M))))).comp
        (Ideal.Quotient.mk (p : Ideal ↥M))).toAlgebra
  let eNorm := Classical.choice
    (minimalPrimes.integralClosure_fractionRing_algEquiv_pi_quotient
      (A := ↥M) (minimalPrimes_multicross_finite k n))
  let eFactor := RingEquiv.piCongrRight
    (fun p : minimalPrimes ↥M => multicrossMinimalPrimeIntegralClosureEquiv k n p)
  let eIndex := RingEquiv.piCongrLeft'
    (fun _ : minimalPrimes ↥M => PowerSeries k)
    (multicrossMinimalPrimesEquiv k n).symm
  exact eNorm.toRingEquiv.trans (eFactor.trans eIndex)

/-- The normalization isomorphism is the identity on the multicross ring itself. -/
private theorem multicrossNormalizationEquiv_apply_algebraMap
    (k : Type u) [Field k] (n : ℕ) (m : ↥(multicross k n)) :
    multicrossNormalizationEquiv k n
        (algebraMap ↥(multicross k n)
          ↥(integralClosure ↥(multicross k n)
            (FractionRing ↥(multicross k n))) m) = m.1 := by
  funext i
  simp only [multicrossNormalizationEquiv, Set.mem_ofPred_eq,
    multicrossMinimalPrimeIntegralClosureEquiv, multicrossMinimalPrimeQuotientEquiv,
    multicrossProjection, multicrossQuotientEquiv, RingEquiv.coe_trans, RingEquiv.coe_mk,
    AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Function.comp_apply, AlgEquiv.commutes,
    RingEquiv.piCongrLeft'_apply, Equiv.symm_symm, RingEquiv.piCongrRight_apply,
    Pi.algebraMap_apply]
  let M := multicross k n
  let p := (multicrossMinimalPrimesEquiv k n) i
  let Q := ↥M ⧸ (p : Ideal ↥M)
  let T := ↥(integralClosure Q (FractionRing Q))
  let : IsIntegrallyClosed Q :=
    IsIntegrallyClosed.of_equiv (multicrossMinimalPrimeQuotientEquiv k n p).symm
  let : Algebra ↥M T :=
    ((algebraMap Q T).comp (Ideal.Quotient.mk (p : Ideal ↥M))).toAlgebra
  let eQ := multicrossMinimalPrimeQuotientEquiv k n p
  let eC := IsIntegralClosure.equiv Q T (FractionRing Q) Q
  show eQ (eC (algebraMap ↥M T m)) = m.1 i
  have hmap : algebraMap ↥M T m =
      algebraMap Q T (Ideal.Quotient.mk (p : Ideal ↥M) m) := rfl
  rw [hmap, eC.commutes]
  show eQ ((Ideal.Quotient.mk (p : Ideal ↥M)) m) = m.1 i
  let j := (multicrossMinimalPrimesEquiv k n).symm p
  have hi : (p : Ideal ↥M) = RingHom.ker (multicrossProjection k n j) :=
    (congrArg Subtype.val ((multicrossMinimalPrimesEquiv k n).apply_symm_apply p)).symm
  show (multicrossQuotientEquiv k n j)
    ((Ideal.quotEquivOfEq hi) ((Ideal.Quotient.mk (p : Ideal ↥M)) m)) = m.1 i
  rw [Ideal.quotEquivOfEq_mk]
  rw [show (multicrossQuotientEquiv k n j)
      ((Ideal.Quotient.mk (RingHom.ker (multicrossProjection k n j))) m) =
        multicrossProjection k n j m from
    RingHom.quotientKerEquivOfSurjective_apply_mk
      (multicrossProjection_surjective k n j) m]
  have hj : j = i := by simp [j, p]
  show multicrossProjection k n j m = m.1 i
  rw [hj]
  rfl

/-- The normalization of the multicross ring, as an algebra over it. -/
private def multicrossNormalizationAlgEquiv
    (k : Type u) [Field k] (n : ℕ) :
    let M := multicross k n
    let : Algebra ↥M (Fin n → PowerSeries k) := M.subtype.toAlgebra
    ↥(integralClosure ↥M (FractionRing ↥M)) ≃ₐ[↥M] (Fin n → PowerSeries k) := by
  let M := multicross k n
  let : Algebra ↥M (Fin n → PowerSeries k) := M.subtype.toAlgebra
  exact { multicrossNormalizationEquiv k n with
    commutes' := multicrossNormalizationEquiv_apply_algebraMap k n }

/-- The delta invariant of the multicross ring is the length of the product of the branches
modulo the multicross ring itself. -/
private theorem deltaInvariant_multicross_eq_length_productQuotient
    (k : Type u) [Field k] (n : ℕ) :
    let M := multicross k n
    let P := Fin n → PowerSeries k
    let : Algebra ↥M P := M.subtype.toAlgebra
    Ring.deltaInvariant ↥M =
      Module.length ↥M (P ⧸ LinearMap.range (Algebra.linearMap ↥M P)) := by
  let M := multicross k n
  let P := Fin n → PowerSeries k
  let : Algebra ↥M P := M.subtype.toAlgebra
  let C := ↥(integralClosure ↥M (FractionRing ↥M))
  let e := multicrossNormalizationAlgEquiv k n
  have hcomp : e.toLinearEquiv.toLinearMap.comp (Algebra.linearMap ↥M C) =
      Algebra.linearMap ↥M P :=
    LinearMap.ext fun m => e.commutes m
  have hmap : Submodule.map e.toLinearEquiv.toLinearMap
      (LinearMap.range (Algebra.linearMap ↥M C)) =
        LinearMap.range (Algebra.linearMap ↥M P) := by
    rw [← LinearMap.range_comp, hcomp]
  let eQ :
      (C ⧸ LinearMap.range (Algebra.linearMap ↥M C)) ≃ₗ[↥M]
        (P ⧸ LinearMap.range (Algebra.linearMap ↥M P)) := Submodule.Quotient.equiv
    (LinearMap.range (Algebra.linearMap ↥M C))
    (LinearMap.range (Algebra.linearMap ↥M P)) e.toLinearEquiv hmap
  show Module.length ↥M (C ⧸ LinearMap.range (Algebra.linearMap ↥M C)) =
    Module.length ↥M (P ⧸ LinearMap.range (Algebra.linearMap ↥M P))
  let : AddCommGroup C := (inferInstance : CommRing C).toAddCommGroup
  exact eQ.length_eq

/-- The common constant coefficient of an element of a nonempty multicross ring. -/
private def multicrossConstantCoeff (k : Type u) [Field k] (n : ℕ) :
    ↥(multicross k (n + 1)) →+* k :=
  PowerSeries.constantCoeff.comp
    (multicrossProjection k (n + 1) (Fin.last n))

private theorem multicrossConstantCoeff_surjective (k : Type u) [Field k]
    (n : ℕ) : Function.Surjective (multicrossConstantCoeff k n) :=
  fun a => ⟨multicrossDiag k (n + 1) (PowerSeries.C a), by
    simp [multicrossConstantCoeff, multicrossProjection, multicrossDiag]⟩

/-- Every branch of an element of the multicross ring has the same constant coefficient. -/
private theorem constantCoeff_apply_eq_multicrossConstantCoeff (k : Type u) [Field k] (n : ℕ)
    (a : ↥(multicross k (n + 1))) (i : Fin (n + 1)) :
    PowerSeries.constantCoeff (a.1 i) = multicrossConstantCoeff k n a := by
  simpa [multicrossConstantCoeff, multicrossProjection] using
    (mem_multicross a.1).mp a.2 i (Fin.last n)

/-- Taking the constant coefficient in every branch, as a map of modules over the multicross
ring. -/
private def multicrossProductConstantCoeffLinear (k : Type u) [Field k]
    (n : ℕ) :
    let M := multicross k (n + 1)
    let P := Fin (n + 1) → PowerSeries k
    let : Algebra ↥M P := M.subtype.toAlgebra
    let : Module ↥M P := (M.subtype.toAlgebra).toModule
    let : Algebra ↥M k := (multicrossConstantCoeff k n).toAlgebra
    let : Module ↥M k := ((multicrossConstantCoeff k n).toAlgebra).toModule
    let : Module ↥M (Fin (n + 1) → k) :=
      Module.compHom (Fin (n + 1) → k) (multicrossConstantCoeff k n)
    P →ₗ[↥M] (Fin (n + 1) → k) := by
  let M := multicross k (n + 1)
  let P := Fin (n + 1) → PowerSeries k
  let : Algebra ↥M P := M.subtype.toAlgebra
  let : Module ↥M P := (M.subtype.toAlgebra).toModule
  let : Algebra ↥M k := (multicrossConstantCoeff k n).toAlgebra
  let : Module ↥M k := ((multicrossConstantCoeff k n).toAlgebra).toModule
  let : Module ↥M (Fin (n + 1) → k) :=
    Module.compHom (Fin (n + 1) → k) (multicrossConstantCoeff k n)
  exact
    { toFun := fun p i => PowerSeries.constantCoeff (p i)
      map_add' := by
        intro p q
        funext i
        simp
      map_smul' := by
        intro a p
        funext i
        simp only [Algebra.smul_def, Pi.mul_apply]
        change PowerSeries.constantCoeff (a.1 i * p i) =
          multicrossConstantCoeff k n a * PowerSeries.constantCoeff (p i)
        rw [map_mul, constantCoeff_apply_eq_multicrossConstantCoeff] }

/-- An `(n + 1)`-dimensional space modulo its diagonal line has length `n`. -/
private theorem length_quotient_diagonal (k : Type u) [Field k] (n : ℕ) :
    Module.length k
      ((Fin (n + 1) → k) ⧸
        (LinearMap.const (R := k) (ι := Fin (n + 1)) :
          k →ₗ[k] Fin (n + 1) → k).range) = n := by
  let d : k →ₗ[k] (Fin (n + 1) → k) := LinearMap.const
  have hinj : Function.Injective d := fun a b hab => congrFun hab (Fin.last n)
  have hd : Module.finrank k d.range = 1 := by
    simpa using (LinearEquiv.ofInjective d hinj).finrank_eq.symm
  have hpi : Module.finrank k (Fin (n + 1) → k) = n + 1 := by
    simp
  have h := Submodule.finrank_quotient_add_finrank d.range
  rw [hd, hpi] at h
  have hfin : Module.finrank k ((Fin (n + 1) → k) ⧸ d.range) = n := by omega
  rw [Module.length_eq_finrank, hfin]

/-- The product of the branches of a nonempty multicross ring, modulo the multicross ring, has
length `n`. -/
private theorem length_multicross_product_quotient (k : Type u) [Field k]
    (n : ℕ) :
    let M := multicross k (n + 1)
    let P := Fin (n + 1) → PowerSeries k
    let : Algebra ↥M P := M.subtype.toAlgebra
    let : Module ↥M P := (M.subtype.toAlgebra).toModule
    Module.length ↥M (P ⧸ LinearMap.range (Algebra.linearMap ↥M P)) = n := by
  let M := multicross k (n + 1)
  let P := Fin (n + 1) → PowerSeries k
  let K := Fin (n + 1) → k
  let : Algebra ↥M P := M.subtype.toAlgebra
  let : Module ↥M P := (M.subtype.toAlgebra).toModule
  let ρ := multicrossConstantCoeff k n
  let : Algebra ↥M k := ρ.toAlgebra
  let : Module ↥M k := (ρ.toAlgebra).toModule
  let : Module ↥M K := Module.compHom K ρ
  let d : k →ₗ[k] K := LinearMap.const
  let V := K ⧸ d.range
  let : Module ↥M V := Module.compHom V ρ
  let : SMul ↥M P := (inferInstance : Module ↥M P).toSMul
  let : SMul ↥M V := (inferInstance : Module ↥M V).toSMul
  let c := multicrossProductConstantCoeffLinear k n
  let q : P →ₗ[↥M] V :=
    { toFun := fun p => d.range.mkQ (c p)
      map_add' := by
        intro p p'
        simp
      map_smul' := by
        intro a p
        show d.range.mkQ (c (a • p)) = d.range.mkQ (ρ a • c p)
        exact congrArg d.range.mkQ (c.map_smul a p) }
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective d.range y
    refine ⟨(fun i => PowerSeries.C (b i)), ?_⟩
    simp [q, c, multicrossProductConstantCoeffLinear]
  have hker : q.ker = LinearMap.range (Algebra.linearMap ↥M P) := by
    ext p
    constructor
    · intro hp
      have hd : c p ∈ d.range :=
        (Submodule.Quotient.mk_eq_zero d.range).mp (LinearMap.mem_ker.mp hp)
      obtain ⟨a, ha⟩ := hd
      have hm : p ∈ multicross k (n + 1) := by
        rw [mem_multicross]
        intro i j
        calc
          PowerSeries.constantCoeff (p i) = d a i := by
            simpa [c, multicrossProductConstantCoeffLinear] using (congrFun ha i).symm
          _ = d a j := rfl
          _ = PowerSeries.constantCoeff (p j) := by
            simpa [c, multicrossProductConstantCoeffLinear] using congrFun ha j
      exact ⟨⟨p, hm⟩, rfl⟩
    · rintro ⟨m, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply (Submodule.Quotient.mk_eq_zero d.range).mpr
      refine ⟨ρ m, ?_⟩
      funext i
      exact (constantCoeff_apply_eq_multicrossConstantCoeff k n m i).symm
  have hlen := ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    (q.quotKerEquivOfSurjective hsurj)).length_eq
  rw [Module.length_eq_of_surjective (S := ↥M) (R := k) (M := V)
    (multicrossConstantCoeff_surjective k n)] at hlen
  exact hlen.trans (length_quotient_diagonal k n)

/-- **The delta invariant of the `n`-branch multicross ring is `n - 1`**, for every `n`.  This
is the general-`n` form of the computation; `Stacks.Curves.deltaInvariant_multicross` is the
case `n = 2`. -/
@[sga "7 X 2.24" "more general"]
theorem deltaInvariant_multicross_eq_sub_one (k : Type u) [Field k] (n : ℕ) :
    Ring.deltaInvariant ↥(multicross k n) = (n : ℕ∞) - 1 := by
  rw [deltaInvariant_multicross_eq_length_productQuotient]
  cases n with
  | zero =>
      have : Subsingleton (Fin 0 → PowerSeries k) := inferInstance
      simp
  | succ n =>
      rw [length_multicross_product_quotient k n]
      exact_mod_cast (Nat.add_one_sub_one n).symm

end Stacks.Curves

end
