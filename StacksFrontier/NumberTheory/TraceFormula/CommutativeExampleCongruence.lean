module

public import Mathlib.Algebra.Group.Pi.Units
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.ProcyclicTrivialTrace
public import StacksFrontier.CategoryTheory.Trace.Sorites.Multiplicativity
public import StacksFrontier.NumberTheory.TraceFormula.AbstractTraceFormula
public import StacksFrontier.NumberTheory.TraceFormula.ProfiniteIntegersProcyclic

/-!
# The commutative example of an abstract trace formula: the congruence

Fix `q ≥ 1` and an extension of profinite groups `1 → Ẑ^{(q)} → Γ → Ẑ → 1` with `F ↦ 1` and
`F x F⁻¹ = u x` for a unit `u` of `Ẑ^{(q)}`. If `Γ` has an abstract trace formula with integer `q`
and sets `S_d`, then evaluating it on the trivial modules gives, for every finite commutative ring
`Λ` reached from `Ẑ^{(q)}` by a ring homomorphism `r` with open kernel (e.g. `Λ = ℤ/m` for `m`
prime to `q`),

`∑_{d ∣ n} d #S_d = q^n - r(qu)^n` in `Λ`.

The derived coinvariants `LH₀(Ẑ^{(q)}, Λ)` are `Λ` in degrees `0` and `-1`, and `F^n` acts on them
by `1` and by `r(u)^n`: this is `Stacks.GroupHomology.Procyclic.perfectDerivedTrace_trivialRep`
with the augmentation computed by
`Stacks.GroupHomology.Procyclic.augmentation_eq_natCast_of_mul_eq`.

## Main results

* `Stacks.TraceFormula.pointCountSum_eq_of_ringHom`: the congruence above.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
* [Stacks Project, Section 03VO](https://stacks.math.columbia.edu/tag/03VO)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.GroupHomology Stacks.GroupHomology.Procyclic
  Stacks.GroupHomology.CompletedGroupAlgebra
  CategoryTheory.FilteredDerived

universe u

namespace Stacks.TraceFormula

attribute [local instance] HasDerivedCategory.standard

/-- `q` is a unit of `Ẑ^{(q)} = ∏_{ℓ ∤ q} ℤ_ℓ`. -/
public theorem isUnit_natCast_restrictedProfiniteIntegers (q : ℕ) :
    IsUnit (q : RestrictedProfiniteIntegers q) := by
  refine Pi.isUnit_iff.2 fun p => ?_
  rw [Pi.natCast_apply, PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd p.2.1).2 p.2.2

/-- Every element of `Ẑ^{(q)}` agrees with a natural number modulo an open subgroup. -/
public theorem exists_natCast_sub_mem {q : ℕ} {S : AddSubgroup (RestrictedProfiniteIntegers q)}
    (hS : IsOpen (S : Set (RestrictedProfiniteIntegers q))) (x : RestrictedProfiniteIntegers q) :
    ∃ v : ℕ, (v : RestrictedProfiniteIntegers q) - x ∈ S :=
  (denseRange_natCast_restrictedProfiniteIntegers q).exists_mem_open
    (hS.preimage (continuous_id.sub continuous_const)) ⟨x, by simp [S.zero_mem]⟩

/-- `q` is a unit modulo every power of a prime `ℓ ∤ q`. -/
private theorem isUnit_natCast_zmod_pow {q : ℕ} (ℓ : CoprimePrimes q) (k : ℕ) :
    IsUnit (q : ZMod (ℓ.1 ^ k)) :=
  (ZMod.isUnit_iff_coprime _ _).2 <| Nat.Coprime.pow_right k <|
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd ℓ.2.1).2 ℓ.2.2)

/-- A trace identity in `ℤ/ℓ^k` (lifted to any universe) between `∑_{d ∣ n} d s_d` and
`q^n (1 - v)`, with `v ≡ u_ℓ^n`, is the congruence `q^n - (qu)_ℓ^n ≡ ∑_{d ∣ n} d s_d`. -/
private theorem toZModPow_sub_eq_pointCountSum {q : ℕ} (u : RestrictedProfiniteIntegers q)
    (s : ℕ → ℕ) {n : ℕ} (ℓ : CoprimePrimes q) (k v : ℕ)
    (hv : (v : ZMod (ℓ.1 ^ k)) = PadicInt.toZModPow k (u ℓ) ^ n)
    (h : ∑ x ∈ n.divisors, x • s x • (1 : ULift.{u} (ZMod (ℓ.1 ^ k))) =
      q ^ n • (1 - (v : ULift.{u} (ZMod (ℓ.1 ^ k))))) :
    PadicInt.toZModPow k ((q : ℤ_[ℓ.1]) ^ n - ((q : RestrictedProfiniteIntegers q) * u) ℓ ^ n) =
      (pointCountSum s n : ZMod (ℓ.1 ^ k)) := by
  have h' := congrArg ULift.ringEquiv h
  simp only [map_sum, map_nsmul, map_one, map_sub, map_natCast] at h'
  simp only [nsmul_eq_mul, mul_one] at h'
  rw [pointCountSum, Nat.cast_sum]
  simp only [Nat.cast_mul]
  rw [h', map_sub, map_pow, map_pow, map_natCast, hv, Pi.mul_apply, Pi.natCast_apply, map_mul,
    map_natCast, Nat.cast_pow]
  ring

/-- The generator of `G ≅ Ẑ^{(q)}` has prime-power quotients at every prime dividing `ℓ^k`. -/
private theorem hasPrimePowerQuotients_of_dvd_pow {q : ℕ} {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (e : Multiplicative (RestrictedProfiniteIntegers q) ≃ₜ* G) (ℓ : CoprimePrimes q) (k : ℕ)
    (p : ℕ) (hp : p.Prime) (hpd : p ∣ ℓ.1 ^ k) : HasPrimePowerQuotients (generatorOf e) p := by
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hp ℓ.2.1).1 (hp.dvd_of_dvd_pow hpd)
  exact hasPrimePowerQuotients_of_continuousMulEquiv e ℓ

/-- The image of `σ ^ m` under `G ≅ Ẑ^{(q)} → ℤ/ℓ^k` is `m`. -/
private theorem primePowerQuotient_generatorOf_pow {q : ℕ} {G : Type*} [Group G]
    [TopologicalSpace G] (e : Multiplicative (RestrictedProfiniteIntegers q) ≃ₜ* G)
    (ℓ : CoprimePrimes q) (k m : ℕ) :
    primePowerQuotient e ℓ k ((generatorOf e : G) ^ m) =
      Multiplicative.ofAdd (m : ZMod (ℓ.1 ^ k)) := by
  rw [map_pow, primePowerQuotient_generatorOf, ← ofAdd_nsmul, nsmul_one]

/-- The order of the generator modulo the kernel of `G ≅ Ẑ^{(q)} → ℤ/ℓ^k` vanishes in
`ℤ/ℓ^k`. -/
private theorem natCast_orderOf_generatorOf_quotient {q : ℕ} {G : Type*} [Group G]
    [TopologicalSpace G] (e : Multiplicative (RestrictedProfiniteIntegers q) ≃ₜ* G)
    (ℓ : CoprimePrimes q) (k : ℕ) :
    ((orderOf ((generatorOf e : G) : G ⧸ (primePowerQuotient e ℓ k).ker) : ℕ) :
      ZMod (ℓ.1 ^ k)) = 0 := by
  have h := pow_orderOf_eq_one ((generatorOf e : G) : G ⧸ (primePowerQuotient e ℓ k).ker)
  rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker,
    primePowerQuotient_generatorOf_pow, ofAdd_eq_one] at h

section Congruence

variable {q : ℕ} {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {deg : Γ →* Multiplicative ProfiniteIntegers}
  (e : Multiplicative (RestrictedProfiniteIntegers q) ≃ₜ* deg.ker) {F : Γ}
  (u : (RestrictedProfiniteIntegers q)ˣ)
  (hconj : ∀ x : RestrictedProfiniteIntegers q, F * (e (Multiplicative.ofAdd x) : Γ) * F⁻¹ =
    e (Multiplicative.ofAdd ((u : RestrictedProfiniteIntegers q) * x)))
include hconj

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
/-- Conjugation by `F^n` is multiplication by `u^n` on the kernel. -/
public theorem pow_conj (n : ℕ) (x : RestrictedProfiniteIntegers q) :
    F ^ n * (e (Multiplicative.ofAdd x) : Γ) * (F ^ n)⁻¹ =
      e (Multiplicative.ofAdd (((u ^ n : (RestrictedProfiniteIntegers q)ˣ) :
        RestrictedProfiniteIntegers q) * x)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_inv_rev, show F * F ^ n * (e (Multiplicative.ofAdd x) : Γ) *
      ((F ^ n)⁻¹ * F⁻¹) = F * (F ^ n * (e (Multiplicative.ofAdd x) : Γ) * (F ^ n)⁻¹) * F⁻¹ by
        group, ih, hconj, pow_succ', Units.val_mul, mul_assoc]

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
/-- The conjugate of the generator `σ` by `F^n` is `e(u^n)`. -/
public theorem conj_generatorOf (n : ℕ) :
    (conjContinuousMulEquiv deg.ker (F ^ n) (generatorOf e) : deg.ker) =
      e (Multiplicative.ofAdd ((u ^ n : (RestrictedProfiniteIntegers q)ˣ) :
        RestrictedProfiniteIntegers q)) := by
  apply Subtype.ext
  rw [conjContinuousMulEquiv_apply, generatorOf, pow_conj e u hconj, mul_one]

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
/-- Modulo the kernel of `deg.ker → ℤ/ℓ^k`, the conjugate of `σ` by `F^n` is the power of `σ`
given by the image of `u^n`. -/
private theorem conj_generatorOf_quotient_eq_pow (n : ℕ) (ℓ : CoprimePrimes q) (k : ℕ) :
    ((conjContinuousMulEquiv deg.ker (F ^ n) (generatorOf e) : deg.ker) :
        deg.ker ⧸ (primePowerQuotient e ℓ k).ker) =
      ((generatorOf e : deg.ker) : deg.ker ⧸ (primePowerQuotient e ℓ k).ker) ^
        (PadicInt.toZModPow k (((u ^ n : (RestrictedProfiniteIntegers q)ˣ) :
          RestrictedProfiniteIntegers q) ℓ)).val := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv,
    conj_generatorOf e u hconj n, primePowerQuotient_apply,
    primePowerQuotient_generatorOf_pow, ZMod.natCast_zmod_val, inv_mul_cancel]

end Congruence

section Trivial

variable {Γ : Type u} [Group Γ] (Λ : Type u) [Ring Λ]

/-- The trace of any element on the trivial representation is `1`. -/
public theorem projectiveModuleTrace_trivialRep (γ : Γ) :
    Stacks.Trace.projectiveModuleTrace Λ (TrivialRep Γ Λ)
        (DistribMulAction.toModuleEnd Λ (TrivialRep Γ Λ) γ) =
      additiveCommutatorQuotientMk Λ 1 := by
  rw [show DistribMulAction.toModuleEnd Λ (TrivialRep Γ Λ) γ = LinearMap.id from
    LinearMap.ext fun _ => rfl]
  exact (projectiveModuleTrace_self (R := Λ) LinearMap.id).trans rfl

end Trivial

section MainCongruence

variable {q : ℕ} {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {deg : Γ →* Multiplicative ProfiniteIntegers}
  {hdeg : Continuous deg} {hsurj : Function.Surjective deg}
  (e : Multiplicative (RestrictedProfiniteIntegers q) ≃ₜ* deg.ker) {F : Γ}
  (hF : deg F = Multiplicative.ofAdd 1) (u : (RestrictedProfiniteIntegers q)ˣ)
  (hconj : ∀ x : RestrictedProfiniteIntegers q, F * (e (Multiplicative.ofAdd x) : Γ) * F⁻¹ =
    e (Multiplicative.ofAdd ((u : RestrictedProfiniteIntegers q) * x)))
  (T : AbstractTraceFormula Γ deg hdeg hsurj) (hTq : T.q = q)
include hF hconj hTq

/-- **The congruence for the trivial modules.** An abstract trace formula for `Γ` gives
`q^n - (qu)^n ≡ ∑_{d ∣ n} d #S_d` modulo every power of every prime `ℓ ∤ q`. -/
public theorem isTrivialModuleCongruence_of_abstractTraceFormula :
    IsTrivialModuleCongruence q ((q : RestrictedProfiniteIntegers q) * u)
      (fun d => Fintype.card (T.S d)) := by
  classical
  intro n hn ℓ k
  have := compactSpace_ker deg hdeg
  let Λ : Type u := ULift.{u} (ZMod (ℓ.1 ^ k))
  let ι : ZMod (ℓ.1 ^ k) ≃+* Λ := ULift.ringEquiv.symm
  have hqΛ : IsUnit ((T.q : ℕ) : Λ) := by
    rw [hTq, ← map_natCast ι]
    exact (isUnit_natCast_zmod_pow ℓ k).map ι
  -- the trace formula on the trivial module `Λ`
  let M : Type u := TrivialRep Γ Λ
  have hM : ∀ m : M, IsOpen {γ : Γ | γ • m = m} := TrivialRep.isOpen_stabilizer Λ
  obtain ⟨hperf, htr⟩ := T.trace_formula Λ hqΛ M hM n hn
  choose g hg using fun d (x : T.S d) => ConjClasses.mk_surjective (T.F d x)
  have key := htr g hg F hF
  -- the left hand side
  have hlhs : ∀ d (x : T.S d), Stacks.Trace.projectiveModuleTrace Λ M
      (DistribMulAction.toModuleEnd Λ M (g d x ^ (n / d))) = additiveCommutatorQuotientMk Λ 1 :=
    fun d x => projectiveModuleTrace_trivialRep (Γ := Γ) Λ _
  simp only [hlhs, Finset.sum_const, Finset.card_univ] at key
  -- the right hand side
  have := Module.finite_of_finite Λ (M := M)
  set hV : IsSmoothFor deg.ker M := isSmoothFor_ker deg hdeg M hM
  set σ : deg.ker := generatorOf e
  have hgen : GeneratesQuotients σ := generatesQuotients_of_continuousMulEquiv e
  have hn' : ℓ.1 ^ k ≠ 0 := pow_ne_zero _ ℓ.2.1.ne_zero
  have hpow : ∀ p : ℕ, p.Prime → p ∣ ℓ.1 ^ k → HasPrimePowerQuotients σ p :=
    hasPrimePowerQuotients_of_dvd_pow e ℓ k
  have hΛ : ∀ a : Λ, (ℓ.1 ^ k) • a = 0 := fun a => by
    rw [nsmul_eq_mul, ← map_natCast ι, ZMod.natCast_self, map_zero, zero_mul]
  set τ := conjContinuousMulEquiv deg.ker (F ^ n) σ
  have hτ : augmentation ((of τ : CompletedGroupAlgebra Λ deg.ker) - 1) = 0 := by
    rw [map_sub, augmentation_of, map_one, sub_self]
  obtain ⟨w, hw⟩ := exists_mul_eq_of_augmentation_eq_zero hgen hn' hpow hΛ hτ
  rw [perfectDerivedTrace_trivialRep σ (F ^ n) hgen hn' hpow hΛ hV w hw hperf] at key
  -- the augmentation of `w` is the image of `u^n`
  let W : OpenNormalSubgroup deg.ker :=
    { toOpenSubgroup := ⟨_, isOpen_ker_primePowerQuotient e ℓ k⟩
      isNormal' := (primePowerQuotient e ℓ k).normal_ker }
  set y := ((u ^ n : (RestrictedProfiniteIntegers q)ˣ) : RestrictedProfiniteIntegers q)
  set v := (PadicInt.toZModPow k (y ℓ)).val
  have hv : (τ : deg.ker ⧸ (W : Subgroup deg.ker)) = (σ : deg.ker ⧸ (W : Subgroup deg.ker)) ^ v :=
    conj_generatorOf_quotient_eq_pow e u hconj n ℓ k
  have hW : ((orderOf (σ : deg.ker ⧸ (W : Subgroup deg.ker)) : ℕ) : Λ) = 0 := by
    rw [← map_natCast ι, natCast_orderOf_generatorOf_quotient e ℓ k, map_zero]
  rw [augmentation_eq_natCast_of_mul_eq hgen hw W hv hW] at key
  -- evaluate in `Λ` and transport to `ℤ/ℓ^k`
  have key' := congrArg (Stacks.Trace.commutativeAdditiveCommutatorQuotientEval Λ) key
  simp only [map_sum, map_nsmul] at key'
  change ∑ x ∈ n.divisors, x • Fintype.card (T.S x) • (1 : Λ) = T.q ^ n • (1 - (v : Λ)) at key'
  rw [hTq] at key'
  refine toZModPow_sub_eq_pointCountSum _ _ ℓ k v ?_ key'
  have hy : y ℓ = ((u : RestrictedProfiniteIntegers q) ℓ) ^ n := by
    simp [y, Units.val_pow_eq_pow_val]
  rw [ZMod.natCast_zmod_val, hy, map_pow]

end MainCongruence

end Stacks.TraceFormula

end
