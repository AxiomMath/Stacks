module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.RingTheory.FormallySmooth.LocalRings
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.DedekindDomain.IntegralClosureFlat
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReduction

/-!
# Local algebra for the counterexample to the reduced fibre theorem over a non-quasi-compact curve

Three statements about local rings, used in the counterexample to Tags 0BRQ and 0BRS.

* A formally smooth local homomorphism `A → B` with `B` Noetherian, at a point that is a generic
  point of its fibre, has `𝔪_A B = 𝔪_B`: the fibre ring `B / 𝔪_A B` is formally smooth over the
  residue field of `A`, hence regular (Tag 07EI), hence a domain, and a local domain with a
  unique prime is a field.
* A flat local homomorphism `A → B` with `𝔪_A B = 𝔪_B` cannot carry an element `t ∈ 𝔪_A` to
  `a ^ n * c` with `c` a unit unless `t ∈ 𝔪_A ^ n`: `a` then lies in `𝔪_B = 𝔪_A B`, and the
  extension of an ideal along a faithfully flat map contracts back to it.
* In the integral closure `B` of a Dedekind domain `A` in a finite extension `L` of its fraction
  field `K`, a generator `τ` of a maximal ideal of `A` does not lie in the `([L : K] + 1)`-st
  power of the maximal ideal of any localization `B_q` in which it is not a unit: the
  ramification index of `q` bounds the `B_q`-valuation of `τ`, and is at most `[L : K]`.

## Main results

* `AlgebraicGeometry.ReducedFibreCurveCounterexample.map_maximalIdeal_eq_of_formallySmooth`
* `AlgebraicGeometry.ReducedFibreCurveCounterexample.mem_maximalIdeal_pow_of_map_maximalIdeal_eq`
* `AlgebraicGeometry.ReducedFibreCurveCounterexample.algebraMap_notMem_maximalIdeal_pow`

## References

* [Stacks Project, Tag 07EI](https://stacks.math.columbia.edu/tag/07EI)
* [Stacks Project, Tag 0BRQ](https://stacks.math.columbia.edu/tag/0BRQ)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.ReducedFibreCurveCounterexample

/-- **A formally smooth local homomorphism is unramified at a generic point of its fibre.** Let
`A → B` be a local homomorphism of local rings with `B` Noetherian and formally smooth over `A`,
and assume every prime of `B` containing `𝔪_A B` is `𝔪_B`. Then `𝔪_A B = 𝔪_B`. -/
theorem map_maximalIdeal_eq_of_formallySmooth {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Algebra.FormallySmooth A B]
    (h : ∀ P : Ideal B, P.IsPrime → (maximalIdeal A).map (algebraMap A B) ≤ P →
      P = maximalIdeal B) :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
  set I := (maximalIdeal A).map (algebraMap A B) with hI
  let k := A ⧸ maximalIdeal A
  let : Field k := Ideal.Quotient.field _
  let C := k ⊗[A] B
  have hItop : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top (map_maximalIdeal_le (algebraMap A B))
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have : IsLocalRing (B ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  let e : B ⧸ I ≃+* C :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).toRingEquiv.trans
      (Algebra.TensorProduct.comm A B k).toRingEquiv
  have : IsLocalRing C := e.isLocalRing
  have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv _ e
  have hreg : IsRegularLocalRing C := by
    refine isRegularLocalRing_of_isFormallySmooth_maximalIdeal (k := k) ?_
    unfold FormallySmoothDiscreteMaximalIdeal
    let : TopologicalSpace k := ⊥
    let : DiscreteTopology k := ⟨rfl⟩
    let : TopologicalSpace C := (maximalIdeal C).adicTopology
    refine ⟨continuous_of_discreteTopology, ?_⟩
    exact Stacks.FormallySmooth.TopologicalRings.formallySmoothTop_of_formallySmooth_of_isAdic
      _ (maximalIdeal C) rfl (by rw [toAlgebra_algebraMap]; infer_instance)
  have : IsDomain C := IsRegularLocalRing.isDomain C
  have : IsDomain (B ⧸ I) := MulEquiv.isDomain C e.toMulEquiv
  exact (h I ((Ideal.Quotient.isDomain_iff_prime I).mp inferInstance) le_rfl).symm ▸ rfl

/-- **Flatness bounds the order of vanishing.** Let `A → B` be a flat local homomorphism of local
rings with `𝔪_A B = 𝔪_B`. If `t ∈ 𝔪_A` maps to `a ^ n * c` with `c` a unit of `B`, then
`t ∈ 𝔪_A ^ n`. -/
theorem mem_maximalIdeal_pow_of_map_maximalIdeal_eq {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) {t : A}
    (ht : t ∈ maximalIdeal A) {a c : B} (hc : IsUnit c) (n : ℕ)
    (h : algebraMap A B t = a ^ n * c) : t ∈ maximalIdeal A ^ n := by
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have htB : algebraMap A B t ∈ maximalIdeal B := hm ▸ Ideal.mem_map_of_mem _ ht
  have ha : a ∈ maximalIdeal B := (maximalIdeal.isMaximal B).isPrime.mem_of_pow_mem n
    ((Ideal.mul_unit_mem_iff_mem _ hc).mp (h ▸ htB))
  rw [← hm] at ha
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) ((maximalIdeal A) ^ n), Ideal.mem_comap,
    h, Ideal.map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha n)

/-- **The ramification bound.** Let `A` be a Nagata Dedekind domain with fraction field `K`, let
`L / K` be finite and let `B` be the integral closure of `A` in `L`. If `τ ∈ A` is nonzero and
generates a maximal ideal, and `q` is a prime of `B` at which `τ` is not a unit, then `τ` does not
lie in the `([L : K] + 1)`-st power of the maximal ideal of `B_q`. -/
theorem algebraMap_notMem_maximalIdeal_pow {A : Type u} [CommRing A] [IsDedekindDomain A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] (hA : IsNagataRing A) {τ : A} (hτ0 : τ ≠ 0)
    (hτ : (Ideal.span {τ}).IsMaximal) (q : Ideal (integralClosure A L)) [q.IsPrime]
    (hq : algebraMap A (Localization.AtPrime q) τ ∈ maximalIdeal (Localization.AtPrime q)) :
    algebraMap A (Localization.AtPrime q) τ ∉
      maximalIdeal (Localization.AtPrime q) ^ (Module.finrank K L + 1) := by
  intro hmem
  have : Module.Finite A (integralClosure A L) :=
    module_finite_integralClosure_of_isNagataRing K L hA
  have : IsDedekindDomain (integralClosure A L) :=
    isDedekindDomain_integralClosure_of_isNagataRing K L hA
  have : Module.Flat A (integralClosure A L) := integralClosure.flat A K L
  have : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  -- `A → B` is injective
  have hinj : Function.Injective (algebraMap A (integralClosure A L)) := by
    refine .of_comp (f := algebraMap (integralClosure A L) L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : Module.IsTorsionFree A (integralClosure A L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  -- `q` lies over `(τ)`
  have hτq : algebraMap A (integralClosure A L) τ ∈ q := by
    rw [IsScalarTower.algebraMap_apply A (integralClosure A L) (Localization.AtPrime q)] at hq
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q _).mp hq
  have hpτ : q.under A = Ideal.span {τ} := by
    have hle : Ideal.span {τ} ≤ q.under A := (Ideal.span_singleton_le_iff_mem _).mpr hτq
    exact (hτ.eq_of_le (Ideal.IsPrime.under A q).ne_top hle).symm
  have : (q.under A).IsMaximal := hpτ ▸ hτ
  have hq0 : q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hτq
    exact hτ0 (hinj (by rw [hτq, map_zero]))
  have : IsDiscreteValuationRing (Localization.AtPrime q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure A L) hq0
      (Localization.AtPrime q)
  -- the ramification index is at least `d + 1`
  have hmap : (q.under A).map (algebraMap A (Localization.AtPrime q)) ≤
      maximalIdeal (Localization.AtPrime q) ^ (Module.finrank K L + 1) := by
    rw [hpτ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hlen : ((Module.finrank K L + 1 : ℕ) : ℕ∞) ≤ Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ (q.under A).map (algebraMap A (Localization.AtPrime q))) := by
    rw [← IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (Localization.AtPrime q)
      (Module.finrank K L + 1)]
    exact Module.length_le_of_surjective (Submodule.factor hmap)
      (Submodule.factor_surjective hmap)
  have hepos : 0 < q.ramificationIdx A := Ideal.ramificationIdx_pos A q
  have hge : Module.finrank K L + 1 ≤ q.ramificationIdx A := by
    rw [Ideal.ramificationIdx_def] at hepos ⊢
    have hne : Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸ (q.under A).map (algebraMap A (Localization.AtPrime q))) ≠ ⊤ := by
      intro htop
      rw [htop] at hepos
      simp at hepos
    rw [← ENat.coe_toNat hne] at hlen
    exact_mod_cast hlen
  -- the fundamental identity bounds it by `d`
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (q.under A) (integralClosure A L)
  rw [← IsFractionRing.finrank_eq A K (integralClosure A L) L] at hsum
  have hle : q.ramificationIdx A * q.inertiaDeg A ≤ Module.finrank K L := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun q' : (q.under A).primesOver (integralClosure A L) ↦
      q'.1.ramificationIdx A * q'.1.inertiaDeg A) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ ⟨q, inferInstance, ⟨rfl⟩⟩)
  have : q.ramificationIdx A ≤ Module.finrank K L :=
    le_trans (Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos q A)) hle
  omega

end AlgebraicGeometry.ReducedFibreCurveCounterexample
