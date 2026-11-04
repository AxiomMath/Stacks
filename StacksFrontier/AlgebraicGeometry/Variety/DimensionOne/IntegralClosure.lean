module

public import StacksFrontier.RingTheory.IntegralClosure.DedekindDomain
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.Jacobson
public import StacksCore.Tactic.StacksAttribute

/-!
# Integral closures of one-dimensional semilocal domains

The integral closure of a Noetherian semilocal domain of dimension at most one in its fraction
field is a semilocal Dedekind domain. Moreover, multiplying any element of the integral closure
by a sufficiently large power of a nonzero element of its Jacobson radical brings it into the
original domain: the Jacobson radical of the closure contracts into that of the base, and the
quotient of a finite subalgebra by the base is killed by a power of it.

## Main results

* `IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite` supplies the
  Dedekind-domain assertion.
* `IsIntegralClosure.finite_maximalSpectrum` proves semilocality of the integral closure.
* `IsIntegralClosure.exists_pow_mul_mem_range` is the conductor assertion.

## Implementation notes

The integral closure is represented abstractly by `IsIntegralClosure C B K`, where `K` is a
fraction field of `B`; this includes the concrete subalgebra `integralClosure B (FractionRing B)`.
The dimension-one hypothesis is weakened to `Ring.DimensionLEOne B`. Membership in the original
domain is expressed as membership in the range of the canonical algebra map.

The Krull--Akizuki theorem gives the Dedekind-domain part (as well as stronger auxiliary
conclusions), so it is registered directly rather than restated.

## References

* [Stacks Project, Tag 09N2](https://stacks.math.columbia.edu/tag/09N2)
-/

@[expose] public section

namespace IsIntegralClosure

private lemma support_quotient_range_subset_jacobson
    (B K A : Type*) [CommRing B] [IsDomain B] [Ring.DimensionLEOne B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    [CommRing A] [Algebra B A] [Algebra A K] [IsScalarTower B A K]
    (hinj : Function.Injective (algebraMap A K)) :
    Module.support B (A ⧸ LinearMap.range (Algebra.linearMap B A)) ⊆
      PrimeSpectrum.zeroLocus (Ring.jacobson B : Set B) := by
  classical
  intro p hp r hr
  change r ∈ Ring.jacobson B at hr
  show r ∈ p.asIdeal
  by_cases hpb : p.asIdeal = ⊥
  · refine (not_subsingleton_iff_nontrivial.mpr (Module.mem_support_iff.mp hp) ?_).elim
    rw [LocalizedModule.subsingleton_iff]
    intro z
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective
      (LinearMap.range (Algebra.linearMap B A)) z
    obtain ⟨b, d, hd, hfrac⟩ := IsFractionRing.div_surjective B (algebraMap A K a)
    have hmul : algebraMap B K d * algebraMap A K a = algebraMap B K b := by
      simpa [mul_comm] using
        ((div_eq_iff (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)).mp hfrac).symm
    have hclear : algebraMap B A d * a = algebraMap B A b := hinj (by
      simpa [map_mul, IsScalarTower.algebraMap_apply B A K] using hmul)
    have hmem : algebraMap B A d * a ∈ LinearMap.range (Algebra.linearMap B A) := by
      rw [hclear]
      exact LinearMap.mem_range_self _ b
    refine ⟨d, by simpa [hpb] using nonZeroDivisors.ne_zero hd, ?_⟩
    show Submodule.Quotient.mk (d • a) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    simpa [Algebra.smul_def] using hmem
  · have := Ring.DimensionLEOne.maximalOfPrime hpb p.isPrime
    exact Ring.jacobson_le_of_isMaximal p.asIdeal hr

private lemma exists_pow_smul_top_le_of_iPowerTorsion
    (B : Type*) [CommRing B] (A : Type*) [AddCommGroup A] [Module B A]
    (I : Ideal B) (N : Submodule B A) [Module.Finite B (A ⧸ N)]
    (htor : IsIPowerTorsion B (A ⧸ N) I) :
    ∃ n : ℕ, I ^ n • (⊤ : Submodule B A) ≤ N := by
  classical
  let Q := A ⧸ N
  have hfg : (⊤ : Submodule B Q).FG := Module.Finite.fg_top
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp hfg
  choose e he hkill using htor
  let n := hsfin.toFinset.sup e + 1
  refine ⟨n, ?_⟩
  rw [Submodule.smul_le]
  intro r hr a ha
  have hkillall : ∀ q : Q, r • q = 0 := by
    intro q
    have hspan : q ∈ Submodule.span B s := by simp [hs]
    have hgen : ∀ z ∈ s, r • z = 0 := fun z hz =>
      hkill z r (Ideal.pow_le_pow_right
        (Nat.le_succ_of_le (Finset.le_sup (hsfin.mem_toFinset.mpr hz))) hr)
    induction hspan using Submodule.span_induction with
    | mem z hz => exact hgen z hz
    | zero => simp
    | add z w hz hw ihz ihw => simp [ihz, ihw]
    | smul b z hz ih =>
        simpa [smul_smul, mul_comm] using congrArg (fun q => b • q) ih
  have hq : (Submodule.Quotient.mk ((r : B) • (a : A)) : Q) = 0 := by
    calc
      _ = r • (Submodule.Quotient.mk a : Q) := Submodule.Quotient.mk_smul N (S := B) r a
      _ = 0 := hkillall (Submodule.Quotient.mk a)
  rwa [Submodule.Quotient.mk_eq_zero] at hq

/-- If an element of an integral extension lies in its Jacobson radical, then the element of the
base below it lies in every maximal ideal. -/
private lemma mem_of_algebraMap_mem_jacobson (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S] (P : Ideal R) [P.IsMaximal] (r : R)
    (hr : algebraMap R S r ∈ Ring.jacobson S) : r ∈ P := by
  obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S ⟨P, inferInstance⟩
  have hqm : q.asIdeal.comap (algebraMap R S) = P := by
    simpa using congrArg (fun z : PrimeSpectrum R => z.asIdeal) hq
  have : q.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q.asIdeal (hqm ▸ ‹P.IsMaximal›)
  rw [← hqm]
  exact Ideal.mem_comap.mpr (Ring.jacobson_le_of_isMaximal q.asIdeal hr)

add_to_stacks 09N2 "the Dedekind-domain assertion"
  IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite

universe u v w

/-- The integral closure of a semilocal Noetherian domain of dimension at most one in its
fraction field is semilocal. -/
@[stacks 09N2 "the semilocal assertion", ega "0 23.2.6" "K' = K case"]
public lemma finite_maximalSpectrum (B : Type u) (K : Type v) (C : Type w)
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Ring.DimensionLEOne B] [Finite (MaximalSpectrum B)] [Field K] [Algebra B K]
    [IsFractionRing B K] [CommRing C] [Algebra B C] [Algebra C K] [IsScalarTower B C K]
    [IsIntegralClosure C B K] :
    Finite (MaximalSpectrum C) := by
  classical
  have : IsDomain C := Function.Injective.isDomain (algebraMap C K)
    (IsIntegralClosure.algebraMap_injective C B K)
  have : Algebra.IsIntegral B C := IsIntegralClosure.isIntegral_algebra B K
  have : IsFractionRing C K := IsIntegralClosure.isFractionRing_of_finite_extension B K K C
  have : ∀ m : MaximalSpectrum B, Finite {q : Ideal C // q ∈ m.asIdeal.primesOver C} :=
    fun m => (Ideal.isMaximal_and_finite_primesOver_and_module_finite_quotient
      B C K K m.asIdeal).2.1.to_subtype
  let g : MaximalSpectrum C →
      Σ m : MaximalSpectrum B, {q : Ideal C // q ∈ m.asIdeal.primesOver C} := fun n => by
    refine ⟨⟨n.asIdeal.comap (algebraMap B C),
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n.asIdeal⟩, ⟨n.asIdeal, ?_⟩⟩
    simp only [Ideal.primesOver]
    exact ⟨n.isMaximal.isPrime, Ideal.LiesOver.mk rfl⟩
  exact Finite.of_injective g fun _ _ h => MaximalSpectrum.ext (congrArg (fun z => z.2.1) h)

/-- A nonzero element of the Jacobson radical of the integral closure eventually carries every
element of the integral closure into the original domain. -/
@[stacks 09N2 "the conductor assertion"]
public lemma exists_pow_mul_mem_range (B : Type u) (K : Type v) (C : Type w)
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Ring.DimensionLEOne B] [Finite (MaximalSpectrum B)] [Field K] [Algebra B K]
    [IsFractionRing B K] [CommRing C] [Algebra B C] [Algebra C K] [IsScalarTower B C K]
    [IsIntegralClosure C B K]
    (x : C) (hx : x ≠ 0) (hxj : x ∈ Ring.jacobson C) (y : C) :
    ∃ n : ℕ, x ^ n * y ∈ RingHom.range (algebraMap B C) := by
  classical
  have : IsDomain C := Function.Injective.isDomain (algebraMap C K)
    (IsIntegralClosure.algebraMap_injective C B K)
  have : IsFractionRing C K := IsIntegralClosure.isFractionRing_of_finite_extension B K K C
  have : Algebra.IsIntegral B C := IsIntegralClosure.isIntegral_algebra B K
  have : FaithfulSMul B C := (faithfulSMul_iff_algebraMap_injective B C).mpr <| by
    have h := IsFractionRing.injective B K
    rw [IsScalarTower.algebraMap_eq B C K, RingHom.coe_comp] at h
    exact h.of_comp
  let I : Ideal B := Ring.jacobson B
  have hcomap_ne : Ideal.comap (algebraMap B C) (Ring.jacobson C) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx hxj (Algebra.IsIntegral.isIntegral (R := B) x)
  have hcomap_le : Ideal.comap (algebraMap B C) (Ring.jacobson C) ≤ Ring.jacobson B := by
    rw [Ring.jacobson_eq_sInf_isMaximal (R := B)]
    refine le_sInf fun m hm b hb => ?_
    have : m.IsMaximal := hm
    exact mem_of_algebraMap_mem_jacobson B C m b hb
  have hIne : I ≠ ⊥ := fun h => hcomap_ne (le_antisymm (by simpa [I, h] using hcomap_le) bot_le)
  let A := Algebra.adjoin B ({x, y} : Set C)
  have : Algebra.FiniteType B A := Algebra.FiniteType.adjoin_of_finite (by simp)
  have : Algebra.IsIntegral B A :=
    Algebra.IsIntegral.of_injective (IsScalarTower.toAlgHom B A C) Subtype.val_injective
  have : Module.Finite B A := Algebra.IsIntegral.finite
  have : Algebra.IsIntegral A C := Algebra.IsIntegral.tower_top B
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr
    Subtype.val_injective
  let xA : A := ⟨x, Algebra.subset_adjoin (by simp)⟩
  let yA : A := ⟨y, Algebra.subset_adjoin (by simp)⟩
  have hxrad : xA ∈ (I.map (algebraMap B A)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro P hP
    have hPprime : P.IsPrime := hP.2
    have hIle : I ≤ P.comap (algebraMap B A) := (Ideal.map_le_iff_le_comap).mp hP.1
    have hPcomapne : P.comap (algebraMap B A) ≠ ⊥ := fun hbot =>
      hIne (le_antisymm (by simpa [hbot] using hIle) bot_le)
    have : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P
      (Ring.DimensionLEOne.maximalOfPrime hPcomapne (hPprime.comap (algebraMap B A)))
    exact mem_of_algebraMap_mem_jacobson A C P xA hxj
  obtain ⟨m, hxm⟩ := Ideal.mem_radical_iff.mp hxrad
  let M : Submodule B A := LinearMap.range (Algebra.linearMap B A)
  have : Module.Finite B (A ⧸ M) := Module.Finite.quotient B M
  have hinjAK : Function.Injective (algebraMap A K) := by
    intro a₁ a₂ h
    exact Subtype.ext (IsFractionRing.injective C K (by simpa using h))
  have htor : IsIPowerTorsion B (A ⧸ M) I :=
    (isIPowerTorsion_iff_support_subset B (A ⧸ M) I (IsNoetherian.noetherian I)).2
      (support_quotient_range_subset_jacobson B K A hinjAK)
  obtain ⟨n, hn⟩ := exists_pow_smul_top_le_of_iPowerTorsion B A I M htor
  have hpower : xA ^ (m * n) * yA ∈ M := by
    rw [pow_mul]
    refine hn ?_
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
    exact Ideal.mul_mem_right yA _ (Ideal.pow_mem_pow hxm n)
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hpower
  refine ⟨m * n, RingHom.mem_range.mpr ⟨b, ?_⟩⟩
  simpa [xA, yA] using congrArg (fun z : A => (z : C)) hb

end IsIntegralClosure
