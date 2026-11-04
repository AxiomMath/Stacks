module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppTotallyRamifiedTower
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationTower

open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Vertical agreement of ramification indices from a totally ramified enlargement

Let `D₁` and `D₂` be integral-closure base-change packages over `K₁` and `K₂`, with `K₂ / K₁`
totally ramified with respect to `D₁.A₁`. A weak solution over `K₁` is one over `K₂` as soon as
the two vertical ramification indices of the local factor square agree, by
`IsDiscreteValuationRing.IntegralClosureBaseChange.IsWeakSolution.of_ramificationIdx_vertical_eq`.
This agreement does not follow from the multiplicativity of ramification indices in towers.

This file reduces it to a degree bound. By the `≤` form of the criterion,
`Ideal.ramificationIdx_eq_one_iff_ramificationIdx_vertical_le`, only one inequality is needed,
and when `K₂ / K₁` is totally ramified the vertical index on the `A`-side is exactly
`Module.finrank K₁ K₂`. So the criterion becomes

    every maximal ideal of `D₂.B₁` has vertical ramification index at most `Module.finrank K₁ K₂`

over `D₁.B₁`. This follows from the same bound on the dimensions of the fibres of `D₂.B₁` over
`D₁.B₁`, and it suffices to check that bound at the minimal primes of `D₁.B₁`.

## Main results

* `Stacks.EppTheorem.exists_surjective_algHom_reduction_tensor`: the reduction of a base change
  `C ⊗[R] S` is a quotient of the base change of the reduction of `C`.
* `Stacks.EppTheorem.ramificationIdx_eq_finrank_of_totallyRamified_under`: for a totally ramified
  `K₂ / K₁` and any integral closure `S` of `R` in `K₂`, every maximal ideal of `S` has
  `Ideal.ramificationIdx` over `R` equal to `Module.finrank K₁ K₂`.
* `Stacks.EppTheorem.ramificationIdx_le_finrank_fiber`: for a finite algebra, the ramification
  index at a prime is at most the dimension of the fibre there.
* `Stacks.EppTheorem.isWeakSolution_of_totallyRamified_of_ramificationIdx_le`: a weak solution
  over `K₁` is one over `K₂` as soon as the vertical index on the `B`-side is at most
  `Module.finrank K₁ K₂` at every maximal ideal.
* `Stacks.EppTheorem.finrank_fiber_le_of_minimalPrimes`: for a finite flat algebra, a bound on the
  fibre dimension at the minimal primes is a bound at every prime.
* `Stacks.EppTheorem.isWeakSolution_of_totallyRamified_of_finrank_fiber_le`: the same, given that
  every fibre of `D₂.B₁` over `D₁.B₁` has dimension at most `Module.finrank K₁ K₂`.
* `Stacks.EppTheorem.isWeakSolution_of_totallyRamified_of_finrank_fiber_le_minimalPrimes`: the
  same, given that bound only at the minimal primes of `D₁.B₁`.

## References

* [The Stacks Project, Tag 09ER](https://stacks.math.columbia.edu/tag/09ER)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.EppTheorem

open IsDiscreteValuationRing

/-- For `R`-algebras `C` and `S` there is a surjective `R`-algebra map

    `(C ⧸ nilradical C) ⊗[R] S  ↠  (C ⊗[R] S) ⧸ nilradical (C ⊗[R] S)`

sending `Ideal.Quotient.mk (nilradical C) c ⊗ₜ s` to the class of `c ⊗ₜ s`. It need not be an
isomorphism, since `(C ⧸ nilradical C) ⊗[R] S` need not be reduced. -/
theorem exists_surjective_algHom_reduction_tensor
    (R : Type*) [CommRing R] (C : Type*) [CommRing C] [Algebra R C]
    (S : Type*) [CommRing S] [Algebra R S] :
    ∃ f : ((C ⧸ nilradical C) ⊗[R] S) →ₐ[R] ((C ⊗[R] S) ⧸ nilradical (C ⊗[R] S)),
      Function.Surjective f ∧ ∀ (c : C) (s : S),
        f (Ideal.Quotient.mk (nilradical C) c ⊗ₜ[R] s)
          = Ideal.Quotient.mk (nilradical (C ⊗[R] S)) (c ⊗ₜ[R] s) := by
  classical
  have hker : ∀ a ∈ nilradical C,
      ((Ideal.Quotient.mkₐ R (nilradical (C ⊗[R] S))).comp
        (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] S)) a = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    have hx0 : x ^ n = 0 := by simpa using hn
    refine (Ideal.Quotient.eq_zero_iff_mem (I := nilradical (C ⊗[R] S))).mpr ⟨n, ?_⟩
    simp only [← map_pow, hx0, map_zero]
    exact Submodule.zero_mem _
  set f := Algebra.TensorProduct.lift
    (Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R (nilradical (C ⊗[R] S))).comp
      (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] S)) hker)
    ((Ideal.Quotient.mkₐ R (nilradical (C ⊗[R] S))).comp
      (Algebra.TensorProduct.includeRight : S →ₐ[R] C ⊗[R] S))
    (fun _ _ => Commute.all _ _) with hf
  have hfmk : ∀ (c : C) (s : S),
      f (Ideal.Quotient.mk (nilradical C) c ⊗ₜ[R] s)
        = Ideal.Quotient.mk (nilradical (C ⊗[R] S)) (c ⊗ₜ[R] s) := by
    intro c s
    rw [hf, Algebra.TensorProduct.lift_tmul]
    have h1 : (Ideal.Quotient.liftₐ (nilradical C)
        ((Ideal.Quotient.mkₐ R (nilradical (C ⊗[R] S))).comp
          (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] S)) hker)
        (Ideal.Quotient.mk (nilradical C) c)
        = Ideal.Quotient.mk (nilradical (C ⊗[R] S)) (c ⊗ₜ[R] 1) := rfl
    have h2 : ((Ideal.Quotient.mkₐ R (nilradical (C ⊗[R] S))).comp
        (Algebra.TensorProduct.includeRight : S →ₐ[R] C ⊗[R] S)) s
        = Ideal.Quotient.mk (nilradical (C ⊗[R] S)) (1 ⊗ₜ[R] s) := rfl
    rw [h1, h2, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine ⟨f, ?_, hfmk⟩
  intro z
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c s => exact ⟨Ideal.Quotient.mk _ c ⊗ₜ[R] s, hfmk c s⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, ← map_add]⟩

-- The carrier data of a package are instance-implicit structure fields; they are made local
-- instances so that binders mentioning `D.A₁`, `D.B₁` and `K₁` elaborate.
attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁K₁

/-- Let `R` be a discrete valuation ring with fraction field `K₁`, let `K₂ / K₁` be finite
separable and totally ramified with respect to `R`, and let `S` be any integral closure of `R` in
`K₂`. Then every maximal ideal of `S` has ramification index `Module.finrank K₁ K₂` over `R`.

Total ramification is stated with `Ideal.ramificationIdx'`, the multiplicity in the factorisation
of the extended ideal; the hypothesis `IsDedekindDomain S` identifies it with
`Ideal.ramificationIdx` (`Ideal.ramificationIdx'_eq_ramificationIdx`). -/
theorem ramificationIdx_eq_finrank_of_totallyRamified_under
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₁ : Type*) [Field K₁] [Algebra R K₁] [IsFractionRing R K₁]
    (K₂ : Type*) [Field K₂] [Algebra K₁ K₂] [FiniteDimensional K₁ K₂]
    [Algebra.IsSeparable K₁ K₂] [Algebra R K₂] [IsScalarTower R K₁ K₂]
    (S : Type*) [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Algebra S K₂] [IsScalarTower R S K₂] [IsIntegralClosure S R K₂]
    (htot : IsTotallyRamifiedWithRespectTo R K₁ K₂)
    (m : Ideal S) (hm : m.IsMaximal) :
    m.ramificationIdx R = Module.finrank K₁ K₂ := by
  classical
  have hmP : m.IsPrime := hm.isPrime
  have hintS : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R K₂
  have hmaxdown : (m.under R).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (hI := hm) m
  have hlo : m.LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(IsLocalRing.eq_maximalIdeal hmaxdown).symm⟩
  have hRK₂ : Function.Injective (algebraMap R K₂) := by
    rw [IsScalarTower.algebraMap_eq R K₁ K₂]
    exact (algebraMap K₁ K₂).injective.comp (IsFractionRing.injective R K₁)
  have hinjRS : Function.Injective (algebraMap R S) := by
    intro x y hxy
    apply hRK₂
    rw [IsScalarTower.algebraMap_apply R S K₂, IsScalarTower.algebraMap_apply R S K₂, hxy]
  have htf : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjRS
  have hmaxR : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  have hpne : IsLocalRing.maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal R) m hpne]
  exact
    ramificationIdx'_eq_finrank_of_totallyRamified_transport R K₁ K₂ S htot
    m hm (IsLocalRing.maximalIdeal R) hlo

/-- For a finite `R`-algebra `S` and a prime `q` of `S`, the ramification index of `q` over `R`
is at most the dimension of the fibre of `S` over `q.under R`. No hypothesis that `R` or `S` is a
domain or a local ring is needed, so this applies to semilocal rings such as `D₁.B₁`. -/
theorem ramificationIdx_le_finrank_fiber
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (q : Ideal S) [hq : q.IsPrime] [Module.Finite R S] :
    q.ramificationIdx R ≤
      Module.finrank (q.under R).ResidueField ((q.under R).Fiber S) := by
  classical
  have hlo : q.LiesOver (q.under R) := ⟨rfl⟩
  let : Fintype ((q.under R).primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver (q.under R)).fintype
  have hterm : q.ramificationIdx R * q.inertiaDeg R ≤
      Module.finrank (q.under R).ResidueField ((q.under R).Fiber S) := by
    rw [← Ideal.sum_ramification_inertia_eq_finrank_fiber (q.under R) S]
    exact Finset.single_le_sum
      (f := fun r : (q.under R).primesOver S => r.1.ramificationIdx R * r.1.inertiaDeg R)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (Ideal.primesOver.mk (q.under R) q))
  exact (Nat.le_mul_of_pos_right _ (q.inertiaDeg_pos R)).trans hterm

/-- Let `D₁` and `D₂` be integral-closure base-change packages over `K₁` and `K₂`, with `K₂ / K₁`
finite separable and totally ramified with respect to `D₁.A₁`. If every maximal ideal of `D₂.B₁`
has ramification index over `D₁.B₁` at most `Module.finrank K₁ K₂` (`hle`), then `D₂` is a weak
solution whenever `D₁` is. No hypothesis on the residue characteristic, completeness or
henselianness is needed. -/
theorem isWeakSolution_of_totallyRamified_of_ramificationIdx_le
    {A B K L K₁ K₂ : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [Algebra K K₂] [Algebra A K₂]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower A K K₁] [IsScalarTower A K K₂]
    [Module.Finite K K₁] [Module.Finite K K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [Algebra D₁.A₁ D₂.A₁] [Algebra D₁.B₁ D₂.B₁]
    [Algebra D₁.A₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₁.B₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₂.A₁ D₂.B₁]
    [Module.Finite D₁.B₁ D₂.B₁]
    [Module.Flat D₁.B₁ D₂.B₁] [Module.Flat D₂.A₁ D₂.B₁]
    [IsDomain D₁.A₁] [IsDiscreteValuationRing D₁.A₁] [IsFractionRing D₁.A₁ K₁]
    [IsDedekindDomain D₂.A₁]
    [Algebra K₁ K₂] [FiniteDimensional K₁ K₂] [Algebra.IsSeparable K₁ K₂]
    [Algebra D₁.A₁ K₂] [IsScalarTower D₁.A₁ K₁ K₂] [IsScalarTower D₁.A₁ D₂.A₁ K₂]
    [IsIntegralClosure D₂.A₁ D₁.A₁ K₂]
    (htot : IsTotallyRamifiedWithRespectTo D₁.A₁ K₁ K₂)
    (hmaxdown : ∀ q' : Ideal D₂.B₁, q'.IsMaximal → (q'.under D₂.A₁).IsMaximal)
    (hle : ∀ q' : Ideal D₂.B₁, q'.IsMaximal →
      q'.ramificationIdx D₁.B₁ ≤ Module.finrank K₁ K₂)
    (hD₁ : D₁.IsWeakSolution) : D₂.IsWeakSolution := by
  have hAside : ∀ q' : Ideal D₂.B₁, q'.IsMaximal →
      (q'.under D₂.A₁).ramificationIdx D₁.A₁ = Module.finrank K₁ K₂ := fun q' hq' =>
    ramificationIdx_eq_finrank_of_totallyRamified_under D₁.A₁ K₁ K₂ D₂.A₁ htot _
      (hmaxdown q' hq')
  refine IntegralClosureBaseChange.IsWeakSolution.of_ramificationIdx_vertical_le
    D₁ D₂ ?_ ?_ ?_ hD₁
  · intro q' hq'
    rw [hAside q' hq']
    exact Module.finrank_pos
  · intro q' hq'
    have : q'.IsPrime := hq'.isPrime
    exact Ideal.ramificationIdx_pos q' D₁.B₁
  · intro q' hq'
    rw [hAside q' hq']
    exact hle q' hq'

/-- For a finite flat `R`-algebra `M`, a bound `d` on the dimension of the fibre of `M` at every
minimal prime of `R` is a bound at every prime of `R`: the rank `Module.rankAtStalk` of a finite
flat module agrees at nested primes, and every prime contains a minimal one. -/
theorem finrank_fiber_le_of_minimalPrimes
    {R M : Type*} [CommRing R] [CommRing M] [Algebra R M]
    [Module.Finite R M] [Module.Flat R M] (d : ℕ)
    (hgen : ∀ p : Ideal R, p ∈ minimalPrimes R → ∀ _ : p.IsPrime,
      Module.finrank p.ResidueField (p.Fiber M) ≤ d)
    (q : Ideal R) [q.IsPrime] :
    Module.finrank q.ResidueField (q.Fiber M) ≤ d := by
  obtain ⟨p, hpmin, hpq⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := q) bot_le
  have hpP : p.IsPrime := hpmin.1.1
  rw [Ideal.finrank_fiber_eq_rankAtStalk,
    ← Module.rankAtStalk_eq_of_le_of_finite_of_flat' M (p := p) (q := q) hpq,
    ← Ideal.finrank_fiber_eq_rankAtStalk]
  exact hgen p hpmin hpP

/-- Let `D₁` and `D₂` be integral-closure base-change packages over `K₁` and `K₂`, with `K₂ / K₁`
finite separable and totally ramified with respect to `D₁.A₁`. If for every prime `q` of `D₁.B₁`
the fibre of `D₂.B₁` over `q` has dimension at most `Module.finrank K₁ K₂` (`hfib`), then `D₂` is
a weak solution whenever `D₁` is. By `Ideal.finrank_fiber_eq_rankAtStalk`, `hfib` says that
`D₂.B₁` has local rank at most `[K₂ : K₁]` over `D₁.B₁` at every prime. -/
theorem isWeakSolution_of_totallyRamified_of_finrank_fiber_le
    {A B K L K₁ K₂ : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [Algebra K K₂] [Algebra A K₂]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower A K K₁] [IsScalarTower A K K₂]
    [Module.Finite K K₁] [Module.Finite K K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [Algebra D₁.A₁ D₂.A₁] [Algebra D₁.B₁ D₂.B₁]
    [Algebra D₁.A₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₁.B₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₂.A₁ D₂.B₁]
    [Module.Finite D₁.B₁ D₂.B₁]
    [Module.Flat D₁.B₁ D₂.B₁] [Module.Flat D₂.A₁ D₂.B₁]
    [IsDomain D₁.A₁] [IsDiscreteValuationRing D₁.A₁] [IsFractionRing D₁.A₁ K₁]
    [IsDedekindDomain D₂.A₁]
    [Algebra K₁ K₂] [FiniteDimensional K₁ K₂] [Algebra.IsSeparable K₁ K₂]
    [Algebra D₁.A₁ K₂] [IsScalarTower D₁.A₁ K₁ K₂] [IsScalarTower D₁.A₁ D₂.A₁ K₂]
    [IsIntegralClosure D₂.A₁ D₁.A₁ K₂]
    (htot : IsTotallyRamifiedWithRespectTo D₁.A₁ K₁ K₂)
    (hmaxdown : ∀ q' : Ideal D₂.B₁, q'.IsMaximal → (q'.under D₂.A₁).IsMaximal)
    (hfib : ∀ (q : Ideal D₁.B₁) [q.IsPrime],
      Module.finrank q.ResidueField (q.Fiber D₂.B₁) ≤ Module.finrank K₁ K₂)
    (hD₁ : D₁.IsWeakSolution) : D₂.IsWeakSolution := by
  refine isWeakSolution_of_totallyRamified_of_ramificationIdx_le D₁ D₂ htot hmaxdown ?_ hD₁
  intro q' hq'
  have : q'.IsPrime := hq'.isPrime
  exact (ramificationIdx_le_finrank_fiber q').trans (hfib (q'.under D₁.B₁))

/-- The variant of `Stacks.EppTheorem.isWeakSolution_of_totallyRamified_of_finrank_fiber_le` in
which the bound `hgen` on the dimensions of the fibres of `D₂.B₁` is required only at the minimal
primes of `D₁.B₁`. -/
theorem isWeakSolution_of_totallyRamified_of_finrank_fiber_le_minimalPrimes
    {A B K L K₁ K₂ : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [Algebra K K₂] [Algebra A K₂]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower A K K₁] [IsScalarTower A K K₂]
    [Module.Finite K K₁] [Module.Finite K K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [Algebra D₁.A₁ D₂.A₁] [Algebra D₁.B₁ D₂.B₁]
    [Algebra D₁.A₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₁.B₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₂.A₁ D₂.B₁]
    [Module.Finite D₁.B₁ D₂.B₁]
    [Module.Flat D₁.B₁ D₂.B₁] [Module.Flat D₂.A₁ D₂.B₁]
    [IsDomain D₁.A₁] [IsDiscreteValuationRing D₁.A₁] [IsFractionRing D₁.A₁ K₁]
    [IsDedekindDomain D₂.A₁]
    [Algebra K₁ K₂] [FiniteDimensional K₁ K₂] [Algebra.IsSeparable K₁ K₂]
    [Algebra D₁.A₁ K₂] [IsScalarTower D₁.A₁ K₁ K₂] [IsScalarTower D₁.A₁ D₂.A₁ K₂]
    [IsIntegralClosure D₂.A₁ D₁.A₁ K₂]
    (htot : IsTotallyRamifiedWithRespectTo D₁.A₁ K₁ K₂)
    (hmaxdown : ∀ q' : Ideal D₂.B₁, q'.IsMaximal → (q'.under D₂.A₁).IsMaximal)
    (hgen : ∀ p : Ideal D₁.B₁, p ∈ minimalPrimes D₁.B₁ → ∀ _ : p.IsPrime,
      Module.finrank p.ResidueField (p.Fiber D₂.B₁) ≤ Module.finrank K₁ K₂)
    (hD₁ : D₁.IsWeakSolution) : D₂.IsWeakSolution :=
  isWeakSolution_of_totallyRamified_of_finrank_fiber_le D₁ D₂ htot hmaxdown
    (fun _ => finrank_fiber_le_of_minimalPrimes _ hgen _) hD₁

end Stacks.EppTheorem

end
