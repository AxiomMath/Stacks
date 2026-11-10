module

public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.MinimalPrimeComponents

/-!
# Two minimal primes of a local ring of delta invariant one sum to the maximal ideal

Let `A` be a reduced local ring with finitely many minimal primes, at least two of them, and
delta invariant one, and let `p ≠ q` be two of its minimal primes. Then `p ⊔ q` is the maximal
ideal of `A`: the two branches through the closed point meet transversally.

## Main results

* `Ring.length_quotient_sup_minimalPrimes_le_deltaInvariant` — the length of `A ⧸ (p ⊔ q)` is at
  most the delta invariant of `A`.
* `Ring.sup_eq_maximalIdeal_of_deltaInvariant_eq_one` — two distinct minimal primes of a reduced
  local ring of delta invariant one sum to the maximal ideal.
* `Ring.sup_eq_maximalIdeal_of_mem_minimalPrimes_of_deltaInvariant_eq_one` — the same, for two
  distinct ideals in `minimalPrimes A`.

## References

* [Stacks Project, Tag 0C3T](https://stacks.math.columbia.edu/tag/0C3T)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
-/

@[expose] public section

universe u

namespace Ring

/-- For two distinct minimal primes `p` and `q` of a reduced local ring `A` with finitely many
minimal primes and delta invariant one, the length of `A ⧸ (p ⊔ q)` is at most the delta
invariant of `A`. -/
public theorem length_quotient_sup_minimalPrimes_le_deltaInvariant
    (A : Type u) [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : (minimalPrimes A).Finite)
    {p q : minimalPrimes A} (hpq : p ≠ q)
    (hδ : Ring.deltaInvariant A = 1) :
    Module.length A (A ⧸ ((p : Ideal A) ⊔ (q : Ideal A))) ≤ Ring.deltaInvariant A := by
  classical
  have hfin : Finite (minimalPrimes A) := hA
  have hprime : ∀ s : minimalPrimes A, (s : Ideal A).IsPrime := fun s => s.property.left.left
  have hdomain : ∀ s : minimalPrimes A, IsDomain (A ⧸ (s : Ideal A)) := fun s =>
    Ideal.Quotient.isDomain (s : Ideal A)
  let (s : minimalPrimes A) : Algebra A (FractionRing (A ⧸ (s : Ideal A))) :=
    ((algebraMap (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))).comp
      (Ideal.Quotient.mk (s : Ideal A))).toAlgebra
  let (s : minimalPrimes A) : Algebra A
      ↥(integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))) :=
    ((algebraMap (A ⧸ (s : Ideal A))
      ↥(integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A))))).comp
        (Ideal.Quotient.mk (s : Ideal A))).toAlgebra
  obtain ⟨e⟩ := minimalPrimes.integralClosure_fractionRing_algEquiv_pi_quotient (A := A) hA
  have hsurj : ∀ s : minimalPrimes A, Function.Surjective
      (algebraMap (A ⧸ (s : Ideal A))
        ↥(integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A))))) := by
    intro s
    have h0 := deltaInvariant_quotient_minimalPrimes_eq_zero_of_deltaInvariant_eq_one A hA hpq hδ s
    rw [Ring.deltaInvariant] at h0
    have htop : LinearMap.range (Algebra.linearMap (A ⧸ (s : Ideal A))
        ↥(integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A))))) = ⊤ :=
      Submodule.Quotient.subsingleton_iff.mp (Module.length_eq_zero_iff.mp h0)
    exact LinearMap.range_eq_top.mp htop
  have hinj : ∀ s : minimalPrimes A, Function.Injective
      (algebraMap (A ⧸ (s : Ideal A))
        ↥(integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A))))) := by
    intro s x y hxy
    have := hdomain s
    exact IsFractionRing.injective (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))
      (congrArg Subtype.val hxy)
  let ε : ∀ s : minimalPrimes A, (A ⧸ (s : Ideal A)) ≃ₐ[A]
      ↥(integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))) := fun s =>
    { __ := RingEquiv.ofBijective
        (algebraMap (A ⧸ (s : Ideal A))
          ↥(integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))))
        ⟨hinj s, hsurj s⟩
      commutes' := fun _ => rfl }
  let Φ : ∀ (s : minimalPrimes A), (s : Ideal A) ≤ (p : Ideal A) ⊔ (q : Ideal A) →
      ↥(integralClosure A (FractionRing A)) →ₐ[A]
        A ⧸ ((p : Ideal A) ⊔ (q : Ideal A)) := fun s h =>
    (Ideal.Quotient.factorₐ A h).comp
      (((ε s).symm.toAlgHom).comp
        ((Pi.evalAlgHom A (fun s : minimalPrimes A =>
          ↥(integralClosure (A ⧸ (s : Ideal A))
            (FractionRing (A ⧸ (s : Ideal A))))) s).comp e.toAlgHom))
  have hΦ : ∀ (s : minimalPrimes A) (h : (s : Ideal A) ≤ (p : Ideal A) ⊔ (q : Ideal A))
      (x : ↥(integralClosure A (FractionRing A))),
      Φ s h x = Ideal.Quotient.factor h ((ε s).symm (e x s)) := fun _ _ _ => rfl
  set Ψ : ↥(integralClosure A (FractionRing A)) →ₗ[A] A ⧸ ((p : Ideal A) ⊔ (q : Ideal A)) :=
    (Φ p le_sup_left).toLinearMap - (Φ q le_sup_right).toLinearMap with hΨdef
  have hΨ : ∀ x, Ψ x = Ideal.Quotient.factor (le_sup_left : (p : Ideal A) ≤ _)
        ((ε p).symm (e x p)) -
      Ideal.Quotient.factor (le_sup_right : (q : Ideal A) ≤ _) ((ε q).symm (e x q)) :=
    fun _ => rfl
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨e.symm (Pi.single p (ε p (Ideal.Quotient.mk (p : Ideal A) a))), ?_⟩
    rw [hΨ]
    have hp : e (e.symm (Pi.single p (ε p (Ideal.Quotient.mk (p : Ideal A) a)))) p =
        ε p (Ideal.Quotient.mk (p : Ideal A) a) := by
      rw [e.apply_symm_apply]; exact Pi.single_eq_same _ _
    have hq : e (e.symm (Pi.single p (ε p (Ideal.Quotient.mk (p : Ideal A) a)))) q = 0 := by
      rw [e.apply_symm_apply]; exact Pi.single_eq_of_ne (Ne.symm hpq) _
    rw [hp, hq, (ε p).symm_apply_apply, map_zero, map_zero, sub_zero]
    rfl
  have hεc : ∀ (s : minimalPrimes A) (a : A),
      (ε s).symm (e (algebraMap A ↥(integralClosure A (FractionRing A)) a) s) =
        Ideal.Quotient.mk (s : Ideal A) a := by
    intro s a
    rw [AlgEquiv.commutes]
    exact (ε s).symm_apply_eq.mpr rfl
  have hker : LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) ≤
      LinearMap.ker Ψ := by
    rintro - ⟨a, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    rw [hΨ, show Algebra.linearMap A ↥(integralClosure A (FractionRing A)) a =
      algebraMap A _ a from rfl, hεc p a, hεc q a]
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, sub_self]
  have hliftsurj : Function.Surjective (Submodule.liftQ
      (LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A)))) Ψ hker) := by
    intro y
    obtain ⟨x, rfl⟩ := hΨsurj y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  exact Module.length_le_of_surjective _ hliftsurj

/-- Two distinct minimal primes of a reduced local ring with finitely many minimal primes and
delta invariant one sum to the maximal ideal. -/
public theorem sup_eq_maximalIdeal_of_deltaInvariant_eq_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : (minimalPrimes A).Finite)
    {p q : minimalPrimes A} (hpq : p ≠ q)
    (hδ : Ring.deltaInvariant A = 1) :
    (p : Ideal A) ⊔ (q : Ideal A) = IsLocalRing.maximalIdeal A := by
  classical
  have hprime : ∀ s : minimalPrimes A, (s : Ideal A).IsPrime := fun s => s.property.left.left
  have hle : (p : Ideal A) ⊔ (q : Ideal A) ≤ IsLocalRing.maximalIdeal A :=
    sup_le (IsLocalRing.le_maximalIdeal (hprime p).ne_top)
      (IsLocalRing.le_maximalIdeal (hprime q).ne_top)
  have hlen : Module.length A (A ⧸ ((p : Ideal A) ⊔ (q : Ideal A))) ≤ 1 := by
    rw [← hδ]
    exact length_quotient_sup_minimalPrimes_le_deltaInvariant A hA hpq hδ
  by_contra hne
  have hlt : (p : Ideal A) ⊔ (q : Ideal A) < IsLocalRing.maximalIdeal A := lt_of_le_of_ne hle hne
  set I : Ideal A := (p : Ideal A) ⊔ (q : Ideal A) with hIdef
  set M : Submodule A (A ⧸ I) := Submodule.map I.mkQ (IsLocalRing.maximalIdeal A) with hMdef
  have hMbot : M ≠ ⊥ := by
    obtain ⟨z, hzm, hzI⟩ := IsConcreteLE.exists_of_lt hlt
    intro hM
    have : I.mkQ z ∈ M := Submodule.mem_map_of_mem hzm
    rw [hM, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact hzI this
  have hMtop : M ≠ ⊤ := by
    intro hM
    rw [hMdef, Submodule.map_mkQ_eq_top] at hM
    exact IsLocalRing.maximalIdeal.isMaximal A |>.ne_top (by
      rwa [sup_eq_right.mpr hle] at hM)
  have h01 : (⊥ : Submodule A (A ⧸ I)) < M := lt_of_le_of_ne bot_le (Ne.symm hMbot)
  have h12 : M < (⊤ : Submodule A (A ⧸ I)) := lt_of_le_of_ne le_top hMtop
  let c : LTSeries (Submodule A (A ⧸ I)) :=
    RelSeries.fromListIsChain [⊥, M, ⊤] (by simp)
      (List.IsChain.cons_cons h01 (List.isChain_pair.mpr h12))
  have hclen : c.length = 2 := by simp [c]
  have hdim : (2 : WithBot ℕ∞) ≤ Order.krullDim (Submodule A (A ⧸ I)) := by
    have := Order.LTSeries.length_le_krullDim c
    rwa [hclen] at this
  rw [← Module.coe_length] at hdim
  have : (2 : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) :=
    hdim.trans (by exact_mod_cast hlen)
  norm_num at this

/-- Two distinct ideals in `minimalPrimes A`, for a reduced local ring `A` with finitely many
minimal primes and delta invariant one, sum to the maximal ideal. -/
public theorem sup_eq_maximalIdeal_of_mem_minimalPrimes_of_deltaInvariant_eq_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : (minimalPrimes A).Finite)
    {p q : Ideal A} (hp : p ∈ minimalPrimes A) (hq : q ∈ minimalPrimes A) (hpq : p ≠ q)
    (hδ : Ring.deltaInvariant A = 1) :
    p ⊔ q = IsLocalRing.maximalIdeal A :=
  sup_eq_maximalIdeal_of_deltaInvariant_eq_one A hA (p := ⟨p, hp⟩) (q := ⟨q, hq⟩)
    (fun h => hpq (Subtype.ext_iff.mp h)) hδ

end Ring

end
