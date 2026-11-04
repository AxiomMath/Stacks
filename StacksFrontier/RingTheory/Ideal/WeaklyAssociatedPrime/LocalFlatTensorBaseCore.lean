module

public import StacksFrontier.RingTheory.Flat.MittagLeffler
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.ProjectiveClosedFibre

/-!
# The coordinate argument behind the base clause of Stacks 05IH

Let `R` be a ring with an ideal `𝔭`, let `A` be an `R`-algebra, `P` an `A`-module and `q` an
ideal of `A`. Suppose given a flat `A`-algebra `A'` over a local ring `R'` with `𝔭 R' = 𝔪_{R'}`,
a proper ideal of `A'` containing `q A'`, and a base change `P'` of `P` to `A'` which is *free*
over `R'`; suppose moreover that every element of `A` outside `q` acts injectively on `P / 𝔭 P`
up to elements of `A` which become units in `A'` (the *key observation* of the proof of
[Stacks, Tag 05IG]). This is what an elementary étale neighbourhood as in [Stacks, Tag 05KZ]
provides.

This file proves: if `w ∈ P ⊗_R M` has annihilator in `A` contained in `q`, and for every
`f ∈ 𝔭` some power `f^k` kills `w` up to an element of `A` outside `q`, then there is a nonzero
`y ∈ R' ⊗_R M` killed by a power of every element of `𝔭`.

## The argument

The image `w'` of `w` in `P' ⊗_R M` is nonzero: the cyclic submodule `A w` is `A / Ann(w)`, its
base change `A' / Ann(w) A'` is nonzero because `Ann(w) A'` lies in a proper ideal, and `A'` is
flat. If `t f^k w = 0` with `t ∉ q`, then `t f^k w' = 0`, and multiplication by `t` on the free
`R'`-module `P'` is injective modulo `𝔪_{R'} = 𝔭 R'` (the key observation, carried to `P'` by
flatness of `A'`), hence universally injective by [Stacks, Tag 05FQ]; so `f^k w' = 0`. A basis
of `P'` writes `P' ⊗_R M` as a direct sum of copies of `R' ⊗_R M`, and a nonzero coordinate of
`w'` is the element sought.

## Main results

* `Stacks.WeaklyAssociatedPrimes.exists_ne_zero_pow_smul_eq_zero_of_isBaseChange_free`

## References

* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05FQ](https://stacks.math.columbia.edu/tag/05FQ)
-/

@[expose] public section

open TensorProduct IsLocalRing

universe u

namespace Stacks.WeaklyAssociatedPrimes

section KeyObservation

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {P : Type u} [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]
  {A' : Type u} [CommRing A'] [Algebra A A'] [Module.Flat A A'] [Algebra R A']
  [IsScalarTower R A A']
  {P' : Type u} [AddCommGroup P'] [Module A' P'] [Module A P'] [IsScalarTower A A' P']
  [Module R P'] [IsScalarTower R A' P'] [IsScalarTower R A P']

/-- Scalar multiplication by a commuting ring preserves `I • ⊤`. -/
private theorem smul_mem_smul_top_of_mem {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (I : Ideal R) (a : S) {x : N}
    (hx : x ∈ I • (⊤ : Submodule R N)) : a • x ∈ I • (⊤ : Submodule R N) := by
  induction hx using Submodule.smul_induction_on' with
  | smul r hr z _ =>
      rw [smul_comm]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
  | add z _ z' _ hz hz' => rw [smul_add]; exact Submodule.add_mem _ hz hz'

/-- **The key observation survives a flat base change.** Let `I` be an ideal of `R` and `t ∈ A`.
Suppose `t` acts injectively on `P / I P` up to elements of `A` which become units in `A'`: if
`t p ∈ I P` then `s p ∈ I P` for some such `s`. Then the image of `t` in `A'` acts injectively
on `P' / I P'` for any base change `P'` of `P` along a flat `A → A'`. -/
theorem smul_mem_smul_top_imp_of_isBaseChange (I : Ideal R) (t : A)
    (ht : ∀ p : P, t • p ∈ I • (⊤ : Submodule R P) →
      ∃ s : A, IsUnit (algebraMap A A' s) ∧ s • p ∈ I • (⊤ : Submodule R P))
    (ι : P →ₗ[A] P') (hι : IsBaseChange A' ι) (x : P')
    (hx : algebraMap A A' t • x ∈ I • (⊤ : Submodule R P')) :
    x ∈ I • (⊤ : Submodule R P') := by
  classical
  -- the saturation of `I P` along the elements becoming units in `A'`
  let K : Submodule A P :=
    { carrier := {p | ∃ s : A, IsUnit (algebraMap A A' s) ∧ s • p ∈ I • (⊤ : Submodule R P)}
      add_mem' := by
        rintro p₁ p₂ ⟨s₁, hs₁, h₁⟩ ⟨s₂, hs₂, h₂⟩
        refine ⟨s₁ * s₂, by rw [map_mul]; exact hs₁.mul hs₂, ?_⟩
        rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
        exact Submodule.add_mem _ (smul_mem_smul_top_of_mem I _ h₁)
          (smul_mem_smul_top_of_mem I _ h₂)
      zero_mem' := ⟨1, by simp, by simp⟩
      smul_mem' := by
        rintro a p ⟨s, hs, h⟩
        exact ⟨s, hs, by rw [smul_comm]; exact smul_mem_smul_top_of_mem I _ h⟩ }
  have hmemK : ∀ p : P, p ∈ K ↔
      ∃ s : A, IsUnit (algebraMap A A' s) ∧ s • p ∈ I • (⊤ : Submodule R P) := fun _ => Iff.rfl
  have hIK : ∀ p : P, p ∈ I • (⊤ : Submodule R P) → p ∈ K := fun p hp =>
    ⟨1, by simp, by rwa [one_smul]⟩
  set e := hι.equiv
  set π : A' ⊗[A] P →ₗ[A'] A' ⊗[A] (P ⧸ K) := K.mkQ.baseChange A' with hπ
  -- `I` kills `A' ⊗[A] (P ⧸ K)`
  have hkill : ∀ (r : R), r ∈ I → ∀ y : A' ⊗[A] (P ⧸ K), algebraMap R A' r • y = 0 := by
    intro r hr y
    induction y with
    | zero => simp
    | add y y' hy hy' => rw [smul_add, hy, hy', add_zero]
    | tmul a p =>
        obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ p
        rw [IsScalarTower.algebraMap_apply R A A', smul_tmul', algebraMap_smul,
          smul_tmul, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).mpr,
          tmul_zero]
        rw [algebraMap_smul]
        exact hIK _ (Submodule.smul_mem_smul hr Submodule.mem_top)
  -- elements of `I • ⊤` in `P'` die in `A' ⊗[A] (P ⧸ K)`
  have hdie : ∀ x : P', x ∈ I • (⊤ : Submodule R P') → π (e.symm x) = 0 := by
    intro x hx
    induction hx using Submodule.smul_induction_on' with
    | smul r hr y _ =>
        rw [← algebraMap_smul A' r y, map_smul, map_smul, hkill r hr]
    | add x _ y _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  -- the kernel of `π` lands in `I • ⊤`
  have hker : ∀ y : A' ⊗[A] P, π y = 0 → e y ∈ I • (⊤ : Submodule R P') := by
    intro y hy
    have hex : Function.Exact (K.subtype.lTensor A') (K.mkQ.lTensor A') :=
      lTensor_exact A' (LinearMap.exact_subtype_mkQ K) (Submodule.mkQ_surjective K)
    obtain ⟨y₀, rfl⟩ := (hex y).mp (by simpa [hπ, LinearMap.baseChange_eq_ltensor] using hy)
    clear hy
    induction y₀ with
    | zero => simp
    | add y y' hy hy' => rw [map_add, map_add]; exact Submodule.add_mem _ hy hy'
    | tmul a k =>
        rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, IsBaseChange.equiv_tmul]
        obtain ⟨s, hs, hsk⟩ := (hmemK k).mp k.2
        apply smul_mem_smul_top_of_mem I a
        have h1 : algebraMap A A' s • ι k ∈ I • (⊤ : Submodule R P') := by
          rw [algebraMap_smul, ← map_smul]
          exact Submodule.smul_top_le_comap_smul_top I (ι.restrictScalars R) hsk
        obtain ⟨u, hu⟩ := hs
        have := smul_mem_smul_top_of_mem I (↑u⁻¹ : A') h1
        rwa [← hu, smul_smul, Units.inv_mul, one_smul] at this
  -- multiplication by `t` on `A' ⊗[A] (P ⧸ K)` is injective
  set τ : (P ⧸ K) →ₗ[A] (P ⧸ K) := t • LinearMap.id with hτ
  have hτinj : Function.Injective τ := by
    intro p₁ p₂ h
    obtain ⟨p₁, rfl⟩ := Submodule.Quotient.mk_surjective _ p₁
    obtain ⟨p₂, rfl⟩ := Submodule.Quotient.mk_surjective _ p₂
    simp only [hτ, LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq, ← smul_sub] at h ⊢
    obtain ⟨s, hs, hst⟩ := (hmemK _).mp h
    rw [smul_comm] at hst
    obtain ⟨s', hs', hs't⟩ := ht _ hst
    refine (hmemK _).mpr ⟨s' * s, by rw [map_mul]; exact hs'.mul hs, ?_⟩
    rwa [mul_smul]
  have hτ' : Function.Injective (τ.lTensor A') :=
    Module.Flat.lTensor_preserves_injective_linearMap τ hτinj
  have hcomm : ∀ y : A' ⊗[A] P, π (algebraMap A A' t • y) = τ.lTensor A' (π y) := by
    intro y
    induction y with
    | zero => simp
    | add y y' hy hy' => rw [smul_add, map_add, hy, hy', map_add, map_add]
    | tmul a p =>
        rw [smul_tmul', algebraMap_smul, smul_tmul]
        simp [hπ, hτ]
  apply (e.apply_symm_apply x) ▸ hker _ ?_
  apply hτ'
  rw [map_zero, ← hcomm, ← map_smul, hdie _ hx]

end KeyObservation

/-- **The coordinate argument.** Under a key observation for `P` at `q`, a free base change of
`P` over an `R'` with `𝔭 R' = 𝔪_{R'}`, along a flat `A → A'` with a proper ideal of `A'`
above `q`, turns an element of `P ⊗_R M` whose annihilator lies in `q` and which is killed by a
power of every element of `𝔭` up to elements outside `q`, into a nonzero element of `R' ⊗_R M`
killed by a power of every element of `𝔭`. -/
theorem exists_ne_zero_pow_smul_eq_zero_of_isBaseChange_free
    {R : Type u} [CommRing R] (𝔭 : Ideal R)
    {A : Type u} [CommRing A] [Algebra R A]
    {P : Type u} [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]
    (q : Ideal A)
    {R' : Type u} [CommRing R'] [IsLocalRing R'] [Algebra R R']
    (hmax : 𝔭.map (algebraMap R R') = maximalIdeal R')
    {A' : Type u} [CommRing A'] [Algebra A A'] [Module.Flat A A'] [Algebra R' A']
    [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
    (q' : Ideal A') (hq' : q.map (algebraMap A A') ≤ q') (hq'top : q' ≠ ⊤)
    {P' : Type u} [AddCommGroup P'] [Module A' P'] [Module A P'] [IsScalarTower A A' P']
    [Module R' P'] [IsScalarTower R' A' P'] [Module R P'] [IsScalarTower R A' P']
    [IsScalarTower R A P'] [IsScalarTower R R' P'] [Module.Free R' P']
    (ι : P →ₗ[A] P') (hι : IsBaseChange A' ι)
    (hKO : ∀ t : A, t ∉ q → ∀ p : P, t • p ∈ 𝔭 • (⊤ : Submodule R P) →
      ∃ s : A, IsUnit (algebraMap A A' s) ∧ s • p ∈ 𝔭 • (⊤ : Submodule R P))
    {M : Type u} [AddCommGroup M] [Module R M]
    (w : P ⊗[R] M) (hwq : ∀ a : A, a • w = 0 → a ∈ q)
    (hwf : ∀ f ∈ 𝔭, ∃ k : ℕ, ∃ t : A, t ∉ q ∧ t • (f ^ k • w) = 0) :
    ∃ y : R' ⊗[R] M, y ≠ 0 ∧ ∀ f ∈ 𝔭, ∃ k : ℕ, f ^ k • y = 0 := by
  classical
  set j : P ⊗[R] M →ₗ[A] P' ⊗[R] M := AlgebraTensorModule.map ι LinearMap.id with hj
  have hjb : IsBaseChange A' j := isBaseChange_tensorProduct_map (P := M) A' hι
  set w' : P' ⊗[R] M := j w with hw'
  -- Step A: `w' ≠ 0`
  have hw'0 : w' ≠ 0 := by
    intro h0
    have h1 : (1 : A') ⊗ₜ[A] w = 0 := by
      apply hjb.equiv.injective
      rw [IsBaseChange.equiv_tmul, one_smul, map_zero]
      exact h0
    set C : Submodule A (P ⊗[R] M) := A ∙ w with hC
    have hinj : Function.Injective (C.subtype.lTensor A') :=
      Module.Flat.lTensor_preserves_injective_linearMap C.subtype C.injective_subtype
    have h2 : (1 : A') ⊗ₜ[A] (⟨w, Submodule.mem_span_singleton_self w⟩ : C) = 0 :=
      hinj (by simpa using h1)
    set I : Ideal A := Ideal.torsionOf A (P ⊗[R] M) w with hI
    let eC := Ideal.quotTorsionOfEquivSpanSingleton A (P ⊗[R] M) w
    have he1 : eC (Submodule.Quotient.mk 1) = ⟨w, Submodule.mem_span_singleton_self w⟩ := by
      rw [Ideal.quotTorsionOfEquivSpanSingleton_apply_mk, one_smul]
    have h3 : ((1 : A') ⊗ₜ[A] (Ideal.Quotient.mk I 1) : A' ⊗[A] (A ⧸ I)) = 0 := by
      have := congrArg (eC.symm.lTensor A') h2
      rw [LinearEquiv.lTensor_tmul, ← he1, LinearEquiv.symm_apply_apply, map_zero] at this
      exact this
    have h4 := congrArg (tensorQuotEquivQuotSMul A' I) h3
    rw [tensorQuotEquivQuotSMul_tmul_mk, one_smul, map_zero, Submodule.Quotient.mk_eq_zero] at h4
    apply hq'top
    rw [Ideal.eq_top_iff_one]
    clear h1 h2 h3 he1
    suffices hsuff : ∀ x ∈ I • (⊤ : Submodule A A'), x ∈ q' from hsuff 1 h4
    intro x hx
    induction hx using Submodule.smul_induction_on' with
    | smul a ha b _ =>
        rw [Algebra.smul_def]
        exact q'.mul_mem_right b (hq' (Ideal.mem_map_of_mem _
          (hwq a ((Ideal.mem_torsionOf_iff _ _).mp ha))))
    | add x _ y _ hx hy => exact q'.add_mem hx hy
  -- Step B: `f ^ k • w' = 0`
  have hkill : ∀ f ∈ 𝔭, ∃ k : ℕ, f ^ k • w' = 0 := by
    intro f hf
    obtain ⟨k, t, htq, ht⟩ := hwf f hf
    refine ⟨k, ?_⟩
    set a' : A' := algebraMap A A' t
    set u : P' →ₗ[R'] P' := a' • LinearMap.id with hu
    have hu' : ∀ x : P', u x ∈ maximalIdeal R' • (⊤ : Submodule R' P') →
        x ∈ maximalIdeal R' • (⊤ : Submodule R' P') := by
      intro x hx
      rw [← hmax, ← mem_smul_top_iff_mem_map_smul_top] at hx ⊢
      exact smul_mem_smul_top_imp_of_isBaseChange 𝔭 t (hKO t htq) ι hι x hx
    have huinj := Module.Flat.rTensor_injective_of_projective_of_mem_maximalIdeal_smul_top u hu'
      (R' ⊗[R] M)
    set c := AlgebraTensorModule.cancelBaseChange R R' R' P' M
    have hcu : ∀ y : P' ⊗[R'] (R' ⊗[R] M), c (u.rTensor (R' ⊗[R] M) y) = t • c y := by
      intro y
      induction y with
      | zero => simp
      | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, smul_add]
      | tmul p z =>
          induction z with
          | zero => simp
          | add z z' hz hz' => rw [tmul_add, map_add, map_add, hz, hz', map_add, smul_add]
          | tmul r m =>
              simp only [LinearMap.rTensor_tmul, hu, LinearMap.smul_apply, LinearMap.id_apply, c,
                AlgebraTensorModule.cancelBaseChange_tmul]
              rw [smul_tmul', smul_comm r a' p, ← algebraMap_smul A' t (r • p)]
    have hjf : f ^ k • j w = j (f ^ k • w) := by
      rw [← algebraMap_smul A (f ^ k) w, map_smul, algebraMap_smul]
    have h1 : t • (f ^ k • w') = 0 := by
      rw [hw', hjf, ← map_smul, ht, map_zero]
    apply c.symm.injective
    apply huinj
    apply c.injective
    rw [map_zero, map_zero, hcu, c.apply_symm_apply, h1, map_zero]
  -- Step C: coordinates
  obtain ⟨ι', b⟩ := Module.Free.exists_basis (R := R') (M := P')
  set eb : P' ⊗[R] M ≃ₗ[R] ι' →₀ (R' ⊗[R] M) :=
    (TensorProduct.congr (b.repr.restrictScalars R) (LinearEquiv.refl R M)).trans
      ((TensorProduct.finsuppLeft R R' R' M ι').restrictScalars R) with heb
  have hne : eb w' ≠ 0 := fun h => hw'0 (eb.injective (h.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  refine ⟨eb w' i, hi, fun f hf => ?_⟩
  obtain ⟨k, hk⟩ := hkill f hf
  refine ⟨k, ?_⟩
  have h := congrArg eb hk
  rw [map_smul, map_zero] at h
  simpa using congrArg (fun g => g i) h

end Stacks.WeaklyAssociatedPrimes

end
