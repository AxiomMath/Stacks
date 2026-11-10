module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Detecting injectivity and surjectivity after flat base change

Two pieces of commutative algebra used to check properties of maps of quasi-coherent modules on
flat coverings.

*Jointly faithfully flat families.*  Let `A ⟶ B k` be a family of flat ring maps such that every
prime of `A` is the contraction of a prime of some `B k`.  Then an element `m` of an `A`-module
with `1 ⊗ m = 0` in every `B k ⊗_A M` is zero.  No finiteness of the family is needed: the
annihilator of `m` is contained in a maximal ideal `𝔭` if `m ≠ 0`, flatness makes
`B ⊗_A A/Ann(m) ⟶ B ⊗_A M` injective, so `1 ∈ Ann(m) B`, which is impossible when a prime of `B`
lies over `𝔭`.

*Maps compatible with base change.*  Let `A ⟶ B` be a ring map, let `f : M ⟶ N` be `A`-linear
and `f' : M' ⟶ N'` be `B`-linear, and let `r_M : M ⟶ M'`, `r_N : N ⟶ N'` be `A`-linear maps with
`f' ∘ r_M = r_N ∘ f` whose `B`-linear extensions `B ⊗_A M ⟶ M'` and `B ⊗_A N ⟶ N'` are
bijective.  Then `f'` is `B ⊗ f` up to these identifications, so it is surjective, resp.
bijective, when `f` is, and injective when `f` is and `B` is flat over `A`; and an element of `M`
killed by `r_M`, resp. of `N` whose image under `r_N` is in the range of `f'`, becomes zero in
`B ⊗_A M`, resp. in `B ⊗_A coker f`.

## Main results

* `Module.eq_zero_of_forall_one_tmul_eq_zero`: the vanishing criterion for a jointly faithfully
  flat family.
* `LinearMap.injective_of_liftBaseChange_of_flat`, `LinearMap.surjective_of_liftBaseChange` and
  `LinearMap.bijective_of_liftBaseChange`: the three transfer statements.
* `LinearMap.one_tmul_eq_zero_of_liftBaseChange` and
  `LinearMap.one_tmul_mkQ_eq_zero_of_liftBaseChange`: the two vanishing statements.
-/

@[expose] public section

open TensorProduct

namespace Module

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- **An element vanishing after base change along a jointly faithfully flat family is zero.**
Let `A ⟶ B k` be flat ring maps such that every prime of `A` is the contraction of a prime of
some `B k`.  If `1 ⊗ m = 0` in `B k ⊗_A M` for every `k`, then `m = 0`. -/
theorem eq_zero_of_forall_one_tmul_eq_zero {K : Type*} (B : K → Type*) [∀ k, CommRing (B k)]
    [∀ k, Algebra A (B k)] [∀ k, Module.Flat A (B k)]
    (hsurj : ∀ P : PrimeSpectrum A, ∃ k, ∃ Q : PrimeSpectrum (B k),
      Q.asIdeal.comap (algebraMap A (B k)) = P.asIdeal)
    {m : M} (hm : ∀ k, (1 : B k) ⊗ₜ[A] m = 0) : m = 0 := by
  classical
  by_contra hne
  let f : A →ₗ[A] M := LinearMap.toSpanSingleton A M m
  let I : Ideal A := LinearMap.ker f
  have hI : I ≠ ⊤ := fun h => hne (by simpa [I, f] using (h ▸ Submodule.mem_top : (1 : A) ∈ I))
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨k, Q, hQ⟩ := hsurj ⟨P, hPmax.isPrime⟩
  have h0 : (1 : B k) ⊗ₜ[A] (Submodule.Quotient.mk 1 : A ⧸ I) = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := B k) (I.liftQ f le_rfl)
      (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))
    rw [LinearMap.lTensor_tmul, map_zero, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
      one_smul]
    exact hm k
  have h1 : (Submodule.Quotient.mk (1 : B k) : B k ⧸ (I • (⊤ : Submodule A (B k)))) = 0 := by
    have := congrArg (TensorProduct.tensorQuotEquivQuotSMul (B k) I) h0
    rw [map_zero] at this
    have h2 : (Submodule.Quotient.mk 1 : A ⧸ I) = Ideal.Quotient.mk I 1 := rfl
    rw [h2, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul] at this
    exact this
  have hle : I • (⊤ : Submodule A (B k)) ≤ Q.asIdeal.restrictScalars A := by
    refine Submodule.smul_le.2 fun r hr b _ => ?_
    rw [Submodule.restrictScalars_mem, Algebra.smul_def]
    exact Q.asIdeal.mul_mem_right b (hQ.symm ▸ hIP hr : r ∈ Q.asIdeal.comap (algebraMap A (B k)))
  exact Q.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 (hle ((Submodule.Quotient.mk_eq_zero _).1 h1)))

end Module

namespace LinearMap

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
  {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {M' N' : Type*} [AddCommGroup M'] [Module B M'] [Module A M'] [IsScalarTower A B M']
  [AddCommGroup N'] [Module B N'] [Module A N'] [IsScalarTower A B N']
  (f : M →ₗ[A] N) (f' : M' →ₗ[B] N') (rM : M →ₗ[A] M') (rN : N →ₗ[A] N')
  (hrM : Function.Bijective (rM.liftBaseChange B))
  (hrN : Function.Bijective (rN.liftBaseChange B))
  (hcomm : ∀ m, f' (rM m) = rN (f m))

include hcomm in
/-- Under the identifications, `f'` is the base change of `f`. -/
theorem liftBaseChange_comp_baseChange :
    (rN.liftBaseChange B).comp (f.baseChange B) = f'.comp (rM.liftBaseChange B) := by
  ext m
  simp [hcomm]

/-- If the base change of `f` is injective, so is `f'`. -/
private theorem injective_of_baseChange_injective (hrM : Function.Bijective (rM.liftBaseChange B))
    (hrN : Function.Bijective (rN.liftBaseChange B)) (hcomm : ∀ m, f' (rM m) = rN (f m))
    (hb : Function.Injective (f.baseChange B)) : Function.Injective f' := by
  have h := liftBaseChange_comp_baseChange f f' rM rN hcomm
  intro a b hab
  obtain ⟨a, rfl⟩ := hrM.2 a
  obtain ⟨b, rfl⟩ := hrM.2 b
  congr 1
  apply hb
  apply hrN.1
  simp only [← LinearMap.comp_apply, h]
  simpa using hab

include hrM hrN hcomm in
/-- **Flat base change preserves injectivity.** -/
theorem injective_of_liftBaseChange_of_flat [Module.Flat A B] (hf : Function.Injective f) :
    Function.Injective f' :=
  injective_of_baseChange_injective f f' rM rN hrM hrN hcomm
    (Module.Flat.lTensor_preserves_injective_linearMap f hf)

include hrN hcomm in
/-- **Base change preserves surjectivity.** -/
theorem surjective_of_liftBaseChange (hf : Function.Surjective f) : Function.Surjective f' := by
  have h := liftBaseChange_comp_baseChange f f' rM rN hcomm
  have hb : Function.Surjective (f.baseChange B) := LinearMap.lTensor_surjective B hf
  intro c
  obtain ⟨c, rfl⟩ := hrN.2 c
  obtain ⟨a, rfl⟩ := hb c
  exact ⟨rM.liftBaseChange B a, by
    simpa only [LinearMap.comp_apply] using (congrArg (fun g => g a) h).symm⟩

include hrM hrN hcomm in
/-- **Base change preserves bijectivity.** -/
theorem bijective_of_liftBaseChange (hf : Function.Bijective f) : Function.Bijective f' := by
  have hb : Function.Bijective (f.baseChange B) :=
    ((LinearEquiv.ofBijective f hf).baseChange A B M N).bijective
  exact ⟨injective_of_baseChange_injective f f' rM rN hrM hrN hcomm hb.1,
    surjective_of_liftBaseChange f f' rM rN hrN hcomm hf.2⟩

include hrM in
/-- An element killed by `r_M` becomes zero in `B ⊗_A M`. -/
theorem one_tmul_eq_zero_of_liftBaseChange {m : M} (hm : rM m = 0) :
    (1 : B) ⊗ₜ[A] m = 0 := by
  apply hrM.1
  rw [LinearMap.liftBaseChange_tmul, one_smul, hm, map_zero]

include hrM hrN hcomm in
/-- An element of `N` whose image under `r_N` is in the range of `f'` becomes zero in
`B ⊗_A coker f`. -/
theorem one_tmul_mkQ_eq_zero_of_liftBaseChange {n : N} (hn : rN n ∈ LinearMap.range f') :
    (1 : B) ⊗ₜ[A] (LinearMap.range f).mkQ n = 0 := by
  have h := liftBaseChange_comp_baseChange f f' rM rN hcomm
  obtain ⟨c, hc⟩ := hn
  obtain ⟨a, rfl⟩ := hrM.2 c
  have hfa : f.baseChange B a = (1 : B) ⊗ₜ[A] n := by
    apply hrN.1
    rw [← LinearMap.comp_apply, h, LinearMap.comp_apply, hc, LinearMap.liftBaseChange_tmul,
      one_smul]
  have hzero : ((LinearMap.range f).mkQ.baseChange B).comp (f.baseChange B) = 0 := by
    rw [← LinearMap.baseChange_comp, LinearMap.range_mkQ_comp, LinearMap.baseChange_zero]
  simpa [hfa] using congrArg (fun g => g a) hzero

end LinearMap

end
