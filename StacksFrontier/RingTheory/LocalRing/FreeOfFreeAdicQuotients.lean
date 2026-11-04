module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksFrontier.RingTheory.AdicTorsion.PowerQuotient

/-!
# Freeness of a finite module from freeness of the quotients by the powers of a regular parameter

Let `R` be a Noetherian local ring, let `t` be an element of its maximal ideal which is a
nonzerodivisor of `R`, and let `M` be a finite `R`-module.  If every quotient `M / tⁿ⁺¹M` is a
finite free `R / (tⁿ⁺¹)`-module, then `M` is free over `R`.

The hypothesis is recorded as a merely `R`-linear equivalence `M / tⁿ⁺¹M ≃ (R / (tⁿ⁺¹))ʳ`, which
is no loss of generality: the ring map `R → R / (tⁿ⁺¹)` is surjective, so an `R`-linear map
between two `R / (tⁿ⁺¹)`-modules is automatically `R / (tⁿ⁺¹)`-linear.

The proof has two halves.  The powers `n ≥ 1` serve only to show that `t` is a nonzerodivisor on
`M`: if `t • x = 0`, the class of `x` in `M / tⁿ⁺¹M` is killed by `t`, and in a free
`R / (tⁿ⁺¹)`-module an element killed by `t` is `tⁿ` times an element, because in `R / (tⁿ⁺¹)`
this follows from cancelling one factor of the nonzerodivisor `t`.  Hence
`x ∈ tⁿM + tⁿ⁺¹M = tⁿM` for every `n`, so `x` lies in `⋂ₙ (t)ⁿM`, which vanishes by Krull's
intersection theorem.  Granted that, the case `n = 0` finishes the argument: `t` lies in the
Jacobson radical of `R` because `R` is local, `M` is finitely presented because `R` is
Noetherian, and freeness of `M / tM` over `R / (t)` lifts to freeness of `M` over `R`.

## Main results

* `Module.free_of_free_quotient_pow_smul` — a finite module over a Noetherian local ring all of
  whose quotients by the powers of a regular parameter in the maximal ideal are finite free is
  free.
-/

@[expose] public section

open scoped Pointwise

universe u

namespace Module

variable {R : Type u} [CommRing R]

/-- **A regular parameter with finite free adic quotients is a nonzerodivisor on the module.**
If `t • x = 0`, then the class of `x` in `M / tⁿ⁺¹M` is killed by `t`, hence is `tⁿ` times a
class; so `x ∈ tⁿM + tⁿ⁺¹M = tⁿM` for every `n`.  Krull's intersection theorem for a finite
module over a Noetherian local ring then gives `x = 0`. -/
private theorem isSMulRegular_of_free_quotient_pow_smul [IsNoetherianRing R] [IsLocalRing R]
    {t : R} (ht : t ∈ IsLocalRing.maximalIdeal R) (htreg : t ∈ nonZeroDivisors R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : ∀ n : ℕ, ∃ r : ℕ,
      Nonempty ((M ⧸ (Ideal.span {t ^ (n + 1)} • (⊤ : Submodule R M))) ≃ₗ[R]
        (Fin r → (R ⧸ Ideal.span {t ^ (n + 1)})))) :
    IsSMulRegular M t := by
  refine IsSMulRegular.of_right_eq_zero_of_smul fun x hx => ?_
  have key : ∀ n : ℕ, x ∈ (Ideal.span {t} : Ideal R) ^ n • (⊤ : Submodule R M) := by
    intro n
    obtain ⟨r, ⟨e⟩⟩ := h n
    have hbar : t • (Ideal.span {t ^ (n + 1)} • (⊤ : Submodule R M)).mkQ x = 0 := by
      rw [← map_smul, hx, map_zero]
    obtain ⟨y, hy⟩ :=
      Stacks.AdicTorsion.exists_eq_pow_smul_of_smul_eq_zero_of_linearEquiv htreg n r rfl e hbar
    obtain ⟨z, hz⟩ := Submodule.mkQ_surjective _ y
    have hmem : x - t ^ n • z ∈ Ideal.span {t ^ (n + 1)} • (⊤ : Submodule R M) := by
      rw [← Submodule.ker_mkQ (Ideal.span {t ^ (n + 1)} • (⊤ : Submodule R M)), LinearMap.mem_ker,
        map_sub, map_smul, hz, hy, sub_self]
    have hle : Ideal.span {t ^ (n + 1)} • (⊤ : Submodule R M) ≤
        Ideal.span {t ^ n} • (⊤ : Submodule R M) :=
      Submodule.smul_mono_left
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow t (Nat.le_succ n)))
    have hx2 : x = x - t ^ n • z + t ^ n • z := by abel
    rw [Ideal.span_singleton_pow, hx2]
    exact add_mem (hle hmem)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
  have hIne : (Ideal.span {t} : Ideal R) ≠ ⊤ := fun hc =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (hc.ge.trans (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ht))))
  have hbot :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := (Ideal.span {t} : Ideal R)) (M := M) hIne
  have hx' : x ∈ (⊥ : Submodule R M) := by
    rw [← hbot]
    exact (Submodule.mem_iInf _).mpr key
  simpa using hx'

/-- **A finite module over a Noetherian local ring whose quotients by the powers of a regular
parameter are finite free is free.** Let `R` be a Noetherian local ring, `t` a nonzerodivisor of
`R` lying in the maximal ideal, and `M` a finite `R`-module such that every `M / tⁿ⁺¹M` is
`R`-linearly isomorphic to a finite power of `R / (tⁿ⁺¹)`.  Then `M` is a free `R`-module.

The powers `n ≥ 1` are used only to see that `t` is a nonzerodivisor on `M`; the case `n = 0`
then upgrades freeness of `M / tM` over `R / (t)` to freeness of `M` over `R`, Nakayama's lemma
being available because `t` lies in the Jacobson radical of the local ring `R`. -/
theorem free_of_free_quotient_pow_smul {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {t : R} (ht : t ∈ IsLocalRing.maximalIdeal R)
    (htreg : t ∈ nonZeroDivisors R) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (h : ∀ n : ℕ, ∃ r : ℕ,
      Nonempty ((M ⧸ (Ideal.span {t ^ (n + 1)} • (⊤ : Submodule R M))) ≃ₗ[R]
        (Fin r → (R ⧸ Ideal.span {t ^ (n + 1)})))) :
    Module.Free R M := by
  have hreg : IsSMulRegular M t := isSMulRegular_of_free_quotient_pow_smul ht htreg M h
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  refine (Module.free_quotSMulTop_iff_free R M (IsLocalRing.maximalIdeal_le_jacobson _ ht)
    hreg).mp ?_
  obtain ⟨r, ⟨e⟩⟩ := h 0
  have hsub : (Ideal.span {t ^ (0 + 1)} : Ideal R) • (⊤ : Submodule R M)
      = t • (⊤ : Submodule R M) := by
    rw [zero_add, pow_one, Submodule.ideal_span_singleton_smul]
  have hspan : (Ideal.span {t ^ (0 + 1)} : Ideal R) = Ideal.span {t} := by rw [zero_add, pow_one]
  let eM : QuotSMulTop t M ≃ₗ[R] (Fin r → R ⧸ (Ideal.span {t} : Ideal R)) :=
    (Submodule.quotEquivOfEq _ _ hsub).symm ≪≫ₗ e ≪≫ₗ
      LinearEquiv.piCongrRight fun _ => Submodule.quotEquivOfEq _ _ hspan
  exact Module.Free.of_equiv
    (eM.extendScalarsOfSurjective (S := R ⧸ (Ideal.span {t} : Ideal R))
      Ideal.Quotient.mk_surjective).symm

end Module

end
