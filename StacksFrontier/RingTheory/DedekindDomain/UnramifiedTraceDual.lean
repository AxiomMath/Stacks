module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# An everywhere unramified extension of Dedekind domains is self-dual for the trace

Let `A ⊆ B` be Dedekind domains with fraction fields `K ⊆ L`, `L / K` finite separable and `B`
the integral closure of `A` in `L`. If `B` is unramified over `A` at every prime, the different
ideal of `B / A` is the unit ideal, so the trace dual `{x ∈ L | Tr(x B) ⊆ A}` of `B` is `B`
itself.

## Main results

* `differentIdeal_eq_top_of_forall_isUnramifiedAt`: the different is the unit ideal.
* `mem_range_of_forall_traceForm_mem_range`: the self-duality.
-/

@[expose] public noncomputable section

open Module

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A K L B : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDedekindDomain A] [IsFractionRing A K] [IsDedekindDomain B] [IsFractionRing B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
  [Module.IsTorsionFree A B]

include K L in
/-- **The different of an everywhere unramified extension is the unit ideal.** -/
theorem differentIdeal_eq_top_of_forall_isUnramifiedAt
    (hunr : ∀ (P : Ideal B) [P.IsPrime], Algebra.IsUnramifiedAt A P) :
    differentIdeal A B = ⊤ := by
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hdvd : P ∣ differentIdeal A B := Ideal.dvd_iff_le.mpr hle
  exact (not_dvd_differentIdeal_iff (A := A) (P := P)).mpr (hunr P) hdvd

/-- **Self-duality.** If `B` is unramified over `A` at every prime, every `x ∈ L` whose trace
pairing with `B` lands in `A` lies in `B`. -/
theorem mem_range_of_forall_traceForm_mem_range
    (hunr : ∀ (P : Ideal B) [P.IsPrime], Algebra.IsUnramifiedAt A P) {x : L}
    (hx : ∀ y : B, Algebra.trace K L (x * algebraMap B L y) ∈ (algebraMap A K).range) :
    x ∈ (algebraMap B L).range := by
  have hdiff := differentIdeal_eq_top_of_forall_isUnramifiedAt A K L B hunr
  have h1 := coeIdeal_differentIdeal A K L B
  rw [hdiff, FractionalIdeal.coeIdeal_top, eq_comm, inv_eq_one] at h1
  have h2 : Submodule.traceDual A K (1 : Submodule B L) = 1 := by
    rw [← FractionalIdeal.coe_dual_one, h1, FractionalIdeal.coe_one]
  have hmem : x ∈ Submodule.traceDual A K (1 : Submodule B L) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
    rw [Algebra.traceForm_apply]
    exact hx y
  rw [h2] at hmem
  obtain ⟨y, rfl⟩ := Submodule.mem_one.mp hmem
  exact ⟨y, rfl⟩

end
