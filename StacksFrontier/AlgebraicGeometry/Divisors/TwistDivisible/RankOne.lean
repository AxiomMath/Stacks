module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Linear maps between free modules of rank one

A module `M` over a commutative ring `R` which is free of rank one on an element `α` — meaning
that `r ↦ r · α` is bijective — behaves exactly like `R` itself. This file collects the handful
of facts about such modules that the local computation of the twist inclusion
`𝒪_X(p·x) ⊂ 𝒪_X((p+1)x)` at a point needs, stated so that they can be applied to a stalk
without first naming an isomorphism with the local ring.

A linear map `φ : M ⟶ N` between two such modules is multiplication by one scalar `c`, namely
the coordinate of `φ α` on the generator `β` of `N`; its image is `(c) · N` and it is injective
as soon as `c` is a nonzerodivisor. Conversely a submodule of `N` of the form `I · N` determines
`I`, which is what turns an identity between multiples of a stalk into an identity between
ideals of the local ring. The last statement is the colength computation: over a domain, an
equation `(π)^p · (c) = (π)^(p+1)` forces `(c) = (π)`.

## Main results

* `Stacks.Divisors.TwistDivisible.exists_apply_eq_smul` and
  `Stacks.Divisors.TwistDivisible.range_eq_span_singleton`: a linear map out of a cyclic module
  is determined by one value, and its image is the span of that value.
* `Stacks.Divisors.TwistDivisible.ideal_eq_of_smul_top_eq`: **`I · N = J · N` forces `I = J`**
  for `N` free of rank one.
* `Stacks.Divisors.TwistDivisible.bijective_of_isUnit` and
  `Stacks.Divisors.TwistDivisible.injective_of_ne_zero`: multiplication by a unit is bijective,
  and multiplication by a nonzero scalar over a domain is injective.
* `Stacks.Divisors.TwistDivisible.span_eq_span_of_pow_mul`: **the colength computation**,
  `(π)^p · (c) = (π)^(p+1) ⟹ (c) = (π)` over a domain with `π ≠ 0`.
-/

@[expose] public section

namespace Stacks.Divisors.TwistDivisible

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A free generator spans. -/
theorem span_eq_top_of_surjective_smul (β : N) (hβ : Function.Surjective fun r : R => r • β) :
    Submodule.span R ({β} : Set N) = ⊤ :=
  Submodule.eq_top_iff'.mpr fun n => by
    obtain ⟨r, rfl⟩ := hβ n
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)

/-- **The span of a multiple of a free generator is that multiple of the whole module.** -/
theorem span_singleton_smul_eq (c : R) (β : N)
    (hβ : Submodule.span R ({β} : Set N) = ⊤) :
    Submodule.span R ({c • β} : Set N) = (Ideal.span {c}) • (⊤ : Submodule R N) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.smul_le.mpr ?_)
  · rintro _ rfl
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) Submodule.mem_top
  · intro r hr m _
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hm : m ∈ Submodule.span R ({β} : Set N) := hβ ▸ Submodule.mem_top
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hm
    rw [smul_smul, mul_right_comm, ← smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **The image of a linear map out of a cyclic module is the span of one value.** -/
theorem range_eq_span_singleton (φ : M →ₗ[R] N) (α : M)
    (hα : Submodule.span R ({α} : Set M) = ⊤) :
    LinearMap.range φ = Submodule.span R ({φ α} : Set N) := by
  rw [LinearMap.range_eq_map, ← hα, Submodule.map_span, Set.image_singleton]

/-- **`I · N` inside a module free of rank one on `β` is the image of `I` under `r ↦ r · β`.** -/
theorem ideal_smul_top_eq_map (β : N) (hβ : Function.Surjective fun r : R => r • β)
    (I : Ideal R) :
    I • (⊤ : Submodule R N) = Submodule.map (LinearMap.toSpanSingleton R N β) I := by
  refine le_antisymm (Submodule.smul_le.mpr ?_) ?_
  · intro r hr n _
    obtain ⟨s, rfl⟩ := hβ n
    refine ⟨r * s, Ideal.mul_mem_right _ _ hr, ?_⟩
    rw [LinearMap.toSpanSingleton_apply, mul_smul]
  · rintro n ⟨r, hr, rfl⟩
    rw [LinearMap.toSpanSingleton_apply]
    exact Submodule.smul_mem_smul hr Submodule.mem_top

/-- **Two ideals with the same multiple of a module free of rank one are equal.** The map
`r ↦ r · β` is injective, and `I · N` is the image of `I` under it. -/
theorem ideal_eq_of_smul_top_eq (β : N) (hβ : Function.Bijective fun r : R => r • β)
    {I I' : Ideal R} (h : I • (⊤ : Submodule R N) = I' • (⊤ : Submodule R N)) : I = I' := by
  have hinj : Function.Injective (LinearMap.toSpanSingleton R N β) := hβ.1
  refine Submodule.map_injective_of_injective hinj ?_
  rwa [← ideal_smul_top_eq_map β hβ.2, ← ideal_smul_top_eq_map β hβ.2]

/-- **A value in a module free of rank one is a multiple of the generator.** -/
theorem exists_apply_eq_smul (α : M) (β : N) (hβ : Function.Surjective fun r : R => r • β)
    (φ : M →ₗ[R] N) : ∃ c : R, φ α = c • β :=
  (hβ (φ α)).imp fun _ h => h.symm

/-- A linear map sending the generator `α` to `c • β` is injective if `r ↦ r * c` is. -/
private theorem injective_of_mul_right_cancel {α : M} (hα : Function.Surjective fun r : R => r • α)
    {β : N} (hβ : Function.Injective fun r : R => r • β) {φ : M →ₗ[R] N} {c : R}
    (hc : φ α = c • β) (hcancel : ∀ r r' : R, r * c = r' * c → r = r') : Function.Injective φ := by
  have happ : ∀ r : R, φ (r • α) = (r * c) • β := fun r => by
    rw [map_smul, hc, smul_smul]
  intro m m' hmm'
  obtain ⟨r, rfl⟩ := hα m
  obtain ⟨r', rfl⟩ := hα m'
  exact congrArg (· • α) (hcancel r r' (hβ ((happ r).symm.trans (hmm'.trans (happ r')))))

/-- **Multiplication by a unit between modules free of rank one is bijective.** -/
theorem bijective_of_isUnit {α : M} (hα : Function.Bijective fun r : R => r • α)
    {β : N} (hβ : Function.Bijective fun r : R => r • β) {φ : M →ₗ[R] N} {c : R}
    (hc : φ α = c • β) (hu : IsUnit c) : Function.Bijective φ := by
  obtain ⟨u, rfl⟩ := hu
  refine ⟨injective_of_mul_right_cancel hα.2 hβ.1 hc fun r r' h => (Units.mul_left_inj u).mp h,
    fun n => ?_⟩
  obtain ⟨s, rfl⟩ := hβ.2 n
  refine ⟨(s * ((u⁻¹ : Rˣ) : R)) • α, ?_⟩
  rw [map_smul, hc, smul_smul, mul_assoc, Units.inv_mul, mul_one]

/-- **Multiplication by a nonzero scalar between modules free of rank one over a domain is
injective.** -/
theorem injective_of_ne_zero [IsDomain R] {α : M} (hα : Function.Surjective fun r : R => r • α)
    {β : N} (hβ : Function.Bijective fun r : R => r • β) {φ : M →ₗ[R] N} {c : R}
    (hc : φ α = c • β) (hc0 : c ≠ 0) : Function.Injective φ :=
  injective_of_mul_right_cancel hα hβ.1 hc fun _ _ h => mul_right_cancel₀ hc0 h

/-- the unit-ideal case of the colength computation -/
theorem isUnit_of_top_pow_mul {c : R} {p : ℕ}
    (h : (⊤ : Ideal R) ^ p * Ideal.span ({c} : Set R) = (⊤ : Ideal R) ^ (p + 1)) :
    IsUnit c := by
  rw [← Ideal.one_eq_top, one_pow, one_pow, one_mul] at h
  exact Ideal.span_singleton_eq_top.mp (h.trans Ideal.one_eq_top)

/-- **The colength computation.** Over a domain, if `π ≠ 0` and `(π)^p · (c) = (π)^(p+1)` then
`(c) = (π)`: the two generators `π^p · c` and `π^(p+1)` are associated, and `π^p` cancels. -/
theorem span_eq_span_of_pow_mul [IsDomain R] {pi c : R} (hpi : pi ≠ 0) {p : ℕ}
    (h : Ideal.span ({pi} : Set R) ^ p * Ideal.span ({c} : Set R)
      = Ideal.span ({pi} : Set R) ^ (p + 1)) :
    Ideal.span ({c} : Set R) = Ideal.span ({pi} : Set R) := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_pow] at h
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  have hcu : pi ^ p * (c * (u : R)) = pi ^ p * pi := by
    rw [← mul_assoc, hu, pow_succ]
  exact Ideal.span_singleton_eq_span_singleton.mpr ⟨u, mul_left_cancel₀ (pow_ne_zero p hpi) hcu⟩

end Stacks.Divisors.TwistDivisible

end
