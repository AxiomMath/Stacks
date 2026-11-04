module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# A surjective endomorphism of a Noetherian ring is an isomorphism

Let `R` be a Noetherian commutative ring and `φ : R → R` a surjective ring
endomorphism. Then `φ` is an isomorphism; equivalently, `φ` is injective, hence
bijective.

An endomorphism of `R` is a ring homomorphism `R →+* R`, preserving addition,
multiplication and `1`. Being an isomorphism means being bijective, equivalently
admitting a two-sided inverse which is again a ring homomorphism, that is, being
witnessed by a `RingEquiv`. `R` is Noetherian when it satisfies the ascending
chain condition on ideals.

The proof considers the ascending chain of kernels
`ker φ ⊆ ker φ² ⊆ ker φ³ ⊆ ⋯`, which stabilizes by the Noetherian hypothesis,
say `ker φⁿ = ker φⁿ⁺¹`. Given `x ∈ ker φ`, surjectivity of `φ` and hence of
`φⁿ` gives `y` with `φⁿ y = x`; then `φⁿ⁺¹ y = φ x = 0`, so
`y ∈ ker φⁿ⁺¹ = ker φⁿ` and `x = φⁿ y = 0`. Thus `φ` is injective, and being
surjective as well it is a ring isomorphism.
-/

@[expose] public section

/-- A surjective ring endomorphism of a Noetherian commutative ring is injective.
This is the substantive content of Stacks Tag 06RN. -/
theorem surjective_endomorphism_noetherian_injective
    (R : Type*) [CommRing R] [IsNoetherianRing R] (φ : R →+* R)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  -- iterates of `φ`: `φ^n x = φ^[n] x`
  have hpow : ∀ n, ⇑(φ^n) = φ^[n] := fun n => RingHom.coe_pow φ n
  have hmono : Monotone (fun n : ℕ => RingHom.ker (φ^n)) := by
    intro a b hab x hx
    rw [RingHom.mem_ker, hpow] at hx ⊢
    obtain ⟨c, rfl⟩ := Nat.le.dest hab
    rw [add_comm, Function.iterate_add_apply, hx, iterate_map_zero]
  -- by Noetherian, the chain stabilizes
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R)) ⟨_, hmono⟩
  -- now show φ injective: suffices ker φ = 0
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, hy⟩ := (hφ.iterate n) x
  -- φ^(n+1) y = φ (φ^n y) = φ x = 0, so y ∈ ker φ^(n+1) = ker φ^n
  have hy1 : y ∈ RingHom.ker (φ^(n+1)) := by
    rw [RingHom.mem_ker, hpow, Function.iterate_succ_apply', hy, hx]
  have hker : y ∈ RingHom.ker (φ^n) := by
    have heq : RingHom.ker (φ^n) = RingHom.ker (φ^(n+1)) := hn (n+1) (Nat.le_succ n)
    rw [heq]; exact hy1
  rw [RingHom.mem_ker, hpow] at hker
  rw [← hy, hker]

/-- Main statement (Stacks Tag 06RN): a surjective ring endomorphism of a
Noetherian commutative ring is bijective, hence a ring isomorphism. -/
theorem surjective_endomorphism_noetherian_bijective
    (R : Type*) [CommRing R] [IsNoetherianRing R] (φ : R →+* R)
    (hφ : Function.Surjective φ) : Function.Bijective φ :=
  ⟨surjective_endomorphism_noetherian_injective R φ hφ, hφ⟩

/-- The bijective endomorphism above is genuinely a ring isomorphism: there is a
`RingEquiv` `e : R ≃+* R` that agrees with `φ` on every element. -/
@[stacks 06RN]
theorem surjective_endomorphism_noetherian_isomorphism
    (R : Type*) [CommRing R] [IsNoetherianRing R] (φ : R →+* R)
    (hφ : Function.Surjective φ) : ∃ e : R ≃+* R, ∀ x, e x = φ x := by
  refine ⟨RingEquiv.ofBijective φ
    (surjective_endomorphism_noetherian_bijective R φ hφ), ?_⟩
  intro x
  rw [RingEquiv.coe_ofBijective]
