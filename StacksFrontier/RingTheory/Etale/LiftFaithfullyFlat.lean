module

public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.RingTheory.Smooth.LiftDifferenceBaseChange

/-!
# Lifting a faithfully flat étale algebra along a nilpotent thickening

Let `A' → A` be a surjection of commutative rings with square-zero kernel `I` and let `B` be an
étale, faithfully flat `A`-algebra. By Stacks 04D1 (`Stacks.etale_lift_along_surjection`) there
is an étale `A'`-algebra `B'` with a surjection `ψ : B' → B` whose kernel is `I B'`. This file
records that `B'` is then faithfully flat over `A'` and that `ψ` identifies `A ⊗_{A'} B'` with
`B` (`Stacks.exists_etale_faithfullyFlat_lift`).

## Main results

* `Stacks.exists_etale_faithfullyFlat_lift`.

## References

* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
-/

@[expose] public noncomputable section

open TensorProduct Stacks.LocalThickening Stacks.SquareZeroLift

universe u

namespace Stacks

variable {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B] [Algebra A' A] [Algebra A B]
  [Algebra A' B] [IsScalarTower A' A B]

/-- **A faithfully flat étale algebra over a square-zero quotient lifts.** For `A' → A`
surjective with square-zero kernel and `B` étale and faithfully flat over `A`, there is an étale,
faithfully flat `A'`-algebra `B'` together with an isomorphism of `A'`-algebras
`A ⊗_{A'} B' ≅ B` which is `A`-linear. -/
theorem exists_etale_faithfullyFlat_lift (hA : Function.Surjective (algebraMap A' A))
    (hI : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) [Algebra.Etale A B] [Module.FaithfullyFlat A B] :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra A' B'), Algebra.Etale A' B' ∧
      Module.FaithfullyFlat A' B' ∧ ∃ e : A ⊗[A'] B' ≃ₐ[A'] B,
        ∀ a : A, e (a ⊗ₜ 1) = algebraMap A B a := by
  obtain ⟨B', _, _, hB', ψ, hψ, hker⟩ := etale_lift_along_surjection A' A B hA
  refine ⟨B', inferInstance, inferInstance, hB', ?_, ?_⟩
  · -- faithful flatness: every prime of `A'` contains `I` and lifts through `A` and `B`
    have : Module.Flat A' B' := inferInstance
    refine Module.FaithfullyFlat.of_comap_surjective fun P => ?_
    have hIP : RingHom.ker (algebraMap A' A) ≤ P.asIdeal := by
      intro x hx
      have h2 : x ^ 2 = 0 := by
        have hmem : x ^ 2 ∈ RingHom.ker (algebraMap A' A) ^ 2 := Ideal.pow_mem_pow hx 2
        rwa [hI, Ideal.mem_bot] at hmem
      exact P.2.mem_of_pow_mem 2 (h2 ▸ P.asIdeal.zero_mem)
    let P₀ : Ideal A := P.asIdeal.map (algebraMap A' A)
    have hP₀ : P₀.IsPrime := Ideal.map_isPrime_of_surjective hA hIP
    have hcomapP₀ : P₀.comap (algebraMap A' A) = P.asIdeal := by
      rw [Ideal.comap_map_of_surjective _ hA, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hIP]
    obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B)
      ⟨P₀, hP₀⟩
    refine ⟨PrimeSpectrum.comap (ψ : B' →+* B) Q, PrimeSpectrum.ext ?_⟩
    show Ideal.comap (algebraMap A' B') (Ideal.comap (ψ : B' →+* B) Q.asIdeal) = P.asIdeal
    rw [Ideal.comap_comap, show (ψ : B' →+* B).comp (algebraMap A' B') = algebraMap A' B from
      ψ.comp_algebraMap, IsScalarTower.algebraMap_eq A' A B, ← Ideal.comap_comap]
    have hQ' : Q.asIdeal.comap (algebraMap A B) = P₀ := congrArg PrimeSpectrum.asIdeal hQ
    rw [hQ', hcomapP₀]
  · -- the comparison `A ⊗_{A'} B' → B`
    let Φ : A ⊗[A'] B' →ₐ[A'] B :=
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A' A B) ψ fun _ _ => mul_comm _ _
    have hΦ : ∀ (a : A) (b : B'), Φ (a ⊗ₜ b) = algebraMap A B a * ψ b := fun a b =>
      Algebra.TensorProduct.lift_tmul _ _ _ _ _
    have hΦr : Φ.comp (redπ A' A B') = ψ := AlgHom.ext fun b => by
      show Φ ((1 : A) ⊗ₜ b) = ψ b
      rw [hΦ, map_one, one_mul]
    have hbij : Function.Bijective Φ := by
      refine ⟨fun t t' h => ?_, fun b => ?_⟩
      · obtain ⟨b₁, rfl⟩ := redπ_surjective hA B' t
        obtain ⟨b₂, rfl⟩ := redπ_surjective hA B' t'
        rw [← sub_eq_zero, ← map_sub]
        rw [← sub_eq_zero, ← map_sub, ← map_sub, ← AlgHom.comp_apply, hΦr] at h
        refine (redπ_eq_zero_iff hA _).2 ?_
        have hk : b₁ - b₂ ∈ RingHom.ker (ψ : B' →+* B) := h
        rw [hker] at hk
        exact hk
      · obtain ⟨b', rfl⟩ := hψ b
        exact ⟨redπ A' A B' b', by rw [← AlgHom.comp_apply, hΦr]⟩
    refine ⟨AlgEquiv.ofBijective Φ hbij, fun a => ?_⟩
    show Φ (a ⊗ₜ 1) = _
    rw [hΦ, map_one, mul_one]

end Stacks

end
