module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupCanDualSituation

/-!
# Maps into `Iⁿ/I^{2n}` become `I^c`-divisible after twisting down on the blowup

Let `A` be a Noetherian ring and `I ⊆ A` an ideal, `p : X → Spec(A)` the blowing up of `Spec(A)`
in `I`, `d = d(S)` the maximal dimension of the fibres of `p` (`fibreDim I`, equal to
`AssociatedGraded.dInvariant I` by `dInvariant_eq_fibreDim`) and `q₀ = q(S)` (`qS I`). For an
`(A, n, c)`-module `M` and an `A`-linear `φ : M → Iⁿ/I^{2n}`, if `n ≥ q₀ + (1 + d)c` and
`n ≥ (2 + d)c`, the composition `M → Iⁿ/I^{2n} → I^{n-(1+d)c}/I^{2n-(1+d)c}` is `∑ aᵢψᵢ` with
`aᵢ ∈ I^c` and `ψᵢ : M → I^{n-(2+d)c}/I^{2n-(2+d)c}`. No hypothesis `n ≥ q₀ + 2c` is imposed
when `d = 0`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.exists_sum_powQuotSmul_blowup_of_eq`: the statement with
  the two levels as parameters `g + c = f`, `f + (1 + d(S))c = n`.
* `Stacks.LocalCohomology.UniformityIII.exists_sum_powQuotSmul_blowup`: the statement under the
  hypotheses `n ≥ q(S) + (1 + d(S))c` and `n ≥ (2 + d(S))c`, with levels `n - (1 + d(S))c` and
  `n - (2 + d(S))c`.

## References

* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
-/

@[expose] public section

universe u

namespace Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- Let `M` be an `(A, n, c)`-module and `φ : M → Iⁿ/I^{2n}` an `A`-linear map. If
`g + c = f`, `f + (1 + d(S))c = n` and `q(S) ≤ f`, then the composition
`M → Iⁿ/I^{2n} → I^f/I^{f+n}` is of the form `∑ aᵢψᵢ` with `aᵢ ∈ I^c` and
`ψᵢ : M → I^g/I^{g+n}`. -/
theorem exists_sum_powQuotSmul_blowup_of_eq {n c : ℕ} (M : ANCModule I n c)
    (φ : resModule I n M.1 →ₗ[A] powQuot I n n) {g f : ℕ}
    (hgf : g + c = f) (hf : f + (1 + fibreDim I) * c = n) (hq : qS I ≤ f) :
    ∃ (N : ℕ) (a : Fin N → A) (ha : ∀ i, a i ∈ I ^ c)
      (ψ : Fin N → (resModule I n M.1 →ₗ[A] powQuot I g n)),
      (powQuotLe I (Nat.le.intro hf)).comp φ =
        ∑ i, (powQuotSmul I (ha i) hgf).comp (ψ i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := subsingleton_powQuot_zero I f
    exact ⟨0, Fin.elim0, fun i => i.elim0, Fin.elim0,
      LinearMap.ext fun _ => Subsingleton.elim _ _⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (blowupCanDualSituationQS I m c (by nlinarith)).exists_sum_powQuotSmul M φ hgf
      (by simpa using hf) (by simpa using hq)

/-- `(2 + d)c = (1 + d)c + c`. -/
theorem two_add_mul_eq (d c : ℕ) : (2 + d) * c = (1 + d) * c + c := by ring

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `q₀ = q(S)` and `d = d(S)` the integers
attached to the blowing up of `Spec(A)` in `I` (`qS I` and `fibreDim I`), `M` an
`(A, n, c)`-module and `φ : M → Iⁿ/I^{2n}` an `A`-linear map. If `n ≥ q₀ + (1 + d)c` and
`n ≥ (2 + d)c`, then the composition `M → Iⁿ/I^{2n} → I^{n-(1+d)c}/I^{2n-(1+d)c}` is of the
form `∑ aᵢψᵢ` with `aᵢ ∈ I^c` and `ψᵢ : M → I^{n-(2+d)c}/I^{2n-(2+d)c}`. No hypothesis
`n ≥ q₀ + 2c` is imposed when `d = 0`. -/
@[stacks 0GAC]
theorem exists_sum_powQuotSmul_blowup {n c : ℕ} (M : ANCModule I n c)
    (φ : resModule I n M.1 →ₗ[A] powQuot I n n)
    (hn₁ : qS I + (1 + fibreDim I) * c ≤ n) (hn₂ : (2 + fibreDim I) * c ≤ n) :
    ∃ (N : ℕ) (a : Fin N → A) (ha : ∀ i, a i ∈ I ^ c)
      (ψ : Fin N → (resModule I n M.1 →ₗ[A] powQuot I (n - (2 + fibreDim I) * c) n)),
      (powQuotLe I (Nat.sub_le n ((1 + fibreDim I) * c))).comp φ =
        ∑ i, (powQuotSmul I (ha i) (show n - (2 + fibreDim I) * c + c =
          n - (1 + fibreDim I) * c by
            have := two_add_mul_eq (fibreDim I) c; omega)).comp (ψ i) :=
  have := two_add_mul_eq (fibreDim I) c
  exists_sum_powQuotSmul_blowup_of_eq I M φ _ (by omega) (by omega)

end Stacks.LocalCohomology.UniformityIII
