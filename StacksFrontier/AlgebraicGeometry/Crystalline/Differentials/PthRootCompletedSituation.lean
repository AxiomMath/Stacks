module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootCompletedTheorem
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetractEquivalence

/-!
# Tag 07N1 in Situation 07MD

This module states [Stacks, Lemma 60.25.3, Tag 07N1] in its own setting: Situation 07MD, with `D`
the `p`-adically completed divided power envelope (07J8) of the kernel of a polynomial
presentation `P = A[x_i] → C`, with its divided powers `γ̄` of [Stacks, Tag 07KG], and `Ω_D` the
`p`-adic completion of its divided power differentials (07J9).  It is the specialisation of
`Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension`, which proves the
lemma for every divided power ring in which `p` is nilpotent modulo the divided power ideal.

## Main results

* `Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension_situation` —
  **[Stacks, Lemma 60.25.3, Tag 07N1].**

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

universe u v

namespace Crystalline

namespace PthRootExtension

open CompletedLevels

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type u}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)

/-- In Situation 07MD the prime `p` is nilpotent modulo the divided power ideal `J̄` of the
completed divided power envelope `D` of (07J8). -/
theorem completedEnvelopeOfPresentation_prime_nilpotent :
    IsNilpotent (Ideal.Quotient.mk (completedEnvelopeOfPresentation s f hf).ideal
      (s.p : (completedEnvelopeOfPresentation s f hf : Type u))) :=
  completionIdeal_prime_nilpotent _ s.p (presentationEnvelope_prime_nilpotent s f hf)

/-- The completed divided power envelope `D` of (07J8). -/
local notation "𝒟" => completedEnvelopeOfPresentation s f hf

/-- **[Stacks, Lemma 60.25.3, Tag 07N1].**

In Situation 07MD (`s`), let `P = A[x_i] → C` be a surjective polynomial presentation (`f`, `hf`),
let `D` be the `p`-adic completion of the divided power envelope `D_{P,γ}(ker f)` with its divided
powers `γ̄` (07J8, [Stacks, Tag 07KG]), and let `Ω^q_D` be the `p`-adic completion of the divided
power forms of `D` over `A` (07J9, in its second form `Ω_D = lim_e Ω_{D/A,γ̄}/p^e`).  Let `λ ∈ D`,
let `D'` be the `p`-adic completion of `D[z]⟨ξ⟩/(ξ - (z^p - λ))` with the divided powers of
[Stacks, Tag 07KD], and let `Ω^q_{D'}` be the `p`-adic completion of the divided power forms of
`D'` over `A`.  Let `M` be a `D`-module with a connection `∇ : M → M ⊗̂_D Ω_D` (07JC), integrable
(07JD) in the sense of [Stacks, Remark 60.6.1, Tag 07I0]: the composite `M → M ⊗̂ Ω¹ → M ⊗̂ Ω²`
vanishes.  Then:

* `M ⊗^∧_D Ω^•_D` and `M ⊗^∧_D Ω^•_{D'}` are complexes;
* the canonical map `c_M^• : M ⊗^∧_D Ω^•_D → M ⊗^∧_D Ω^•_{D'}` of (07PY) is a map of complexes;
* there is a map of complexes `e_M^•` in the opposite direction with `e_M^• ∘ c_M^• = p`, so that
  `e_M^• ∘ c_M^•` is homotopic to `p` (by the zero homotopy), and a homotopy `h` with
  `h d = p - c_M^• ∘ e_M^•` in degree `0` and `d h + h d = p - c_M^• ∘ e_M^•` in positive degrees,
  so that `c_M^• ∘ e_M^•` is homotopic to `p`; moreover `h ∘ c_M^• = 0`.

The hypotheses (07JB), completeness of `M`, and (07JE), quasi-nilpotence of `∇`, are not needed
and are not assumed. -/
@[stacks 07N1 "in Situation 07MD with D the completed divided power envelope of 07J8 and the \
completed forms of 07J9; for every completed connection integrable in the sense of 07I0"]
theorem exists_homotopyInverse_completedPthRootExtension_situation
    (lam : (𝒟 : Type u)) (M : Type u) [AddCommGroup M] [Module (𝒟 : Type u) M]
    (nabla : CompletedConnection s.p (𝒟 : Type u)
      (completedDividedPowerForms s.p (s.A : Type u) (𝒟).dividedPowers 1)
      (completedDividedPowerDifferentialOnRing s.p (s.A : Type u) (𝒟).dividedPowers) M)
    (hint : IsCompletedIntegrable s.p (s.A : Type u) (𝒟 : Type u) (𝒟).dividedPowers M nabla) :
    CompletedDeRham.IsSquareZero s.p (𝒟 : Type u) (completedDividedPowerForms s.p (s.A : Type u)
        (𝒟).dividedPowers)
        (completedDividedPowerWedgeOnRing s.p (s.A : Type u) (𝒟).dividedPowers)
        (completedDividedPowerDeRham s.p (s.A : Type u) (𝒟).dividedPowers) M nabla
        (isGradedLeibniz_completedDividedPowerOnRing s.p (s.A : Type u) (𝒟).dividedPowers) ∧
      CompletedDeRham.IsSquareZero s.p (completedPrimeRingSelf 𝒟 s.p lam)
        (completedDividedPowerForms s.p (s.A : Type u)
          (completedPrimeDividedPowers 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
              (completedEnvelopeOfPresentation_prime_nilpotent s f hf)))
        (completedDividedPowerWedgeOnRing s.p (s.A : Type u)
          (completedPrimeDividedPowers 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
              (completedEnvelopeOfPresentation_prime_nilpotent s f hf)))
        (completedDividedPowerDeRham s.p (s.A : Type u)
          (completedPrimeDividedPowers 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
              (completedEnvelopeOfPresentation_prime_nilpotent s f hf)))
        (genuineCarrier 𝒟 s.p lam M)
        (genuineCompletedConnection (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
            (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M nabla)
        (isGradedLeibniz_completedDividedPowerOnRing s.p (s.A : Type u) _) ∧
      (∀ q : ℕ, (genuineCompletedDifferential (s.A : Type u) 𝒟 s.p lam (Fact.out :
          s.p.Prime).ne_zero
          (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M nabla
          q).comp (genuineCompletedComparison (s.A : Type u) 𝒟 s.p lam (Fact.out :
              s.p.Prime).ne_zero
              (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M q) =
        (genuineCompletedComparison (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
            (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M (q + 1)).comp
          (baseCompletedDifferential (s.A : Type u) 𝒟 s.p M nabla q)) ∧
      ∃ (e : ∀ q : ℕ, genuineCompletedTerm (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
          (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M q →+
          baseCompletedTerm (s.A : Type u) 𝒟 s.p M q)
        (h : ∀ q : ℕ, genuineCompletedTerm (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
            (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M (q + 1) →+
          genuineCompletedTerm (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
              (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M q),
        (∀ (q : ℕ) (y : genuineCompletedTerm (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
            (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M q),
          e (q + 1) (genuineCompletedDifferential (s.A : Type u) 𝒟 s.p lam (Fact.out :
              s.p.Prime).ne_zero
              (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M
            nabla q y) = baseCompletedDifferential (s.A : Type u) 𝒟 s.p M nabla q (e q y)) ∧
        (∀ (q : ℕ) (x : baseCompletedTerm (s.A : Type u) 𝒟 s.p M q),
          e q (genuineCompletedComparison (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
              (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M q x) =
            s.p • x) ∧
        (∀ y : genuineCompletedTerm (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
            (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M 0,
          h 0 (genuineCompletedDifferential (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
              (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M nabla 0
            y) = s.p • y - genuineCompletedComparison (s.A : Type u) 𝒟 s.p lam (Fact.out :
                s.p.Prime).ne_zero
                (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M 0
              (e 0 y)) ∧
        (∀ (q : ℕ) (y : genuineCompletedTerm (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
            (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M
            (q + 1)),
          genuineCompletedDifferential (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
              (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M nabla q
              (h q y) +
            h (q + 1) (genuineCompletedDifferential (s.A : Type u) 𝒟 s.p lam (Fact.out :
                s.p.Prime).ne_zero
                (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M
              nabla (q + 1) y) =
            s.p • y - genuineCompletedComparison (s.A : Type u) 𝒟 s.p lam (Fact.out :
                s.p.Prime).ne_zero
                (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M
              (q + 1) (e (q + 1) y)) ∧
        (∀ (q : ℕ) (x : baseCompletedTerm (s.A : Type u) 𝒟 s.p M (q + 1)),
          h q (genuineCompletedComparison (s.A : Type u) 𝒟 s.p lam (Fact.out : s.p.Prime).ne_zero
              (completedEnvelopeOfPresentation_prime_nilpotent s f hf) M (q + 1)
            x) = 0) :=
  exists_homotopyInverse_completedPthRootExtension (s.A : Type u) s.p 𝒟
    (completedEnvelopeOfPresentation_prime_nilpotent s f hf) lam M nabla hint

end PthRootExtension

end Crystalline
