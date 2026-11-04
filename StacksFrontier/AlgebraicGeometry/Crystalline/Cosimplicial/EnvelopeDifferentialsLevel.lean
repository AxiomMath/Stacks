module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevel
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedDifferentials

/-!
# The two shapes of `Ω_{D(n)}`, at a finite `p`-adic level

The degree `n` of the cosimplicial module `Ω_{D(*)}` of [Stacks, Tag 07L1] is
`Crystalline.completedTensorPowerDifferentials`: the `p`-adic completion of the divided power
differentials of the *uncompleted* envelope `E(n)` of the kernel of
`P ⊗_A ⋯ ⊗_A P → C`, carrying a divided power derivation out of `D(n)`.  The second equality of
the source's proof of [Stacks, Tag 07LF] — `Crystalline.tensorFormsLevelEquiv` — speaks instead of
`Crystalline.dividedPowerDifferentials` of `D(n)`'s *own* divided powers, the universal object.

The two are not isomorphic, the universal one not being `p`-adically complete.
`Crystalline.completedDifferentialsLevelLinearEquiv` of `ModuleDifferentials/CompletionLevel.lean`
identifies them modulo `pᵏ` for every `k` past the cutoff of a comparison of [Stacks, Tag 07KK],
linearly over the completion and with the tensor products left *uncompleted*.  This module reads
that at `E(n)`, which is where the source needs it: the comparison of [Stacks, Tag 07KK] exists
there because `p` is nilpotent modulo the divided power ideal of a polynomial divided power
envelope, by `Crystalline.polynomialDividedPowerEnvelope_prime_nilpotent`.

## Main definitions

* `Crystalline.tensorPowerEnvelopeCompletionComparison` — **[Stacks, Tag 07KK] read at the
  envelope `E(n)`**, which is what gives the cutoff past which the levels of `Ω_{D(n)}` are
  comparable at all.
* `Crystalline.tensorPowerDifferentialsLevelLinearEquiv` — **the two shapes of `Ω_{D(n)}` agree
  modulo `pᵏ`**, over `D(n)`, for every `k` past that cutoff.

## Main results

* `Crystalline.completionDifferentialsModPow_tensorPowerEnvelope` — the target of the general
  identification, read at `E(n)`, is `Crystalline.completedTensorPowerDifferentials` modulo `pᵏ`;
  this holds by `rfl` and is what makes the identification one about `Ω_{D(n)}`.

## Implementation notes

The `s.A`-algebra structure on the envelope `E(n)` is its structure map, which the chapter carries
as a `letI` rather than as an instance — a global instance would compete with the one the
completion `D(n)` already has.  Every statement here therefore opens with that `letI`, and
`tensorPowerDifferentialsLevelLinearEquiv` bundles the comparison of [Stacks, Tag 07KK] together
with the family of identifications it produces, in one `Σ'` under a single `letI`: the cutoff is a
field of the comparison, so a separate declaration for the identifications could not name it.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07L1](https://stacks.math.columbia.edu/tag/07L1)
* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

universe u v w

namespace Crystalline

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)

/-- **[Stacks, Tag 07KK] read at the envelope `E(n)`.**  The prime is nilpotent modulo the divided
power ideal of a polynomial divided power envelope, so the comparison of the three inverse limits
of divided power differentials exists at `E(n)`; its cutoff is the level past which the quotients
`E(n)/pᵏ` carry divided powers, and hence past which the two shapes of `Ω_{D(n)}` can be
compared. -/
public noncomputable def tensorPowerEnvelopeCompletionComparison (n : ℕ) :
    letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    DifferentialsCompletionComparison (A := (s.A : Type u))
      (tensorPowerEnvelope s f n).object.ideal
      (tensorPowerEnvelope s f n).object.dividedPowers s.p
      (polynomialDividedPowerEnvelope_prime_nilpotent s (tensorPowerPresentation s f n)) := by
  letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  exact dividedPowerDifferentialsCompletionComparison (A := (s.A : Type u))
    (B := (tensorPowerEnvelope s f n).object)
    (J := (tensorPowerEnvelope s f n).object.ideal)
    (delta := (tensorPowerEnvelope s f n).object.dividedPowers) (p := s.p)
    (polynomialDividedPowerEnvelope_prime_nilpotent s (tensorPowerPresentation s f n))

/-- **The target of the general level identification, read at `E(n)`, is `Ω_{D(n)}` modulo
`pᵏ`.**  `Crystalline.completionDifferentialsModPow` of the envelope's divided powers is
`Crystalline.completedTensorPowerDifferentials` modulo `pᵏ` — the degree `n` of the cosimplicial
module `Ω_{D(*)}` modulo `pᵏ` — on the nose. -/
public theorem completionDifferentialsModPow_tensorPowerEnvelope (n k : ℕ) :
    letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    completionDifferentialsModPow (A := (s.A : Type u))
        (tensorPowerEnvelope s f n).object.ideal
        (tensorPowerEnvelope s f n).object.dividedPowers s.p k =
      (completedTensorPowerDifferentials s f n ⧸
        (DividedPowers.pAdicIdeal
              (A := pAdicCompletedTensorPowerEnvelope s f hf n) s.p ^ k •
          (⊤ : Submodule (pAdicCompletedTensorPowerEnvelope s f hf n)
            (completedTensorPowerDifferentials s f n)))) :=
  rfl

/-- **The two shapes of `Ω_{D(n)}` agree modulo `pᵏ`.**  Bundled with the comparison of
[Stacks, Tag 07KK] at `E(n)` whose cutoff fixes the range of `k`: for every `e`, the universal
divided power differentials of `D(n)` and the `p`-adic completion of the differentials of `E(n)`
— the degree `n` of `Ω_{D(*)}` — have the same reduction modulo `p^{cutoff + e}`, `D(n)`-linearly.

Both quotients are the *uncompleted* ones, so the identification survives tensoring with a module
killed by `p^{cutoff + e}`; that is what the level-`e` step of the source's proof of
[Stacks, Tag 07LF] applies `Crystalline.tensorFormsLevelEquiv` through, and it is what the
`p`-adically completed comparison of `Crystalline.dividedPowerDifferentialsCompletionComparison`
alone does not give. -/
public noncomputable def tensorPowerDifferentialsLevelLinearEquiv (n : ℕ) :
    letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    Σ' cmp : DifferentialsCompletionComparison (A := (s.A : Type u))
        (tensorPowerEnvelope s f n).object.ideal
        (tensorPowerEnvelope s f n).object.dividedPowers s.p
        (polynomialDividedPowerEnvelope_prime_nilpotent s (tensorPowerPresentation s f n)),
      ∀ e : ℕ,
        completedDifferentialsModPow (A := (s.A : Type u))
            (tensorPowerEnvelope s f n).object.ideal
            (tensorPowerEnvelope s f n).object.dividedPowers s.p
            (polynomialDividedPowerEnvelope_prime_nilpotent s
              (tensorPowerPresentation s f n))
            (cmp.quotientSystem.cutoff + e) ≃ₗ[
              pAdicCompletedTensorPowerEnvelope s f hf n]
          (completedTensorPowerDifferentials s f n ⧸
            (DividedPowers.pAdicIdeal
                  (A := pAdicCompletedTensorPowerEnvelope s f hf n) s.p ^
                  (cmp.quotientSystem.cutoff + e) •
              (⊤ : Submodule (pAdicCompletedTensorPowerEnvelope s f hf n)
                (completedTensorPowerDifferentials s f n)))) := by
  letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  refine ⟨tensorPowerEnvelopeCompletionComparison s f n, fun e ↦ ?_⟩
  exact completedDifferentialsLevelLinearEquiv (A := (s.A : Type u))
    (tensorPowerEnvelope s f n).object.ideal
    (tensorPowerEnvelope s f n).object.dividedPowers s.p
    (polynomialDividedPowerEnvelope_prime_nilpotent s (tensorPowerPresentation s f n))
    (tensorPowerEnvelopeCompletionComparison s f n) e

end Crystalline

end
