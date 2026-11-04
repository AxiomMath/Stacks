module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementFormalFunctions

/-!
# A witness for the hypotheses of Stacks 0EII, and the controls around it

`StacksFrontier/AlgebraicGeometry/FormalGeometry/ComplementFormalFunctions.lean` proves
that the canonical map from the sections of `M̃` on `U = Spec A ∖ V(I)` to the inverse limit of the
sections of the `(M/fⁿM)̃` is an isomorphism, under five hypotheses: `A` Noetherian, `f ∈ I`, `M`
finite, `A` is `f`-adically complete, and the first two local cohomology modules of `M` are
annihilated by powers of `f`. This file exhibits an instance where all five hold, so that none of
them is unsatisfiable, together with the controls that locate the degenerate cases.

The witness is `A = ℤ[X]`, `I = (X)`, `f = 0`, `M = A`. Completeness is the `⊥`-adic case, and the
two annihilation hypotheses hold with the exponent `1` because `0 • x = 0`. The open `U` is not
empty — the generic point lies in it — and the first term of the quotient tower, `A ⧸ 0`, is not
the zero module, so the conclusion is not a statement about the empty open or about zero modules.

**The degenerate cases, recorded.** At `I = ⊥` the open `U` is empty and every term of the
comparison is zero, so nothing there is refutable. At a nilpotent `f` — in particular at `f = 0`,
as here — the two annihilation hypotheses hold for *every* `I` and `M`, so this witness certifies
that the hypothesis set is satisfiable but does not exercise the local cohomology hypotheses
non-trivially; what it does exercise is the completeness hypothesis and the non-emptiness of `U`.
Exhibiting an instance with `H¹_I(M) ≠ 0` annihilated by a genuine power of `f` needs a
computation of local cohomology that this library does not have.

## Main results

* `Stacks.Examples.complementFormalFunctions_witness` — all five hypotheses of Stacks 0EII hold at
  `A = ℤ[X]`, `I = (X)`, `f = 0`, `M = A`.
* `Stacks.Examples.control_hkill_needed`, `Stacks.Examples.control_gap_needed`,
  `Stacks.Examples.control_smul_ne_id` — three predicted-failure controls.

## References

* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Stacks.LocalCohomology Stacks.Algebraization.ComplementTower

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Examples

/-- **All five hypotheses of Stacks 0EII are satisfiable.** At `A = ℤ[X]`, `I = (X)`, `f = 0` and
`M = A` the ring is Noetherian, `f ∈ I`, `M` is finite, `A` is `0`-adically complete because the
zero ideal is `⊥`, and both annihilation hypotheses hold with exponent `1`. -/
theorem complementFormalFunctions_witness :
    IsIso (ModuleCat.ofHom (sectionsToLimit (Polynomial ℤ) (Ideal.span {Polynomial.X}) 0
      (ModuleCat.of (Polynomial ℤ) (Polynomial ℤ)))) := by
  have hc : IsAdicComplete (Ideal.span {(0 : Polynomial ℤ)}) (Polynomial ℤ) := by
    rw [Ideal.span_singleton_eq_bot.mpr rfl]; infer_instance
  refine sectionsToLimit_isIso (Polynomial ℤ) (Ideal.span {Polynomial.X}) 0
    (Submodule.zero_mem _) (ModuleCat.of (Polynomial ℤ) (Polynomial ℤ)) hc
    ⟨1, fun x ↦ ?_⟩ ⟨1, fun x ↦ ?_⟩ <;> rw [pow_one, zero_smul]

/-- The open `U = Spec ℤ[X] ∖ V(X)` of the witness is not empty: the generic point lies in it,
because `X ≠ 0`. -/
theorem nonempty_openComplement_witness :
    (⟨⊥, inferInstance⟩ : PrimeSpectrum (Polynomial ℤ)) ∈
      (openComplement (Polynomial ℤ) (Ideal.span {Polynomial.X})).1 := by
  intro hmem
  exact Polynomial.X_ne_zero
    (Submodule.mem_bot _ |>.1 (hmem (Ideal.mem_span_singleton_self Polynomial.X)))

/-- The modules whose sections the comparison relates are not zero at the witness: the first term
of the quotient tower is `ℤ[X] ⧸ 0`. -/
theorem nontrivial_quotientModule_witness :
    Nontrivial
      (quotientModule (Polynomial ℤ) 0 (ModuleCat.of (Polynomial ℤ) (Polynomial ℤ)) 1) :=
  have h : ((Ideal.span {(0 : Polynomial ℤ)}) ^ 1 •
      (⊤ : Submodule (Polynomial ℤ) (Polynomial ℤ))) = ⊥ := by
    rw [Ideal.span_singleton_eq_bot.mpr rfl, pow_one, Submodule.bot_smul]
  (Submodule.quotEquivOfEqBot _ h).toEquiv.nontrivial

/-- **Control 1: the annihilation hypothesis of
`Stacks.LocalCohomology.powerTorsionSESMap` is load-bearing.** At `A = ℤ`, `M = ℤ/4`, `f = 2`,
`m = 2` and `p = 1` the torsion `M[f²]` is all of `M`, and `f ^ (m - p) = 2` does not kill it, so
the morphism of torsion sequences with zero first component does not exist there. -/
theorem control_hkill_needed :
    ¬ (∀ x : ZMod 4, (2 : ℤ) ^ 2 • x = 0 → (2 : ℤ) ^ (2 - 1) • x = 0) := by decide

/-- **Control 2: the stabilization gap in
`Stacks.LocalCohomology.pow_smul_eq_zero_of_powerTorsion_stable` is load-bearing.** At `A = ℤ`,
`M = ℤ/4`, `f = 2` the `fⁿ`-torsion stabilizes only from `N = 2` on, and the conclusion fails for
a gap `m - p = 1 < N`. -/
theorem control_gap_needed : ¬ (∀ x : ZMod 4, (2 : ℤ) ^ 1 • x = 0) := by decide

/-- **Control 3: multiplication by a scalar is not the identity**, so the linearity statements
about the cohomology of derived sections are not trivially true. -/
theorem control_smul_ne_id : (2 : ℤ) • (1 : ZMod 4) ≠ (1 : ZMod 4) := by decide

end Stacks.Examples

end
