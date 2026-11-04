module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.RelativeSpecProper

/-!
# The uniform twist vanishing with the twist ranging over the integers

Part (2) of [Stacks, Tag 0897] is stated in this development with the twist a natural number:
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedModule` and its
corollaries conclude

`∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p → ∀ n : ℕ, Hᵖ(Z, Mₙ ⊗ ℒ ^⊗ d) = 0`.

The consumers in [Stacks, Tag 0D2M] ask for the same statement with `d₀` and `d` **integers**,
because the twist `ℒ ^⊗ d` of an invertible module is defined for every integer ([Stacks, Tag
01CU], `AlgebraicGeometry.tensorPowModule`) and the adic dévissage there twists by an arbitrary
integer.

The two are the same statement, and this file says so. There is no mathematics in it: for
`d₀ := (dₑ : ℤ)` any integer `d` with `d₀ ≤ d` is nonnegative, hence is the image of
`d.toNat`, and the natural-number statement applies at `d.toNat`. It is recorded as its own
declaration, separate from the engine, so that no consumer has to repeat the conversion and no
bridging lemma between two spellings of the twist is ever introduced.

## Main results

* `Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_int_of_nat`: **the
  natural-number form implies the integer form.** The homogeneous pieces enter only as a family
  `ℕ → Z.Modules`, so this applies to the conclusion of any of the capstones with
  `Mp n := M.piece (n : ℤ)` without repeating their hypotheses.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.RelativeVeryAmple Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.FiniteTypeDominating

universe u

namespace Stacks.GradedProperCohomology

/-- **The uniform twist vanishing, with the twist an arbitrary integer.**

Given the vanishing of `Hᵖ(Z, Mₙ ⊗ ℒ ^⊗ d)` for one natural number `d₀`, all natural `d ≥ d₀`,
all `p > 0` and all `n` — the conclusion of part (2) of [Stacks, Tag 0897] in the form the
capstones of this development state it — the same vanishing holds for one *integer* `d₀` and all
*integers* `d ≥ d₀`.

A restatement and nothing else: `d₀ := (dₑ : ℤ)` forces `0 ≤ d`, so `d = (d.toNat : ℤ)` and the
hypothesis applies at `d.toNat`. The family of modules is arbitrary, so this consumes the
conclusion of any of the capstones with `Mp n := M.piece (n : ℤ)` and repeats none of their
hypotheses. -/
theorem exists_isZero_Hgroup_tensorPowTwist_int_of_nat {Z : Scheme.{u}} (L : Z.Modules)
    [IsInvertibleModule Z L] (Mp : ℕ → Z.Modules)
    (h : ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p → ∀ n : ℕ,
      IsZero (Hgroup Z.ringCatSheaf ⊤ p
        (tensorModules Z (Mp n) (tensorPowModule Z L (d : ℤ))))) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℕ,
      IsZero (Hgroup Z.ringCatSheaf ⊤ p
        (tensorModules Z (Mp n) (tensorPowModule Z L d))) := by
  obtain ⟨dₑ, hdₑ⟩ := h
  refine ⟨(dₑ : ℤ), fun d hd p hp n => ?_⟩
  have hcast : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg dₑ) hd)
  have hle : dₑ ≤ d.toNat := by omega
  have hvan := hdₑ d.toNat p hle hp n
  rwa [hcast] at hvan

end Stacks.GradedProperCohomology

end
