module

public import Mathlib.RingTheory.Henselian
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian

/-!
# Henselian and strictly henselian local rings

Let `(R, 𝔪, κ)` be a local ring. Stacks defines `R` to be henselian if for every monic
`f ∈ R[T]` and every root `a₀ ∈ κ` of `f̄` with `f̄'(a₀) ≠ 0` there is `a ∈ R` with `f(a) = 0`
and `ā = a₀`, and strictly henselian if moreover `κ` is separably algebraically closed.

## Main results

* `henselianLocalRing_iff_exists_root_of_residue_root`: Mathlib's `HenselianLocalRing R` is
  equivalent to the Stacks lifting condition for simple roots in the residue field.
* `strictlyHenselianLocalRing_iff`: `StrictlyHenselianLocalRing R` is equivalent to
  `R` being henselian with separably closed residue field.
* `henselianLocalRing_iff_and_strictlyHenselianLocalRing_iff`: both parts of the definition.

## Implementation notes

Mathlib's `HenselianLocalRing` asks for a lift of any `a₀ ∈ R` with `f(a₀) ∈ 𝔪` and `f'(a₀)` a
unit; the Stacks wording is recovered from `HenselianLocalRing.TFAE`.

## References

* [Stacks Project, Tag 04GF](https://stacks.math.columbia.edu/tag/04GF)
-/

@[expose] public section

open Polynomial IsLocalRing

/-- A local ring `R` is a `HenselianLocalRing` if and only if for every monic `f ∈ R[T]` and
every `a₀` in the residue field with `f̄(a₀) = 0` and `f̄'(a₀) ≠ 0` there is `a ∈ R` with
`f(a) = 0` and `ā = a₀`. -/
theorem henselianLocalRing_iff_exists_root_of_residue_root (R : Type*) [CommRing R]
    [IsLocalRing R] :
    HenselianLocalRing R ↔ ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R,
      (f.map (residue R)).eval a₀ = 0 → ((derivative f).map (residue R)).eval a₀ ≠ 0 →
        ∃ a : R, f.eval a = 0 ∧ residue R a = a₀ := by
  refine ((HenselianLocalRing.TFAE R).out 1 2).trans ?_
  simp only [aeval_def, ResidueField.algebraMap_eq, eval_map, IsRoot.def]

/-- A local ring is a `StrictlyHenselianLocalRing` if and only if it is henselian and its residue
field is separably closed. -/
theorem strictlyHenselianLocalRing_iff (R : Type*) [CommRing R] [IsLocalRing R] :
    StrictlyHenselianLocalRing R ↔
      HenselianLocalRing R ∧ IsSepClosed (ResidueField R) :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨h₁, h₂⟩ => { h₁, h₂ with }⟩

/-- Let `(R, 𝔪, κ)` be a local ring. Then
1. `R` is henselian if and only if for every monic `f ∈ R[T]` and every root `a₀ ∈ κ` of `f̄`
   with `f̄'(a₀) ≠ 0` there is `a ∈ R` with `f(a) = 0` and `ā = a₀`;
2. `R` is strictly henselian if and only if `R` is henselian and `κ` is separably
   algebraically closed. -/
@[stacks 04GF "both parts: Mathlib's `HenselianLocalRing` and the library's
  `StrictlyHenselianLocalRing` are each shown equivalent to the Stacks wording"]
theorem henselianLocalRing_iff_and_strictlyHenselianLocalRing_iff (R : Type*) [CommRing R]
    [IsLocalRing R] :
    (HenselianLocalRing R ↔ ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R,
      (f.map (residue R)).eval a₀ = 0 → ((derivative f).map (residue R)).eval a₀ ≠ 0 →
        ∃ a : R, f.eval a = 0 ∧ residue R a = a₀) ∧
    (StrictlyHenselianLocalRing R ↔
      HenselianLocalRing R ∧ IsSepClosed (ResidueField R)) :=
  ⟨henselianLocalRing_iff_exists_root_of_residue_root R, strictlyHenselianLocalRing_iff R⟩
