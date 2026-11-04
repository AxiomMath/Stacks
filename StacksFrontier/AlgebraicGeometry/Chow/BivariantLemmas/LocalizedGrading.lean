module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# The localized bivariant grading of a closed immersion

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S` and let `p ≥ 0`. The Stacks Project
puts

  `A⁽ᵖ⁾(Z ⟶ X) = ∏_{i ≤ p - 1} Aⁱ(X) × ∏_{i ≥ p} Aⁱ(Z ⟶ X)`,

the graded group that carries the localized Chern class calculus: below the cutoff `p` one
works with operational classes on `X`, and from `p` onward with classes localized along the
closed immersion. Here `Aⁱ(X)` is `Aⁱ(X ⟶ X)`, the bivariant group of the identity.

## Main definitions

* `Stacks.Chow.localizedBivariantGrading` — the group `A⁽ᵖ⁾(Z ⟶ X)`, Stacks 0FA0.

## Implementation notes

The two factors are indexed by the subtypes `{i : ℤ // i < p}` and `{i : ℤ // p ≤ i}` of `ℤ`,
the first of which is the source's `i ≤ p - 1`. Since the definition is an abbreviation, the
abelian group structure on `A⁽ᵖ⁾(Z ⟶ X)` is the product of the pointwise ones coming from
`Stacks.Chow.BivariantClass`, and instance search finds it with no further declaration.

The whole development is stated against a `Stacks.Chow.GysinSystem`, which is the parameter
`Stacks.Chow.BivariantClass` carries; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic` for why.

## References

* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **Stacks 0FA0.** The group `A⁽ᵖ⁾(Z ⟶ X)` attached to a closed immersion `f : Z ⟶ X` of
schemes locally of finite type over the base: operational Chow classes on `X` in the degrees
below `p`, and bivariant classes for `f` in the degrees from `p` onward. -/
@[stacks 0FA0 "localized_bivariant_grading"]
abbrev localizedBivariantGrading (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : Z ⟶ X) [IsClosedImmersion f] (hf : f ≫ sX = sZ) (p : ℕ) : Type (u + 1) :=
  ((i : {i : ℤ // i < (p : ℤ)}) → BivariantClass C G sX sX (𝟙 X) (by simp) i.1) ×
    ((i : {i : ℤ // (p : ℤ) ≤ i}) → BivariantClass C G sZ sX f hf i.1)

end Stacks.Chow

end
