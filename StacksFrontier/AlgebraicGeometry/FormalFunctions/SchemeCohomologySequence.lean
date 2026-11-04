module

public import Mathlib.AlgebraicGeometry.Scheme
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologySequence

/-!
# The long exact cohomology sequence on a scheme

Let `X` be a scheme and let `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` be a short exact sequence of abelian sheaves
on the site of opens of `X`. The cohomology groups `H^p(X, ℱ) = H^p(⊤, ℱ)` then sit in a long
exact sequence with connecting homomorphisms `H^p(X, ℱ₃) → H^{p+1}(X, ℱ₁)` in every degree.

This is the specialisation of `StacksFrontier/AlgebraicGeometry/FormalFunctions/CohomologySequence`
to the site of opens of a scheme, taken over the whole scheme. It is recorded separately because
it is the shape in which the sequence is used: positive-degree cohomology of a scheme, with a
degree-raising connecting map, is exactly what the Artin--Rees step of the theorem on formal
functions runs on, applied to `0 → I^n ℱ → ℱ → ℱ/I^n ℱ → 0`.

The groups here are the same ones in which the vanishing theorem
`Stacks.Cohomology.AffineCover.isZero_cohomology_of_degree_ge_separatedCoverBound`
([Stacks, Tag 071L]) is stated, namely `Sheaf.H' ℱ p ⊤` for the site of opens of `X`.

## Main definitions

* `Stacks.Cohomology.Scheme.δ`: the connecting homomorphism
  `H^{p}(X, ℱ₃) → H^{p+1}(X, ℱ₁)` of a short exact sequence of abelian sheaves on `X`.

## Main results

* `Stacks.Cohomology.Scheme.exact_map_map`, `Stacks.Cohomology.Scheme.exact_map_δ` and
  `Stacks.Cohomology.Scheme.exact_δ_map`: the three exactness points of the long exact
  cohomology sequence of `X`.
* `Stacks.Cohomology.Scheme.ker_map_eq_range_map`: `Ker(H^p(X, ℱ₂) → H^p(X, ℱ₃))` is
  `Im(H^p(X, ℱ₁) → H^p(X, ℱ₂))`, the identity opening the Artin--Rees step of the theorem on
  formal functions, [Stacks, Tag 02OB] part (1).

## Implementation notes

The site of opens of a scheme `X : Scheme.{u}` is a small category with morphisms in `Type u`,
so abelian sheaves on it take values in `AddCommGrpCat.{u}` and Mathlib's `Sheaf.H'` applies
with no universe juggling. The `Ext` universe stays a free parameter, as in [Stacks, Tag 071L].

Everything is inherited from the general site statements; no scheme-theoretic input is used, and
in particular `X` is used only through its underlying topological space. The statements are kept
at abelian sheaves rather than at sheaves of `𝒪_X`-modules because the comparison of a short
exact sequence of `𝒪_X`-modules with the underlying sequence of abelian sheaves needs exactness
of `SheafOfModules.toSheaf`, which is a separate matter.

## References

* [Stacks Project, Tag 0159](https://stacks.math.columbia.edu/tag/0159)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace

universe w u

namespace Stacks.Cohomology.Scheme

open Stacks.Cohomology.LongExactSequence

variable {X : AlgebraicGeometry.Scheme.{u}}
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  (hS : S.ShortExact)

/-- The connecting homomorphism `H^{p}(X, ℱ₃) → H^{p+1}(X, ℱ₁)` of a short exact sequence of
abelian sheaves `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` on a scheme `X`.

For the sequence `0 → I^n ℱ → ℱ → ℱ/I^n ℱ → 0` this is the map `δ` of the Artin--Rees step of
the theorem on formal functions, [Stacks, Tag 02OB]. -/
def δ (p : ℕ) : Sheaf.H'.{w} S.X₃ p (⊤ : X.Opens) →+ Sheaf.H'.{w} S.X₁ (p + 1) (⊤ : X.Opens) :=
  LongExactSequence.δ.{w} S hS p (p + 1) rfl ⊤

include hS

/-- **Exactness at `H^p(X, ℱ₂)`.** For a short exact sequence of abelian sheaves
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` on a scheme `X`, the sequence
`H^p(X, ℱ₁) → H^p(X, ℱ₂) → H^p(X, ℱ₃)` is exact. [Stacks, Tag 0159]. -/
theorem exact_map_map (p : ℕ) :
    Function.Exact (map.{w} S.f p (⊤ : X.Opens)) (map.{w} S.g p (⊤ : X.Opens)) :=
  LongExactSequence.exact_map_map S hS p ⊤

/-- **Exactness at `H^p(X, ℱ₃)`.** For a short exact sequence of abelian sheaves
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` on a scheme `X`, the sequence
`H^p(X, ℱ₂) → H^p(X, ℱ₃) → H^{p+1}(X, ℱ₁)` is exact. [Stacks, Tag 0159]. -/
theorem exact_map_δ (p : ℕ) :
    Function.Exact (map.{w} S.g p (⊤ : X.Opens)) (δ.{w} S hS p) :=
  LongExactSequence.exact_map_δ S hS p (p + 1) rfl ⊤

/-- **Exactness at `H^{p+1}(X, ℱ₁)`.** For a short exact sequence of abelian sheaves
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` on a scheme `X`, the sequence
`H^p(X, ℱ₃) → H^{p+1}(X, ℱ₁) → H^{p+1}(X, ℱ₂)` is exact. [Stacks, Tag 0159]. -/
theorem exact_δ_map (p : ℕ) :
    Function.Exact (δ.{w} S hS p) (map.{w} S.f (p + 1) (⊤ : X.Opens)) :=
  LongExactSequence.exact_δ_map S hS p (p + 1) rfl ⊤

/-- **The kernel-image identity on a scheme.** For a short exact sequence of abelian sheaves
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` on a scheme `X`,
`Ker(H^p(X, ℱ₂) → H^p(X, ℱ₃)) = Im(H^p(X, ℱ₁) → H^p(X, ℱ₂))`.

Applied to `0 → I^n ℱ → ℱ → ℱ/I^n ℱ → 0` this is the identification
`Ker(H^p(X, ℱ) → H^p(X, ℱ/I^n ℱ)) = Im(H^p(X, I^n ℱ) → H^p(X, ℱ))` with which the Artin--Rees
step of the theorem on formal functions begins, [Stacks, Tag 02OB] part (1). -/
theorem ker_map_eq_range_map (p : ℕ) :
    (map.{w} S.g p (⊤ : X.Opens)).ker = (map.{w} S.f p (⊤ : X.Opens)).range :=
  LongExactSequence.ker_map_eq_range_map S hS p ⊤

end Stacks.Cohomology.Scheme

end
