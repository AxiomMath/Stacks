module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.RingTheory.LocalCohomology.CutoffCompletionSerreTransport

/-!
# Serre's condition on the formal fibres, read at an affine open

Let `X` be a scheme, let `V` be an affine open of `X` and let `z ∈ V` correspond to the prime
`q ⊆ Γ(X, V)`. This file identifies Serre's condition `(Sₙ)` on the formal fibres of the local
ring `𝒪_{X,z}` with the same condition on the formal fibres of `Γ(X, V)_q`.

This is the hypothesis term of [Stacks, Tag 0BJY] read at an affine open. The tag imposes the
condition on the formal fibres of `𝒪_{X,z}` for the points `z` outside the open subscheme, while
the affine criteria of this directory impose it at `Localization.AtPrime q` for the primes
`q ⊇ I` of a ring of sections. The two rings are isomorphic and never equal, so the condition
has to be carried across the isomorphism; that transport is
`Stacks.LocalCohomology.formalFibersHavePropertySk_iff_of_ringEquiv`, and all that is added here
is the isomorphism itself.

## Main results

* `AlgebraicGeometry.formalFibersHavePropertySk_stalk_iff_primeIdealOf` — **the identification.**

## Implementation notes

The stalk of the structure sheaf at a point of an affine open is a localization of the ring of
sections at the prime of that point (`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), so
`IsLocalization.algEquiv` supplies the isomorphism with `Localization.AtPrime` of that prime.
The algebra structure on the stalk is not an instance and is introduced with `letI`, as
everywhere else in the library that this isomorphism is built; there is no named declaration for
it.

## References

* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Serre's condition on the formal fibres, read at an affine open.** For `V` an affine open of
a scheme `X` and `z ∈ V` corresponding to the prime `q ⊆ Γ(X, V)`, the formal fibres of
`Γ(X, V)_q` satisfy `(Sₙ)` exactly when those of `𝒪_{X,z}` do.

The stalk is a localization of `Γ(X, V)` at `q`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), so `IsLocalization.algEquiv` identifies
it with `Localization.AtPrime q`, and
`Stacks.LocalCohomology.formalFibersHavePropertySk_iff_of_ringEquiv` carries the condition
across. -/
public theorem formalFibersHavePropertySk_stalk_iff_primeIdealOf {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {z : X} (hz : z ∈ V) (n : ℕ) :
    Stacks.LocalCohomology.FormalFibersHavePropertySk
        (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) n ↔
      Stacks.LocalCohomology.FormalFibersHavePropertySk (X.presheaf.stalk z) n := by
  let : Algebra Γ(X, V) (X.presheaf.stalk z) :=
    X.presheaf.algebra_section_stalk ⟨z, hz⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk z) (hV.primeIdealOf ⟨z, hz⟩).asIdeal :=
    hV.isLocalization_stalk ⟨z, hz⟩
  exact Stacks.LocalCohomology.formalFibersHavePropertySk_iff_of_ringEquiv
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)
      (X.presheaf.stalk z)).toRingEquiv n

end AlgebraicGeometry

end
