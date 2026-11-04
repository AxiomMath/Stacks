module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDPuncturedRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# Injectivity of `H¹(X, 𝒪_X) ⟶ H¹(f⁻¹(U), 𝒪_X)`, as a Stacks tag

In Situation [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local domain `A` with
punctured spectrum `U`, and a modification `f : X ⟶ Spec(A)` — with `X` normal, the restriction
map `H¹(X, 𝒪_X) ⟶ H¹(f⁻¹(U), 𝒪_X)` is injective. This is
`AlgebraicGeometry.VanishingSituation.firstCohomologyRestriction_injective`, proved in
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDPuncturedRestriction` without
the source's Nagata hypothesis on `A`. This file records Tag 0AXB on that theorem.

## Main results

* `AlgebraicGeometry.VanishingSituation.firstCohomologyRestriction_injective` realizes
  Tag 0AXB.

## References

* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
-/

@[expose] public section

add_to_stacks 0AXB "in Situation 0AX8 with X normal, the restriction map H^1(X, O_X) -> \
H^1(f^{-1}(U), O_X) is injective, for every A (Nagata or not)"
  AlgebraicGeometry.VanishingSituation.firstCohomologyRestriction_injective

end
