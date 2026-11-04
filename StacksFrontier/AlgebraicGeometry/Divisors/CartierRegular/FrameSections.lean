module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.LocalEquation

/-!
# Sections of a trivialized module over an open

A trivialization `L|_U ≅ 𝒪_U` of a module `L` on a scheme `X` over an open `U`, taken in the
category of modules over the restricted structure sheaf, evaluates to a `Γ(X, U)`-linear
equivalence `Γ(L, U) ≃ₗ Γ(X, U)`. That equivalence is the concrete form in which a trivialization
is used: the zero scheme of a section `s` of an invertible module is cut out on `U` by the single
function `e (s|_U)`, by `Stacks.Divisors.zeroScheme_ideal_of_trivialization`.

## Main definitions

* `Stacks.Divisors.frameSections` — the `Γ(X, U)`-linear equivalence `Γ(L, U) ≃ₗ Γ(X, U)`
  determined by a trivialization of `L` over `U`.

## Implementation notes

Evaluation is `SheafOfModules.evaluation` at the terminal object `𝟙 U` of the over-site of `U`,
whose module of sections is `Γ(L, U)` on the nose; so no transport along an identification of opens
is needed, in contrast with the trivializations indexed by the open subscheme `U` used in
`StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization`.

The open `U` is arbitrary here. Affineness is needed only by the consumers, which read the
equivalence against `Stacks.Divisors.zeroScheme_ideal`.

## References

* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

/-- The `Γ(X, U)`-linear equivalence `Γ(L, U) ≃ₗ Γ(X, U)` obtained by evaluating a trivialization
`eU : L|_U ≅ 𝒪_U` of a module `L` on a scheme `X` over an open `U` at the terminal object of the
over-site of `U`. -/
def frameSections (X : Scheme.{u}) (L : X.Modules) {U : X.Opens}
    (eU : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Γ(L, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  ((_root_.SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (Opposite.op (Over.mk (𝟙 U)))).mapIso eU).toLinearEquiv

end Stacks.Divisors

end
