module

public import Mathlib.RingTheory.LocalRing.Length
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkLength
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange

/-!
# Length at a geometric point of an algebraic space

Let `X` be an algebraic space over a scheme `S`, let `x̄` be a geometric point of `X` and let
`φ : (U, ū) → (X, x̄)` be a small étale neighbourhood whose chart `U` is a scheme, with `u` the
image in `U` of the chosen lift of `x̄`. The canonical map `𝒪_{U, u} → 𝒪_{X, x̄}` of Stacks 05VP
is faithfully flat and carries the maximal ideal of `𝒪_{U, u}` onto the maximal ideal of
`𝒪_{X, x̄}`, because `𝒪_{X, x̄}` is a strict henselization of `𝒪_{U, u}` (Stacks 04KF). The
base change along a flat local homomorphism multiplies lengths by the length of the fibre ring,
and here that fibre ring is the residue field, so the base change preserves lengths exactly:

`length_{𝒪_{X, x̄}} (𝒪_{X, x̄} ⊗_{𝒪_{U, u}} N) = length_{𝒪_{U, u}} N`

for every `𝒪_{U, u}`-module `N`. Taking `N = 𝒪_{U, u}` gives the case `F = 𝒪_X` of Stacks 0EE1:
the étale local ring at a geometric point and the local ring of an étale scheme chart at a point
over it have the same length. That number is the multiplicity of Stacks 0EE2 for the structure
sheaf, which is the multiplicity with which an irreducible component enters the fundamental
cycle of a closed subspace.

## Main results

* `AlgebraicGeometry.Space.length_chartStalkBaseChange_obj`: the base change of Stacks 05VP
  preserves the length of a module over the local ring of the chart.
* `AlgebraicGeometry.Space.length_etaleLocalRing_eq_length_chartLocalRing`: **Stacks 0EE1 for
  the structure sheaf** — the étale local ring and the local ring of any étale scheme chart over
  the geometric point have equal length.

## Implementation notes

Both statements are about the base change along
`AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing`, so the `Algebra` structure they use is
the one that map induces; there is no such structure in scope globally, and the first statement
is therefore phrased through the functor
`AlgebraicGeometry.Space.chartStalkBaseChange`, whose value on a module is the tensor product in
question. The chart is a neighbourhood of a geometric point and is arbitrary, so the equality
holds for one chart exactly when it holds for every chart, which is the form Stacks 0EE1 takes.

The surjectivity of the maximal ideal statement is obtained from the henselization tower
`AlgebraicGeometry.Space.chartHenselizationTower` rather than from the étale local ring
directly: `IsLocalRing.IsHenselization.map_maximalIdeal` applies to the tower's strict
henselization, and the comparison
`AlgebraicGeometry.Space.chartStrictHenselizationEquiv` of Stacks 04KF transports it, an
isomorphism of local rings carrying the maximal ideal to the maximal ideal.

**No `@[stacks 0EE2]`, `@[stacks 0EE9]` or `@[stacks 0EQL]` attribute is carried.** The general
case of Stacks 0EE1, for a quasi-coherent `𝒪_X`-module `F` rather than for `𝒪_X`, needs the
comparison `F_x̄ = (F|_U)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` asserted by Stacks 05VP, which is not
available — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange`. Consequently the length of a
coherent module at a point, the finiteness and positivity of that length at a generic point of
its support (Stacks 0EE4), and the fundamental cycle `[Y]_k` of a closed subspace of a good
algebraic space (Stacks 0EE9) are all absent; and Stacks 0EQL, which asserts an equality between
two such fundamental cycles, cannot yet be stated.

## References

* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
-/

@[expose] public section

open CategoryTheory IsLocalRing TensorProduct

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

include hX

/-- **Stacks 0EE1 for the structure sheaf.** The étale local ring of an algebraic space at a
geometric point has the same length as the local ring of any étale scheme chart at a point over
it. Since the chart is arbitrary, the two readings of Stacks 0EE1 — some chart and every chart —
agree, and the common value is the length of `𝒪_{X, x̄}`.

This is the case `N = 𝒪_{U, u}` of
`AlgebraicGeometry.Space.length_chartStalkBaseChange_obj`, the base change
`𝒪_{X, x̄} ⊗_{𝒪_{U, u}} 𝒪_{U, u}` being `𝒪_{X, x̄}`. -/
@[stacks 0EE1 "the structure sheaf: lengths agree on an étale scheme chart"]
theorem length_etaleLocalRing_eq_length_chartLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    Module.length ↥(etaleLocalRing B S hS X x) ↥(etaleLocalRing B S hS X x) =
      Module.length ↥(chartLocalRing B S hS X V) ↥(chartLocalRing B S hS X V) := by
  let : Algebra ↥(chartLocalRing B S hS X V) ↥(etaleLocalRing B S hS X x) :=
    (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra
  rw [← length_chartStalkBaseChange_obj.{u, u} B S hS X hX V
    (ModuleCat.of ↥(chartLocalRing B S hS X V) ↥(chartLocalRing B S hS X V))]
  exact (LinearEquiv.length_eq (TensorProduct.AlgebraTensorModule.rid
    ↥(chartLocalRing B S hS X V) ↥(etaleLocalRing B S hS X x)
    ↥(etaleLocalRing B S hS X x))).symm

end AlgebraicGeometry.Space

end
