module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections

/-!
# The ring of meromorphic functions over a chart, in the spelling the module action uses

The sections of the sheaf `𝒦_F` of meromorphic functions of Stacks 0EN3 over an étale chart `U`
carry two spellings in this library:

* `(Stacks.SheafOfModules.Tensor.ringSheaf
  (AlgebraicGeometry.Space.meromorphicRingedSite B S hS F hF).O).obj.obj (op U)`, the
  `RingCat`-valued structure sheaf of the meromorphic ringed site, which is the sheaf of rings
  over which the sections of the sheaf `𝒦_F(M)` of meromorphic sections of Stacks 0EN5 are
  modules;
* `(AlgebraicGeometry.Space.meromorphicFunctionSheaf B S hS F hF).obj.obj (op U)`, the
  `CommRingCat` object, which is where commutativity lives and hence the only one of the two on
  which `IsFractionRing` — Stacks 0EN6, part (2) — can be stated.

The two carriers are definitionally equal, the first being the second with its commutativity
forgotten, but instance search does not bridge them: `CommRing` is not found at the first
spelling and the scalar action does not elaborate at the second.  This file registers the
missing instance, so that a statement mixing the fraction-ring structure of `𝒦_F(U)` with the
`𝒦_F(U)`-module structure of `𝒦_F(M)(U)` needs no bridge placed by hand.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicChartRing` names the first spelling, as
  `AlgebraicGeometry.Space.chartRing` names the corresponding spelling for `𝒪_F`.
* `AlgebraicGeometry.Space.meromorphicChartRing_commRing` is the missing `CommRing` instance.

## Implementation notes

The instance is built by adding `mul_comm` to the ambient `Ring` instance rather than by
transporting the whole `CommRing` structure across the two spellings, exactly as
`AlgebraicGeometry.Space.chartRing_commRing` does for `𝒪_F`: the `Ring` field of the result is
then *syntactically* the one the `ModuleCat`-valued sections of `𝒦_F(M)` are modules over, which
is what keeps `Module (meromorphicChartRing …) (…)` solvable by instance search.

## References

* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The ring `𝒦_F(U)` of meromorphic functions over an étale chart `U`, read off the structure
sheaf of the meromorphic ringed site — the spelling over which the sections of the sheaf of
meromorphic sections of an `𝒪_F`-module are modules. -/
noncomputable abbrev meromorphicChartRing (U : SmallEtale B S hS F) : Type u :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj.obj (op U)

/-- **The sections of `𝒦_F` over a chart form a *commutative* ring.**  The `RingCat`-valued
structure sheaf of the meromorphic ringed site is the `CommRingCat`-valued
`AlgebraicGeometry.Space.meromorphicFunctionSheaf` with its commutativity forgotten.

Only `mul_comm` is added to the ambient `Ring` instance, so that instance remains syntactically
the one over which the sections of `𝒦_F(M)` are modules. -/
noncomputable instance meromorphicChartRing_commRing (U : SmallEtale B S hS F) :
    CommRing (meromorphicChartRing B S hS F hF U) :=
  letI r : Ring (meromorphicChartRing B S hS F hF U) := inferInstance
  { r with
    mul_comm := by
      change ∀ a b : (meromorphicFunctionSheaf B S hS F hF).obj.obj (op U), a * b = b * a
      exact mul_comm }

end AlgebraicGeometry.Space

end
