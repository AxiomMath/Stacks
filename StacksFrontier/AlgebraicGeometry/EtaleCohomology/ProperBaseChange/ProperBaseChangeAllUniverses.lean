module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CoefficientUniverseTransfer
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The proper base change theorem at every coefficient universe

[Stacks, Tag 095T] for abelian sheaves with sections in `AddCommGrpCat.{max (u + 1) v}`, for every
universe `v`: for a proper morphism `f : X ⟶ Y` of schemes, every cartesian square and every
torsion abelian sheaf `F` on `X_étale`, the base change map `g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` is an
isomorphism.

## Main results

* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper_allUniverses`.

## Implementation notes

The quasi-compactness and quasi-separatedness of `f` are written out from the definitions rather
than found by instance search: among the imports, the instance
`Stacks.Models.RegularModelSituation.quasiCompact` makes every search for `QuasiCompact _` explore
regular models and time out.

The theorem at the smallest coefficient universe is
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`; the transfer to every
universe is `Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.of_univ_zero`, which needs `f`
quasi-compact and quasi-separated, as a proper morphism is.

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory.Limits

universe v u

namespace Stacks.EtaleCohomology

/-- **The proper base change theorem at every coefficient universe** ([Stacks, Tag 095T]). For a
proper morphism `f : X ⟶ Y`, cohomology commutes with base change for torsion abelian sheaves with
sections in `AddCommGrpCat.{max (u + 1) v}`, whatever the universe `v`. -/
@[sga "4 XII 5.2" "more general"]
theorem cohomologyCommutesWithBaseChange_of_isProper_allUniverses {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] : CohomologyCommutesWithBaseChange.{u, v} f :=
  haveI : QuasiCompact f := ⟨fun _ _ ↦ f.isProperMap.isCompact_preimage⟩
  haveI : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
  haveI : QuasiSeparated f := ⟨⟨fun _ _ hc ↦
    (pullback.diagonal f).isClosedEmbedding.isCompact_preimage hc⟩⟩
  have h0 : CohomologyCommutesWithBaseChange.{u, 0} f :=
    cohomologyCommutesWithBaseChange_of_isProper f
  h0.of_univ_zero

end Stacks.EtaleCohomology

end
