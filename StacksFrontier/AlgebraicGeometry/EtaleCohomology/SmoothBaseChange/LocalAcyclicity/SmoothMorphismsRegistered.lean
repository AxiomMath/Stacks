module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.LocalAcyclicity.SmoothMorphisms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Unconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smooth morphisms are universally locally acyclic

[Stacks, Proposition 0GJQ]: a smooth morphism of schemes is universally locally acyclic. This is
`Stacks.EtaleCohomology.SmoothBaseChange.isUniversallyLocallyAcyclic_of_smooth` with each input of
the smooth base change theorem (Stacks 0EYU) supplied by the proved theorem used in
`Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth`.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.isUniversallyLocallyAcyclic_of_smooth_unconditional`

## References

* [Stacks Project, Tag 0GJQ](https://stacks.math.columbia.edu/tag/0GJQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

/-- **Smooth morphisms are universally locally acyclic** ([Stacks, Proposition 0GJQ]). Let
`f : X ⟶ S` be a smooth morphism of schemes. Then `f` is universally locally acyclic: for every
morphism `S' ⟶ S` and every big étale site containing `X ×_S S'` and `S'`, the base change
`X ×_S S' ⟶ S'` of `f` is locally acyclic there. -/
@[stacks 0GJQ, sga "4½ Arcata 5.2.1" "more general", sga "7 I 2.4" "partial"]
theorem isUniversallyLocallyAcyclic_of_smooth_unconditional {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] : IsUniversallyLocallyAcyclic f :=
  isUniversallyLocallyAcyclic_of_smooth flatReducedFibresBaseChange etaleLocalHigherBaseChange
    higherBaseChangePaste firstFailureNormalization affineCurveCohomologyVanishing
    curveCohomologyAlgClosedInvariance
    (fun D hD => Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne D hD) f

end Stacks.EtaleCohomology.SmoothBaseChange

end
