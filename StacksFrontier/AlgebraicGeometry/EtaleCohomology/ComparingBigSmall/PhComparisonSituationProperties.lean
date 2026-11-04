module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.PhComparisonSituation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# The ph and étale topologies satisfy the properties of the comparison situation

Let `B` be a big ph site, so that its underlying category carries the ph topology and, through
`AlgebraicGeometry.phAssociatedBigEtaleSite`, the étale topology. Take the proper morphisms as
the class `𝒫`, and over every object `X` the class `𝒜'_X` of abelian sheaves on `(Sch/X)_étale`
of the form `π_X⁻¹F` with `F` a torsion abelian sheaf on `X_étale`. Then `𝒜'_X` is a weak Serre
subcategory, and properties (0EZ4)–(0EZ8) of the comparison situation of Stacks 0EZ3 hold for the
comparison of the ph topology with the étale topology.

## Main definitions

* `AlgebraicGeometry.BigPHSite.phEtaleCohomologyComparisonOfProperBaseChange` — the comparison
  situation for the ph and étale topologies, with the two proper base change inputs of
  `AlgebraicGeometry.phEtaleCohomologyComparison` supplied by their proofs.

## Main results

* `AlgebraicGeometry.BigPHSite.exists_phEtaleCohomologyComparison` — there is a comparison
  situation `Stacks.ComparingTopologies.CohomologyComparison` whose finer topology is the ph
  topology of `B`, whose coarser topology is the étale topology, whose distinguished class is the
  class of proper morphisms and whose classes `𝒜'_X` are the sheaves `π_X⁻¹F` with `F` torsion.

## Implementation notes

The classes `𝒜'_X` live on the localization of the coarser topology of the situation, so their
identification with `AlgebraicGeometry.smallEtaleTorsionPullbackClass` is stated as a
heterogeneous equality, the two ambient categories being equal by the identification of the
coarser topology.

## References

* [Stacks Project, Tag 0F0I](https://stacks.math.columbia.edu/tag/0F0I)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigPHSite

/-- For a big ph site `B`, the comparison of the ph topology with the étale topology on its
underlying category, with the proper morphisms as distinguished class and the sheaves `π_X⁻¹F`
with `F` torsion as the classes `𝒜'_X`: `AlgebraicGeometry.phEtaleCohomologyComparison` with its
two inputs supplied by the proper base change theorems Stacks 0A3U and Stacks 095T. -/
public def phEtaleCohomologyComparisonOfProperBaseChange (B : BigPHSite.{u}) :
    Stacks.ComparingTopologies.CohomologyComparison (phAssociatedBigEtaleSite B).Scheme :=
  phEtaleCohomologyComparison B
    (fun f g g' f' sq hf =>
      have := hf
      Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq)
    (fun f _ => Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f)

/-- Consider the comparison of the ph topology of a big ph site `B` with the étale topology on
the same category of schemes. Let `𝒫` be the class of proper morphisms, and for `X` in the site
let `𝒜'_X ⊂ Ab((Sch/X)_étale)` be the full subcategory of sheaves of the form `π_X⁻¹F` with `F` a
torsion abelian sheaf on `X_étale`. Then `𝒜'_X` is a weak Serre subcategory and properties
(0EZ4)–(0EZ8) of the comparison situation of Stacks 0EZ3 hold: there is a comparison situation
with the ph topology as finer topology, the étale topology as coarser topology, `𝒫` as
distinguished class and the `𝒜'_X` as weak Serre classes. -/
@[stacks 0F0I]
public theorem exists_phEtaleCohomologyComparison (B : BigPHSite.{u}) :
    ∃ S : Stacks.ComparingTopologies.CohomologyComparison (phAssociatedBigEtaleSite B).Scheme,
      S.fineCoverage = B.precoverage ∧
      S.coarseCoverage = (phAssociatedBigEtaleSite B).precoverage ∧
      S.morphismProperty = (fun _ _ f => IsProper ((phAssociatedBigEtaleSite B).inclusion.map f)) ∧
      ∀ X : (phAssociatedBigEtaleSite B).Scheme,
        HEq (S.weakSerre X)
          (smallEtaleTorsionPullbackClass (phAssociatedBigEtaleSite B) X
            ((phAssociatedBigEtaleSite B).topology.over X)) :=
  ⟨phEtaleCohomologyComparisonOfProperBaseChange B, rfl, rfl, rfl, fun _ => HEq.rfl⟩

end BigPHSite

end AlgebraicGeometry

end
