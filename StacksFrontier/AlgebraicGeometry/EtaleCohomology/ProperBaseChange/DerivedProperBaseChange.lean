module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeBoundedBelow
import StacksCore.Tactic.StacksAttribute

/-!
# Proper base change for bounded below complexes with torsion cohomology

Let `f : X ⟶ Y` be a proper morphism of schemes, `g : Y' ⟶ Y` a morphism and `X' = Y' ×_Y X`.
For every bounded below object `E` of the derived category of abelian sheaves on `X_étale` with
torsion cohomology sheaves, the base change map `g^{-1} Rf_* E ⟶ Rf'_* (g')^{-1} E` is an
isomorphism. This is [Stacks, Tag 0DDE]: the proper base change theorem (Tag 095T) for single
torsion sheaves, `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`, passed to
complexes by
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange`.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isProper`: [Stacks, Tag 0DDE].

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- **Stacks Project, Tag 0DDE.** Let `f : X ⟶ Y` be a proper morphism of schemes, `g : Y' ⟶ Y`
a morphism of schemes, and `X' = Y' ×_Y X`, given as a cartesian square `sq` with projections
`f' : X' ⟶ Y'` and `g' : X' ⟶ X`. Let `E` be an object of the derived category of abelian sheaves
on `X_étale` which is bounded below and has torsion cohomology sheaves. Then the base change map
`g^{-1} Rf_* E ⟶ Rf'_* (g')^{-1} E` of Tag 0A2A is an isomorphism. -/
@[stacks 0DDE, sga "4 XVII 4.3.2" "special case", sga "4 XVII 5.2.7" "(ii), special case"]
theorem isIso_etaleAbelianDerivedBaseChange_of_isProper {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ)
    (hE : E.IsGE n)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology E) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, 0} f g g' f' sq.w).app E) :=
  isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange
    (cohomologyCommutesWithBaseChange_of_isProper f) sq E n hE hT

end Stacks.EtaleCohomology
