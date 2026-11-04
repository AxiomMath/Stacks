module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleAbelianSheafEquiv
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomology

/-!
# Étale cohomology is unchanged by a thickening

Let `X ⊂ X'` be a thickening of algebraic spaces over `S`. The cohomology of an abelian sheaf
on the small étale site of `X` is the cohomology of its restriction to the small étale site of
`X'`, in every degree and compatibly with the maps induced by morphisms of sheaves.

## Main definitions

* `AlgebraicGeometry.Space.thickeningRestrictAddSheaf`: restriction of an abelian sheaf along
  base change of étale charts.
* `AlgebraicGeometry.Space.thickeningCohomologyAddEquiv`: the resulting isomorphism of
  cohomology groups, in every degree.

## Main results

* `AlgebraicGeometry.Space.thickeningCohomologyAddEquiv_map`: the isomorphism commutes with the
  maps induced on cohomology by a morphism of abelian sheaves.

## Implementation notes

The `Ext` universe is `u + 1`, the universe of the objects of the small étale site, as in
`AlgebraicGeometry.Space.hasExt_sheaf_smallEtale`.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 0DNM](https://stacks.math.columbia.edu/tag/0DNM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsThickening B S hS X G)

/-- An abelian sheaf on the small étale site of the closed member of a thickening is read on the
small étale site of the ambient member by restricting along base change of étale charts. -/
abbrev thickeningRestrictAddSheaf :
    Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) AddCommGrpCat.{u} ⥤
      Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} :=
  (thickeningChartBaseChange B S hS hG).sheafPushforwardContinuous AddCommGrpCat.{u}
    (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)

/-- The cohomology of an abelian sheaf on the small étale site of the closed member of a
thickening is the cohomology of its restriction to the small étale site of the ambient member, in
every degree. -/
def thickeningCohomologyAddEquiv
    (F : Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) AddCommGrpCat.{u})
    (n : ℕ) :
    Sheaf.H.{u + 1} F n ≃+
      Sheaf.H.{u + 1} ((thickeningRestrictAddSheaf B S hS hG).obj F) n :=
  Stacks.Cohomology.DenseSubsite.hAddEquiv (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
    (thickeningChartBaseChange B S hS hG) F n

/-- The comparison of cohomology along a thickening commutes with the maps induced by a morphism
of abelian sheaves. -/
theorem thickeningCohomologyAddEquiv_map
    {F F' : Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
      AddCommGrpCat.{u}} (f : F ⟶ F') (n : ℕ) (x : Sheaf.H.{u + 1} F n) :
    thickeningCohomologyAddEquiv B S hS hG F' n (Sheaf.H.map.{u + 1} f n x) =
      Sheaf.H.map.{u + 1} ((thickeningRestrictAddSheaf B S hS hG).map f) n
        (thickeningCohomologyAddEquiv B S hS hG F n x) :=
  Stacks.Cohomology.DenseSubsite.hAddEquiv_map (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
    (thickeningChartBaseChange B S hS hG) f n x

end AlgebraicGeometry.Space

end
