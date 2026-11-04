module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# Equation 05ZL for sheaves of abelian groups

For a thickening `G ⊂ X` of algebraic spaces over a scheme `S`, Equation
[Stacks Project, Tag 05ZL] is the identification

`X_{spaces, étale} = X'_{spaces, étale}`

of the two spaces-étale sites.  `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/EtaleTopos.lean`
proves it for sheaves of **sets**, as
`AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening` and
`AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening`.  This file reads the same
equation at the coefficient category of sheaves of **abelian groups**, which is the form the
sheaf acting on the lifts of [Stacks Project, Tag 061D] is stated in.

## Why nothing new is proved

The whole content of the identification is that base change of étale scheme charts along the
inclusion of a thickening exhibits one small étale site as a *dense subsite* of the other,
`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite` — and that statement mentions
no coefficients.  `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` turns it into an
equivalence of sheaf categories at **any** coefficient category with the limits sheaves need.
So the abelian reading is the set-valued construction with `Type (u + 1)` replaced by
`AddCommGrpCat.{u + 1}`; the covering-sieve half, which is the geometry, is spent once and
already.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleAbelianSheafEquiv_of_isThickening`: **Equation
  [Stacks Project, Tag 05ZL] for abelian sheaves, chart form** — the sheaves of abelian groups on
  the small étale site of `X` and on that of the thickening are equivalent.
* `AlgebraicGeometry.Space.spacesEtaleAbelianSheafEquiv_of_isThickening`: **the same on the
  spaces-étale sites**, which is the spelling of the equation.

## Implementation notes

The coefficient universe is `AddCommGrpCat.{u + 1}`, the universe in which
`AlgebraicGeometry.Space.LiftDerivationAction` takes its acting sheaf: the sections of the sheaf
of `𝒪`-linear maps over an étale object are the morphisms of the restrictions, which lie one
universe above the structure rings.

As in the set-valued construction, the equivalence of the spaces-étale categories is the chart
form conjugated by the two comparison equivalences of [Stacks Project, Tag 03G1], and only the
equivalence of topoi is asserted: the identification of the two structure sheaves, which is what
makes [Stacks Project, Tag 05ZM] an equivalence of *locally ringed* topoi, is
`AlgebraicGeometry.Space.smallEtaleRingSheafEquiv_of_isThickening` together with
`AlgebraicGeometry.Space.isIso_ringUnit_of_isThickening`, and is not part of this statement.

## References

* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL), the equation.
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM), the equivalence of
  topoi.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D), the acting sheaf this
  serves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- **Equation [Stacks Project, Tag 05ZL] for sheaves of abelian groups, chart form.**  The
sheaves of abelian groups on the small étale site of an algebraic space `X` and on the small
étale site of a thickening `G ⊂ X` of it are equivalent, by restriction along base change of
étale scheme charts.

This is the comparison lemma for the dense subsite inclusion
`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite`, read at `AddCommGrpCat`
rather than at `Type`: the dense-subsite statement mentions no coefficients. -/
noncomputable def smallEtaleAbelianSheafEquiv_of_isThickening (hG : IsThickening B S hS X G) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ≌
      Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
        AddCommGrpCat.{u + 1} :=
  letI := thickeningChartBaseChange_isDenseSubsite B S hS hG
  Functor.IsDenseSubsite.sheafEquiv (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
    (thickeningChartBaseChange B S hS hG) AddCommGrpCat.{u + 1}

/-- **Equation [Stacks Project, Tag 05ZL] for sheaves of abelian groups.**  For a thickening
`G ⊂ X` of algebraic spaces over `S`, the sheaves of abelian groups on the spaces-étale site of
`X` and those on the spaces-étale site of `G` are canonically equivalent.

The equivalence is the chart form
`AlgebraicGeometry.Space.smallEtaleAbelianSheafEquiv_of_isThickening` conjugated by the two
comparison equivalences of [Stacks Project, Tag 03G1], exactly as the set-valued
`AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening` is. -/
@[stacks 05ZL "the identification of the two spaces-etale topoi, at sheaves of abelian groups"]
noncomputable def spacesEtaleAbelianSheafEquiv_of_isThickening (hG : IsThickening B S hS X G) :
    Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1} ≌
      Sheaf (SpacesEtale.topology B S hS (IsThickening.space B S hS hG))
        AddCommGrpCat.{u + 1} :=
  ((comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S hS X.1)
        (SpacesEtale.topology B S hS X)).asEquivalence.trans
    ((smallEtaleAbelianSheafEquiv_of_isThickening B S hS hG).trans
      ((comparisonFunctor B S hS (IsThickening.space B S hS hG)).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1}
          (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
          (SpacesEtale.topology B S hS
            (IsThickening.space B S hS hG))).asEquivalence.symm)

end AlgebraicGeometry.Space

end
