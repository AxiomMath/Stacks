module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapInvertibleSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FirstChernCapChowCommute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClassesIsoInvariance

/-!
# The properties of the Chern classes

The Chern classes of Stacks 0ERZ (`AlgebraicGeometry.Space.PrivateChern.chernCap`) have all the
properties of `AlgebraicGeometry.Space.PrivateChern.ChernCapProperties`: they vanish above the
rank and satisfy the Whitney formula (Stacks 0ES9; both from Stacks 0ES8,
`AlgebraicGeometry.Space.PrivateChern.chernCap_succ_eq_of_shortComplex`, by the splitting
principle, Stacks 0ESC, and the compatibility with flat pullback,
`AlgebraicGeometry.Space.PrivateChern.chernCap_spaceModulePullback_flatPullbackChow`), `c₁` is
additive on tensor products of invertible modules with `c₁(𝒪) = 0` (Stacks 0EQK), they are
invariant under isomorphism, and the first Chern classes of modules of rank one commute
(Stacks 0EQZ).

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chernCapProperties`: the Chern classes have the
  properties of `AlgebraicGeometry.Space.PrivateChern.ChernCapProperties`.

## References

* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
* [Stacks Project, Tag 0ES9](https://stacks.math.columbia.edu/tag/0ES9)
* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u})

/-- **The properties of the Chern classes** (vanishing above the rank, the Whitney formula,
additivity of `c₁` on tensor products of invertible modules, `c₁(𝒪) = 0`, invariance under
isomorphism, commutativity of first Chern classes). -/
theorem chernCapProperties : ChernCapProperties.{u, u + 1} D where
  chernCap_eq_zero_of_lt hP E r h _n hn :=
    chernCap_eq_zero_of_lt_of_hasIntertwiningSplittings
      chernCap_succ_eq_of_shortComplex
      (hasIntertwiningSplittings_of_flatPullbackChow
        chernCap_spaceModulePullback_flatPullbackChow)
      hP E r h hn
  chernCap_shortExact hP _ hT _r₁ _r₃ h₁ h₂ h₃ n :=
    chernCap_shortExact_of_succ
      chernCap_succ_eq_of_shortComplex hP hT h₁ h₂ h₃ n
  chernCap_one_tensorObj hP L M hL hM hLM := chernCap_one_tensorObj hP L M hL hM hLM
  chernCap_congr_iso hP E E' r h h' n e := chernCap_congr_iso hP E E' r h h' n e
  chernCap_one_tensorUnit hP h := chernCap_one_tensorUnit hP h
  chernCap_one_commute hP L M hL hM := chernCap_one_commute D hP L M hL hM

end AlgebraicGeometry.Space.PrivateChern

end
