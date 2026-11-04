module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyRestrictionInjective
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.SplittingBaseChange

/-!
# A tower of projective bundles is universally Chow injective

Let `(S, δ)` be as in Situation 02QL, `X` locally of finite type over `S` and `π : P ⟶ X` a finite
composition of projective space bundles of finite locally free modules of constant rank
(`Stacks.Chow.IsProjectiveBundleTower`). Then flat pullback along every base change of `π` to a
scheme locally of finite type over `S` is injective on Chow groups in every degree: `π` is
universally Chow injective (`Stacks.Chow.UniversallyChowInjective`), which is clause (1) of
Stacks 02UL. Consequently the restriction map `res : A^*(X) ⟶ A^*(P)` of Stacks 0B7F is injective
(`Stacks.Chow.chowCohomologyRestriction_injective`), which is the last assertion of Stacks 02UL.

## Main results

* `Stacks.Chow.IsProjectiveBundleTower.universallyChowInjective` — a tower of projective bundles
  is universally Chow injective.
* `Stacks.Chow.IsProjectiveBundleTower.chowCohomologyTotalRestriction_injective` — along such a
  tower `res : A^*(X) ⟶ A^*(P)` is injective.

## References

* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] SplittingMorphism.locallyOfFiniteType_π SplittingMorphism.flat_π

/-- **Clause (1) of Stacks 02UL for a tower of projective bundles.** Flat pullback along every base
change of a tower of projective bundles, to a scheme locally of finite type over the base with an
arbitrary structure morphism, is injective on Chow groups in every degree. -/
theorem IsProjectiveBundleTower.universallyChowInjective {C : ChowSituation.{u}}
    {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {d : ℕ}
    {T : SplittingMorphism C sX d} (hT : IsProjectiveBundleTower C sX d T) :
    UniversallyChowInjective C T.π d T.relDim :=
  fun sT _ f _ q _ _ hsq k ↦
    hT.injective_flatPullbackChow_of_isPullback sT f _ q rfl _ hsq _ k _

/-- **The last assertion of Stacks 02UL for a tower of projective bundles.** For every Gysin system
natural under base-change isomorphisms, the restriction map `res : A^*(X) ⟶ A^*(P)` of Stacks 0B7F
along a tower of projective bundles is injective: it is so in every degree by
`Stacks.Chow.chowCohomologyRestriction_injective`, since the tower is universally Chow
injective. -/
theorem IsProjectiveBundleTower.chowCohomologyTotalRestriction_injective {C : ChowSituation.{u}}
    {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {d : ℕ}
    {T : SplittingMorphism C sX d} (hT : IsProjectiveBundleTower C sX d T) (G : GysinSystem C)
    (hgys : G.IsNaturalUnderBaseChangeIso) :
    Function.Injective (chowCohomologyTotalRestriction C G sX T.π hgys) :=
  (DirectSum.map_injective _).mpr fun p ↦
    chowCohomologyRestriction_injective C G sX T.π p d T.relDim hT.universallyChowInjective hgys

end Stacks.Chow

end
