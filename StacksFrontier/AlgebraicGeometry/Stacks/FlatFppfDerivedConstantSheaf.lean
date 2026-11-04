module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedLowerShriekOfTheConstantSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of the constant sheaf to the flat-fppf site

Let `𝒳` be an algebraic stack and let `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the comparison
morphism of topoi, so that `g⁻¹` is restriction to the flat objects and `Lg_!` is the derived
lower shriek of **Stacks 07AS (3)**. **Stacks 0H0Z** asserts `Lg_! ℤ = ℤ`, in the form that
pins down the map: the counit of the derived adjunction `Lg_! ⊣ g⁻¹` is invertible at the
constant sheaf `ℤ` of `𝒳_{fppf}` placed in degree zero. Since restriction carries the constant
sheaf to the constant sheaf —
`Stacks.Cohomology.DerivedLowerShriek.restriction_constantSheafIso`, recorded here for this
inclusion as `AlgebraicGeometry.Stack.FlatFppf.restriction_constantSheafIso` — the counit at
`ℤ_𝒳[0]` is the canonical map

`Lg_! ℤ_{𝒳_{flat,fppf}} ⟶ ℤ_𝒳`.

Stacks 0H0Z itself, for both the lisse-étale and the flat-fppf site and with nothing assumed, is
`AlgebraicGeometry.Stack.derivedAbelianLowerShriek_constantSheaf` in
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteConstantSheafLowerShriek.lean`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.restriction_constantSheafIso`: `g⁻¹ℤ_𝒳 ≅ ℤ_{𝒳_{flat,fppf}}`,
  with no hypothesis.

## References

* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Restriction to the flat-fppf site carries the constant sheaf `ℤ` to the constant sheaf
`ℤ`**, with no hypothesis: the instance of
`Stacks.Cohomology.DerivedLowerShriek.restriction_constantSheafIso` at the inclusion of the flat
objects, whose continuity and cocontinuity hold for every algebraic stack.

This is what identifies the source of the counit of the derived adjunction at `ℤ_𝒳[0]` with
`Lg_! ℤ_{𝒳_{flat,fppf}}`. -/
def restriction_constantSheafIso :
    (constantSheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≅
      (subsiteRestriction B S hS 𝒳.val.val.p B.topology (objectProperty B S hS 𝒳)).obj
        ((constantSheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  Stacks.Cohomology.DerivedLowerShriek.restriction_constantSheafIso
    (objectProperty B S hS 𝒳).ι (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳)
    AddCommGrpCat.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} ℤ))

end AlgebraicGeometry.Stack.FlatFppf

end
