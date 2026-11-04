module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteConstantSheafLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteTerminalCohomology

/-!
# `Lg_! ℤ = ℤ` on the flat-fppf site of a stack whose flat-fppf site has a terminal object

Let `𝒳` be an algebraic stack whose flat-fppf site has a terminal object whose image is terminal
in the fppf site. For the `Lg_!` of Stacks 07AS (3), the canonical comparison `Lg_! ℤ ⟶ ℤ` is an
isomorphism (Stacks 0H0Z).

## Main results

* `AlgebraicGeometry.Stack.FlatFppf`
  `.isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf_of_isTerminal`: the counit of
  the derived adjunction `Lg_! ⊣ g⁻¹` is invertible at the constant sheaf `ℤ` in degree zero.

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- For an algebraic stack `𝒳` whose flat-fppf site has a terminal object `e` whose image is
terminal in the fppf site, the counit of the derived adjunction `Lg_! ⊣ g⁻¹` is invertible at the
constant sheaf `ℤ` of `𝒳_{fppf}` in degree zero, so the canonical comparison `Lg_! ℤ ⟶ ℤ` is an
isomorphism. -/
@[stacks 0H0Z "for the `Lg_!` of 07AS part (3), the flat-fppf site of an algebraic stack whose \
flat-fppf site has a terminal object whose image is terminal in the fppf site"]
theorem isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf_of_isTerminal
    {e : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)} (he : IsTerminal e)
    (heX : IsTerminal ((objectProperty B S hS 𝒳).ι.obj e)) :
    IsIso ((derivedAbelianLowerShriekAdjunction B S hS 𝒳
          (abelianLowerShriekAcyclic B S hS 𝒳)).counit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) :=
  have := preservesCoveringPullbacks_inclusion B S hS 𝒳
  (derivedAbelianLowerShriek_constantSheaf B S hS 𝒳).2.2

end Derived

end AlgebraicGeometry.Stack.FlatFppf

end
