module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.ModuleAbelianComparison
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.ModuleDirectSums

/-!
# Vanishing of a higher direct image passes from modules to abelian sheaves

`Stacks.AlgebraicGeometry.HigherDirectImage.rightDerivedPushforwardToSheafIso` identifies the
higher direct images of a sheaf of modules on a scheme with those of its underlying sheaf of
abelian groups, for an arbitrary morphism of schemes and every degree.  This file reads the
vanishing of such a higher direct image across that identification.

The direction recorded is the one a consumer needs.  A vanishing theorem about `R^p f_*` is
proved in sheaves of modules — that is where the quasi-coherent machinery, the filtration
arguments and the base-change statements live — while an argument about a *sheaf of rings*, such
as the quotient map of a square-zero extension, has to run in sheaves of abelian groups, the
extension sheaf not being a module.  So the module-level vanishing is the hypothesis and the
abelian-level one the conclusion.

## Main results

* `Stacks.AlgebraicGeometry.HigherDirectImage.isZero_rightDerived_abelianPushforward_toSheaf`:
  **the vanishing travels.** If `R^p f_*` kills a sheaf of modules then the direct image of
  abelian sheaves kills its underlying abelian sheaf in the same degree.

## Implementation notes

`Stacks.AlgebraicGeometry.HigherDirectImage.abelianPushforward_eq` is what lets the conclusion be
stated with `TopCat.Sheaf.pushforward`, the spelling in which direct image along a continuous map
is usually met, rather than with the `sheafPushforwardContinuous` of the comparison: the two
functors are equal by `rfl`.

Only additivity of `SheafOfModules.toSheaf` is used, through
`CategoryTheory.Functor.map_isZero`; no exactness of it and no property of `f` is needed, the
comparison isomorphism carrying all of that.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.HigherDirectImage

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) (M : X.Modules)

/-- **The vanishing of a higher direct image passes from sheaves of modules to sheaves of abelian
groups.** If `R^p f_*M = 0` in sheaves of `𝒪_Y`-modules, then the `p`-th right derived functor of
the direct image of abelian sheaves along the continuous map of `f` annihilates the abelian sheaf
underlying `M`.

Forgetting the module structure of a zero object gives a zero object, and
`Stacks.AlgebraicGeometry.HigherDirectImage.rightDerivedPushforwardToSheafIso` identifies that
with the abelian higher direct image of the abelian sheaf underlying `M`. -/
theorem isZero_rightDerived_abelianPushforward_toSheaf
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived p).obj M)) :
    IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).rightDerived p).obj
      ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M)) := by
  have h1 : IsZero ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).obj
      (((Scheme.Modules.pushforward f).rightDerived p).obj M)) :=
    (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map_isZero h
  exact h1.of_iso ((rightDerivedPushforwardToSheafIso f p).app M).symm

end Stacks.AlgebraicGeometry.HigherDirectImage

end
