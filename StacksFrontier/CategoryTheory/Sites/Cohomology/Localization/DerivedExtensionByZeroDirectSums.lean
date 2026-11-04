module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# Derived extension by zero commutes with direct sums

Let `X` be a ringed site and let `U` be an object of its underlying category.  On the unbounded
derived categories of sheaves of modules, extension by zero `j_!` along the localization at
`U` is a left adjoint of restriction `j^{-1}`, which is
`Stacks.Cohomology.Localization.derivedExtensionByZeroRestrictionAdjunction`,
[Stacks, Tag 08FJ].  Hence it commutes with direct sums — indeed with all colimits.

This is the open immersion case of the proof of [Stacks, Tag 0G29], that derived lower shriek
`Rf_! = R(fbar)_* ∘ j_!` of a finite type separated morphism of quasi-compact and
quasi-separated schemes commutes with direct sums: the source reduces that statement to the
case of an open immersion, where the reason is exactly the one above, and to the case of a
proper morphism, where it is [Stacks, Tag 0GIW] or [Stacks, Tag 0F0D].  The reduction and the
proper case are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.DirectSums`.

## Main results

* `Stacks.Cohomology.Localization.preservesColimitsOfSize_derivedExtensionByZero`.

## References

* [Stacks Project, Tag 08FJ](https://stacks.math.columbia.edu/tag/08FJ)
* [Stacks Project, Tag 0G29](https://stacks.math.columbia.edu/tag/0G29)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Stacks.Cohomology.Localization

universe w w' u

attribute [local instance] HasDerivedCategory.standard

/-- **The open immersion case of the proof of [Stacks, Tag 0G29].** On the unbounded derived
categories of sheaves of modules over a ringed site, extension by zero along the localization
at an object commutes with direct sums — indeed with all colimits — because it is a left
adjoint of restriction, which is [Stacks, Tag 08FJ],
`Stacks.Cohomology.Localization.derivedExtensionByZeroRestrictionAdjunction`.

The source of [Stacks, Tag 0G29] reduces the commutation of `Rf_!` with direct sums to this
statement for an open immersion and to [Stacks, Tag 0GIW] or [Stacks, Tag 0F0D] for a proper
morphism; this is the half of the reduction that is available outright. -/
@[stacks 0G29 "the open immersion case of the proof: j_! commutes with direct sums"]
theorem preservesColimitsOfSize_derivedExtensionByZero (X : RingedSite.{u, u, u}) (U : X.C) :
    PreservesColimitsOfSize.{w, w'}
      (SheafOfModules.pullback.{u} (F := Over.forget U)
        (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))).mapDerivedCategory :=
  (derivedExtensionByZeroRestrictionAdjunction X U).leftAdjoint_preservesColimits

end Stacks.Cohomology.Localization

end
