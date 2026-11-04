module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Equiv
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekModuleExactness
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of extension by zero of sheaves of modules on small étale sites

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X` of
Tag 021B, and let `Λ` be a ring. Extension by zero of sheaves of `Λ`-modules along `j`,
`AlgebraicGeometry.moduleExtensionByZero`, is a left adjoint, so it preserves finite colimits for
free. This file proves it preserves finite limits as well: that is the exactness assertion of
Tag 03S5, on the sites of Tag 021B and for sheaves of modules.

The proof is the general criterion of Tag 04BH for module coefficients,
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits_module`: the small étale site of `U` has
fibre products and equalizers, and composition with `j` preserves them, because under the
identification of the small étale site of `U` with the localization of the small étale site of
`X` at `U` it becomes the forgetful functor of that slice, which creates connected limits.

## Main results

* `AlgebraicGeometry.hasEqualizers_smallEtale` — the small étale site has equalizers.
* `AlgebraicGeometry.preservesEqualizers_smallEtalePostcompose` — composition with `j` preserves
  them. Both are theorems rather than instances: as instances they would be tried against every
  limit-shape goal, and the universe metavariables they then introduce leave the universe
  unifier with constraints it cannot solve.
* `AlgebraicGeometry.moduleSheaf_hasSheafify` — presheaves of `Λ`-modules on the small étale site
  admit an exact sheafification at the universe `max (u + 1) v`.
* `AlgebraicGeometry.moduleExtensionByZero_preservesFiniteLimits` — **Tag 03S5 for sheaves of
  modules on the sites of Tag 021B**: extension by zero preserves finite limits.

## Implementation notes

Sheafification is proved here rather than assumed, so that the exactness statement carries no
hypothesis: `AlgebraicGeometry.moduleExtensionByZero` already needs weak sheafification to be
defined, and the stronger form costs nothing, the small étale site being essentially small at
the coefficient universe and the forgetful functor of `Λ`-modules preserving filtered colimits.

The conclusion is a global instance, which it can be because
`AlgebraicGeometry.moduleExtensionByZero` leaves no universe free: the coefficient universe
`max (u + 1) v` is determined by the explicit argument `Λ : Type v`, so matching a goal against
it leaves the universe unifier nothing to solve. That is what distinguishes it from
`AlgebraicGeometry.moduleRestriction`, whose module universe is a parameter of its own.

## References

* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- The small étale site of a scheme of a big étale site has equalizers: it has a terminal object
and fibre products, hence binary products, and equalizers are built from those. -/
public theorem hasEqualizers_smallEtale : HasEqualizers (SmallEtale B X hX) :=
  have : HasBinaryProducts (SmallEtale B X hX) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  hasEqualizers_of_hasPullbacks_and_binary_products

variable (U : SmallEtale B X hX)

/-- Composition with the structure morphism of `U` preserves equalizers of small étale sites:
under the identification of the small étale site of `U` with the slice of that of `X` over `U` it
is the forgetful functor of the slice, which preserves connected limits. -/
public theorem preservesEqualizers_smallEtalePostcompose :
    PreservesLimitsOfShape WalkingParallelPair (smallEtalePostcompose B X hX U) := by
  rw [← smallEtaleEquivalenceOver_restriction B X hX U]
  infer_instance

variable (Λ : Type v) [Ring Λ]

/-- Presheaves of `Λ`-modules on the small étale site of a scheme of a big étale site admit an
exact sheafification at the universe `max (u + 1) v`: that site is essentially small there, and
the forgetful functor of `ModuleCat Λ` preserves filtered colimits.

This is the strengthening of `AlgebraicGeometry.moduleSheaf_hasWeakSheafify` whose proof already
passed through it. -/
public theorem moduleSheaf_hasSheafify :
    HasSheafify (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ) :=
  have : PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) v} Λ)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat) (forget AddCommGrpCat)
  have : EssentiallySmall.{max (u + 1) v} (SmallEtale B X hX) := inferInstance
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) v} _ _

/-- **Stacks 03S5 for sheaves of modules, on the sites of Tag 021B.** Extension by zero of
sheaves of `Λ`-modules along an object `U` of the small étale site of `X` preserves finite
limits. Together with the finite colimits it preserves as a left adjoint, extension by zero is
exact.

The small étale site of `U` has fibre products and equalizers, and composition with `U ⟶ X`
preserves both, so Tag 04BH for module coefficients applies. -/
@[stacks 03S5 "left exactness of j_! for sheaves of modules on the small etale sites of Tag 021B"]
public instance moduleExtensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits (moduleExtensionByZero B X hX U Λ) := by
  have := hasEqualizers_smallEtale B U.obj.left.1 U.obj.left.property
  have := preservesEqualizers_smallEtalePostcompose B X hX U
  have := moduleSheaf_hasSheafify.{u, v} B X hX Λ
  change PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
    (smallEtalePostcompose B X hX U) (ModuleCat.{max (u + 1) v} Λ)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX))
  exact Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits_module
    (smallEtalePostcompose B X hX U) Λ
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

end AlgebraicGeometry

end
