module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeWeakSerre
public import StacksFrontier.CategoryTheory.ObjectProperty.KernelsInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackOfModules

/-!
# Exactness of the restriction to a small étale site (Stacks 06WJ)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `x` be an object of `𝒳`.
**Stacks 06WJ** restricts a presheaf of `𝒪_𝒳`-modules to the small étale site of the scheme `U`
below `x`; the functor carrying out the restriction is
`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFunctor`. This file records that it is exact.

The restriction is *computed on sections*: by construction it is restriction of the underlying
abelian presheaf along a functor of sites, followed by a transport of the scalars along the
identification `AlgebraicGeometry.Stack.localStructurePresheafIso` of the two structure sheaves,
and neither step changes the underlying abelian groups. Limits of presheaves of modules are
computed on sections, so no flatness enters: the restriction is left exact for the same reason
that it preserves colimits, and nothing about the comparison map of Stacks 0761 — where
flatness of the morphism of schemes does appear — is used.

## Main results

* `PresheafOfModules.preservesFiniteLimits_restrictScalars`: transport of the scalars along a
  morphism of presheaves of rings is left exact.
* `AlgebraicGeometry.Stack.additive_restrictModuleToSmallEtaleFunctor`,
  `AlgebraicGeometry.Stack.preservesFiniteLimits_restrictModuleToSmallEtaleFunctor` and
  `AlgebraicGeometry.Stack.preservesFiniteColimits_restrictModuleToSmallEtaleFunctor`: the
  restriction of Stacks 06WJ is additive, left exact and right exact, at every universe for the
  sections of the module. These are declared in
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeWeakSerre`, imported here.

## Implementation notes

Left exactness holds at an arbitrary universe `m` for the sections of the module: restriction of
scalars of modules over a ring is left exact with no constraint relating the universe of the
module to that of the ring, being a right adjoint to extension of scalars.

Exactness is what transports a closure property of objects across the restriction: with
`CategoryTheory.ObjectProperty.IsClosedUnderKernels.inverseImage` and its dual, a property of
presheaves of modules on the small étale site of `U` closed under kernels — quasi-coherence, for
instance — pulls back along the restriction to a property closed under kernels, and likewise for
cokernels. The additivity instance is what lets those fire: they ask for a functor preserving
zero morphisms.

Neither half of the restriction preserves finite limits for a reason special to the étale site.
The two general statements are therefore kept separate from the statement about Stacks 06WJ: the
first factor is
`Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.pushforward₀_preservesFiniteLimits`,
which is already available, and the second is proved here in the same style, through
`PresheafOfModules.evaluationJointlyReflectsLimits`.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w m r

namespace PresheafOfModules

variable {C : Type*} [Category* C] {R R' : Cᵒᵖ ⥤ RingCat.{r}} (α : R ⟶ R')

/-- **Transport of the scalars of presheaves of modules is left exact.** A cone of presheaves of
modules is limit as soon as it is limit on sections over every object, and on sections the
transport is the restriction of scalars of modules over a ring, which is a right adjoint to
extension of scalars and hence preserves limits.

No inequality between the universe of the sections and the universe of the rings is needed, in
contrast with `PresheafOfModules.preservesColimitsOfShape_restrictScalars_of_ringUniverse`:
extension of scalars leaves the universe of the module where it is. -/
noncomputable instance preservesFiniteLimits_restrictScalars :
    PreservesFiniteLimits (restrictScalars.{m} α) where
  preservesFiniteLimits _ _ _ :=
    ⟨fun {_} => ⟨fun _ {hc} => ⟨evaluationJointlyReflectsLimits _ _ fun X =>
      isLimitOfPreserves (ModuleCat.restrictScalars (α.app X).hom)
        (isLimitOfPreserves (evaluation R' X) hc)⟩⟩⟩

end PresheafOfModules

end
