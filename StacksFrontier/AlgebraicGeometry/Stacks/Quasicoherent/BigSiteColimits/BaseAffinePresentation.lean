module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.QuasicoherentCokernelsAndDirectSums
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence

/-!
# Global presentations at the affine objects of the big fppf site of a scheme

`AlgebraicGeometry.FibredSite.hasGlobalPresentation_over_of_isQuasicoherentOnSite` is the
affine presentation statement for the fppf site associated with a category fibred in groupoids
over `(Sch/S)_fppf`: a quasi-coherent module there has a *global* presentation after restriction
to the slice at an object lying over an affine scheme, with no covering and nothing assumed.
**The big fppf site of `S` itself is the case `𝒳 = (Sch/S)_fppf` of that**, through the identity
functor, which is fibred in groupoids; and this file performs the instantiation, which is not a
formality because the topology the identity functor inherits is only *propositionally* the
topology it was inherited from.

This is the local step the proof of [Stacks, Tag 03DX] (1) runs its descent argument on, not a
clause of it — 03DX asserts only that `𝓕 ↦ 𝓕^a` is an equivalence of categories — so nothing
here carries a `stacks` attribute.

## Main results

* `AlgebraicGeometry.BigFppfOver.hasGlobalPresentation_over_of_isQuasicoherentOnSite`: a
  quasi-coherent `𝒪`-module on the big fppf site of `S` has a global presentation on the slice
  at an object whose underlying scheme is affine.

## Implementation notes

The two sites differ by `CategoryTheory.Functor.inheritedTopology_id`, an equality of
Grothendieck topologies which is *not* definitional — it is proved by `le_antisymm` — while the
two structure sheaves have the same underlying presheaf on the nose,
`AlgebraicGeometry.FibredSite.ringStructureSheafCore_obj` at the identity functor being
`AlgebraicGeometry.FibredSite.baseRingStructureSheaf_obj`.  Everything in the statement —
`SheafOfModules`, `SheafOfModules.IsQuasicoherentOnSite`, `SheafOfModules.over` and
`SheafOfModules.HasGlobalPresentation` — depends on the topology, so the transport is performed
once, on the whole statement, by generalizing the topology and the coefficient sheaf and
substituting; that is `AlgebraicGeometry.BigFppfOver.AffinePresentationProperty` and the
`key` step of the proof below.

The localized fppf topology `AlgebraicGeometry.BigFppfOver.topology` and the `τ = fppf` member
of the five `AlgebraicGeometry.BigFppfOver.baseOverTopology` are the same by `rfl`, so the
statement is about the site the rest of the tree calls the big fppf site over `S`.

**Only `τ = fppf`.**  The source quantifies over `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`
and the other four are *not* instances of this: every statement the proof rests on —
`AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.FibredSite.hasGlobalPresentation_over_of_isLocallySpannedBySections` — is
stated at `AlgebraicGeometry.FibredSite.ringStructureSheafCore … .fppf`, and the reduction of a
coarser `τ` to fppf is not formal: `SheafOfModules.HasGlobalPresentation` is exactness in the
category of sheaves for the topology, so it is a different assertion at each `τ`, and a
`τ`-sheaf is not an fppf sheaf.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The affine presentation assertion for a ringed site structure on the big fppf category over
`S`: every quasi-coherent module has a global presentation on the slice at an object with affine
underlying scheme.

Both the topology and the coefficient sheaf are parameters because the statement has to be
transported along `CategoryTheory.Functor.inheritedTopology_id`, which is an equality of
topologies and not a definitional one. -/
public abbrev AffinePresentationProperty
    (J : GrothendieckTopology (BigFppfOver B S hS)) (R : Sheaf J RingCat.{u}) : Prop :=
  ∀ (M : SheafOfModules.{u} R), M.IsQuasicoherentOnSite →
    ∀ (T : BigFppfOver B S hS), IsAffine ((toScheme B S hS).obj T) →
      (M.over T).HasGlobalPresentation

/-- **A quasi-coherent module on the big fppf site of `S` is globally presented at an affine
object.**  A quasi-coherent `𝒪`-module on `(Sch/S)_fppf` — quasi-coherent in the sense of
[Stacks, Tag 03DL] (6), so with a presentation only locally on some covering — has a *global*
presentation on the slice at any object whose underlying scheme is affine, with nothing assumed.

This is `AlgebraicGeometry.FibredSite.hasGlobalPresentation_over_of_isQuasicoherentOnSite` at
the identity functor of `(Sch/S)_fppf`, which is fibred in groupoids by
`CategoryTheory.Functor.isFiberedInGroupoids_id`, transported along
`CategoryTheory.Functor.inheritedTopology_id`.

It carries no `stacks` attribute.  [Stacks, Tag 03DX] asserts two clauses and both are of the
form "`𝓕 ↦ 𝓕^a` is an equivalence of categories" — clause (1) onto `QCoh((Sch/S)_τ, 𝒪)` for the
five `τ`, clause (2) onto the small site for `τ ∈ {Zariski, étale}`.  A global presentation at an
affine object is no part of either statement; it is an **input**, the local step the source's
proof of clause (1) runs the descent argument on.  Clause (1) at every `τ` is registered on
`AlgebraicGeometry.BigFppfOver.isEquivalence_baseAssociatedModuleQcohOnSite'` and
`…baseAssociatedModuleEquivalenceOnSite'`, both in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity`
(lines 315 and 323). -/
public theorem hasGlobalPresentation_over_of_isQuasicoherentOnSite :
    AffinePresentationProperty B S hS (baseOverTopology B S hS .fppf)
      (FibredSite.baseRingStructureSheaf B S hS .fppf) := by
  have key : ∀ (J : GrothendieckTopology (BigFppfOver B S hS))
      (_ : BigFppfOver.associatedTopology B S hS (𝟭 (BigFppfOver B S hS)) .fppf = J)
      (R : Sheaf J RingCat.{u}),
      R.obj = (FibredSite.ringStructureSheafCore B S hS (𝟭 (BigFppfOver B S hS))
        Functor.isFiberedInGroupoids_id .fppf).obj →
      AffinePresentationProperty B S hS J R := by
    rintro J rfl R hR
    obtain rfl : R = FibredSite.ringStructureSheafCore B S hS (𝟭 (BigFppfOver B S hS))
        Functor.isFiberedInGroupoids_id .fppf :=
      ObjectProperty.FullSubcategory.ext hR
    intro M hM T hT
    exact FibredSite.hasGlobalPresentation_over_of_isQuasicoherentOnSite B S hS
      (𝟭 (BigFppfOver B S hS)) Functor.isFiberedInGroupoids_id M hM ⟨T, hT⟩
  exact key _ (Functor.inheritedTopology_id _) _ rfl

end AlgebraicGeometry.BigFppfOver

end
