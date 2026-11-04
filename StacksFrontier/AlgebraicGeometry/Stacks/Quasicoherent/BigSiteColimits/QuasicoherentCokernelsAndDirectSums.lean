module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSectionBaseChangeExit

/-!
# Cokernels and arbitrary direct sums of quasi-coherent modules on a fibred site

Let `𝒳` be a category fibred in groupoids over the big fppf category of schemes over `S`.  On
the fppf site associated with `𝒳` the quasi-coherent modules are closed under colimits of every
small shape, under cokernels and under arbitrary direct sums, with nothing assumed beyond the
standing essential smallness of `𝒳`.

The two conditions on the affine slice sites that the colimit clause of Stacks 06WN(1) is
assembled from in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.ColimitsClosure` are both
theorems of this directory: the span condition is
`AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_isQuasicoherentOnSite` and the closure
condition on global presentations is
`AlgebraicGeometry.FibredSite.hasAffineColimitPresentations`.  Composing them gives the
shape-indexed closure property outright, and a cokernel and a direct sum are colimits of
particular shapes.

## Main results

* `AlgebraicGeometry.FibredSite.hasGlobalPresentation_over_of_isQuasicoherentOnSite`: **a
  quasi-coherent module is globally presented on the slice site at an affine object**, with
  nothing assumed.  This is the statement of Stacks 03DX for the affine slices of the fppf site
  associated with `𝒳`.
* `AlgebraicGeometry.FibredSite.isClosedUnderColimitsOfShape_isQuasicoherentOnSite`:
  **quasi-coherence is closed under colimits of every small shape**, with nothing assumed.
* `AlgebraicGeometry.FibredSite.isClosedUnderCokernels_isQuasicoherentOnSite`: the cokernel of a
  morphism of quasi-coherent modules is quasi-coherent.
* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_coprod`: an arbitrary direct sum of
  quasi-coherent modules is quasi-coherent.

## Implementation notes

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, Stacks 03DL(6), and a global
presentation is `SheafOfModules.HasGlobalPresentation`, Stacks 03DE(6); nothing is restated.

`CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape` is stated for a shape in the
universe of the modules, while a cokernel is a colimit over
`CategoryTheory.Limits.WalkingParallelPair`, which lives in `Type`.  The two are related by
`CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence` along
`CategoryTheory.AsSmall.equiv`, so the cokernel clause needs no separate argument.  A direct sum
indexed by `ι : Type u` is a colimit over `CategoryTheory.Discrete ι`, whose morphisms already
lie in `Type u`, so that clause is the main theorem read at one shape.

## What this is not

This is the fppf site associated with a category fibred in groupoids, not the small étale site
of an algebraic space, so none of these statements is a clause of Stacks 03M1 and no
`@[stacks 03M1]` tag is carried.  The corresponding clauses on the small étale site of an
algebraic space rest on Stacks 03DX *there*, which is
`AlgebraicGeometry.Space.HasAffineSlicePresentations` and is a hypothesis, not a theorem: the
faithfully-flat-descent material that
`AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_isQuasicoherentOnSite` rests on is
written throughout this directory for the slices of `AlgebraicGeometry.BigFppfOver` and has no
small-étale counterpart.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **Stacks 03DX for the affine slices of the fppf site associated with a category fibred in
groupoids.**  A quasi-coherent module on that site has a global presentation after restriction
to the slice site at an affine object, with nothing assumed.

This is `AlgebraicGeometry.FibredSite.hasGlobalPresentation_over_of_isLocallySpannedBySections`
with its span hypothesis discharged by
`AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_isQuasicoherentOnSite`. -/
theorem hasGlobalPresentation_over_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) (i : AffineObjects B S hS p) :
    (M.over (affineObj B S hS p i)).HasGlobalPresentation :=
  hasGlobalPresentation_over_of_isLocallySpannedBySections B S hS p hp
    (isAffineLocallySpanned_of_isQuasicoherentOnSite B S hS p hp) M hM i

variable [EssentiallySmall.{u} 𝒳]

/-- **Quasi-coherence of fppf module sheaves on a category fibred in groupoids is closed under
colimits of every small shape**, with nothing assumed.  This is the closure half of the colimit
clause of Stacks 06WN(1): both hypotheses of
`AlgebraicGeometry.FibredSite.isClosedUnderColimitsOfShape_isQuasicoherentOnSite'` are theorems
of this directory. -/
theorem isClosedUnderColimitsOfShape_isQuasicoherentOnSite (K : Type u) [Category.{u} K] :
    (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderColimitsOfShape K :=
  isClosedUnderColimitsOfShape_isQuasicoherentOnSite_of_span B S hS p hp K
    (isAffineLocallySpanned_of_isQuasicoherentOnSite B S hS p hp)

/-- Quasi-coherence of fppf module sheaves is closed under colimits over
`CategoryTheory.Limits.WalkingParallelPair`, the shape of a cokernel.  The shape is transported
from `CategoryTheory.AsSmall.{u} WalkingParallelPair`, which lies in the universe of the
modules, along `CategoryTheory.AsSmall.equiv`. -/
theorem isClosedUnderColimitsOfShape_walkingParallelPair_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderColimitsOfShape
        WalkingParallelPair :=
  have := isClosedUnderColimitsOfShape_isQuasicoherentOnSite B S hS p hp
    (AsSmall.{u} WalkingParallelPair)
  ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence AsSmall.equiv.symm

/-- **The cokernel of a morphism of quasi-coherent fppf module sheaves on a category fibred in
groupoids is quasi-coherent**, with nothing assumed.  A cokernel is a colimit over
`CategoryTheory.Limits.WalkingParallelPair`.

This is the cokernel half of the clause of Stacks 06WN(1) about colimits; the corresponding
clause of Stacks 03M1 is about the small étale site of an algebraic space and is not this
statement. -/
theorem isClosedUnderCokernels_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderCokernels where
  cokernels_le := by
    have := isClosedUnderColimitsOfShape_walkingParallelPair_isQuasicoherentOnSite B S hS p hp
    rintro _ ⟨f, k, hk, hf⟩
    refine ObjectProperty.prop_of_isColimit _ (J := WalkingParallelPair) hk ?_
    rintro (_ | _)
    · exact hf.1
    · exact hf.2

/-- **An arbitrary direct sum of quasi-coherent fppf module sheaves on a category fibred in
groupoids is quasi-coherent**, with nothing assumed.  A direct sum indexed by `ι` is a colimit
over `CategoryTheory.Discrete ι`.

This is the direct-sum half of the clause of Stacks 06WN(1) about colimits; the corresponding
clause of Stacks 03M1 is about the small étale site of an algebraic space and is not this
statement. -/
theorem isQuasicoherentOnSite_coprod {ι : Type u}
    (F : ι → SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    [HasCoproduct F] (hF : ∀ i, (F i).IsQuasicoherentOnSite) :
    (∐ F).IsQuasicoherentOnSite :=
  have := isClosedUnderColimitsOfShape_isQuasicoherentOnSite B S hS p hp (Discrete ι)
  ObjectProperty.prop_colimit _ (Discrete.functor F) fun j ↦ hF j.as

end AlgebraicGeometry.FibredSite

end
