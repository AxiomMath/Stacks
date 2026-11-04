module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Colimits

/-!
# Colimits of quasi-coherent modules at a large module universe

The colimits clause of Stacks 06WN needs two inputs: the ambient category of module sheaves on
the associated fppf site has the colimits in question, and quasi-coherence is closed under them.
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimits` supplies the
first input for a category fibred in groupoids `𝒳` that is *essentially small* over the universe
of the schemes, and reduces the clause to the second. This file supplies the same first input
with **no smallness hypothesis on `𝒳` at all**, by keeping the universe of module sections free
instead of tying it to the universe of the schemes.

## Main results

* `AlgebraicGeometry.FibredSite.hasColimits_sheafOfModules_largeModuleUniverse`: module sheaves
  on the associated fppf site have colimits at section universe `max u v w m`, for an arbitrary
  `𝒳 : Type v` with `Category.{w} 𝒳`.
* `AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules_largeModuleUniverse`:
  quasi-coherent modules have all colimits at that section universe, given that quasi-coherence
  is closed under them.
* `AlgebraicGeometry.FibredSite.preservesColimits_quasicoherentInclusion`: and the inclusion
  into all fppf module sheaves preserves them, under the same hypothesis.

## Implementation notes

The ambient colimits come from sheafification of `AddCommGrpCat`-valued presheaves on the
associated fppf site, which `CategoryTheory.hasSheafifyEssentiallySmallSite` supplies at any
universe containing an essentially small model of that site. At section universe `max u v w m`
such a model exists for any `𝒳 : Type v` with `Category.{w} 𝒳`, so `EssentiallySmall` is
inferred rather than assumed. At a section universe not containing `max v w` — for instance the
`u` of `AlgebraicGeometry.FibredSite.hasColimits_sheafOfModules`, where essential smallness of
`𝒳` is a hypothesis — it does not. This is the same device, and for the same reason, as the one
used for locally quasi-coherent modules in
`StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasicoherent`.

Because the hom universe of `AlgebraicGeometry.FibredSite.quasicoherentModules.{u, v, w, m}` is
`max v w m`, raising the section universe to `max u v w m` makes
`CategoryTheory.Limits.HasColimits` here mean colimits of every shape `K : Type (max u v w m)`
with `Category.{max u v w m} K`, which is why the closure hypothesis is stated for all such
shapes at once rather than one shape at a time.

The closure hypothesis is the remaining mathematical content, and it is not supplied here.
Nothing below asserts any clause of Stacks 06WN, and nothing below carries a `@[stacks]`
attribute: Stacks 06WN(1) asserts the existence of the colimits outright, whereas these results
are conditional on closure, and they fix the section universe where the source leaves it
arbitrary. Closure under arbitrary colimits subsumes the cokernel case, whose two non-formal
hypotheses are recorded in
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels` as the content of Stacks
0GNB(3), routed by the source through Stacks 03DW and 03DX.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- Module sheaves over the structure sheaf of the associated fppf site of a category fibred in
groupoids have all colimits at section universe `max u v w m`. Unlike
`AlgebraicGeometry.FibredSite.hasColimits_sheafOfModules_ringStructureSheafCore`, this assumes
no smallness of `𝒳`: at this section universe an essentially small model of the site exists for
any `𝒳`. -/
public theorem hasColimits_sheafOfModules_largeModuleUniverse :
    HasColimitsOfSize.{max u v w m, max u v w m}
      (SheafOfModules.{max u v w m} (ringStructureSheafCore B S hS p hp .fppf)) := by
  have : EssentiallySmall.{max u v w m} 𝒳 := inferInstance
  have : HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf)
      AddCommGrpCat.{max u v w m} := hasSheafifyEssentiallySmallSite _ _
  have : (BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective
      AddCommGrpCat.{max u v w m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  infer_instance

/-- Quasi-coherent modules on the associated fppf site of a category fibred in groupoids have
all colimits, provided quasi-coherence is closed under them. No smallness of `𝒳` is assumed.
The hypothesis is the remaining mathematical content of Stacks 06WN(1), which this does not
assert. -/
public theorem hasColimits_quasicoherentModules_largeModuleUniverse
    (hclosed : ∀ (K : Type (max u v w m)) [Category.{max u v w m} K],
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, max u v w m}
        (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderColimitsOfShape K) :
    HasColimits (quasicoherentModules.{u, v, w, max u v w m} B S hS p hp) := by
  have := hasColimits_sheafOfModules_largeModuleUniverse.{u, v, w, m} B S hS p hp
  constructor
  intro K _
  have := hclosed K
  infer_instance

/-- The inclusion of quasi-coherent modules into all fppf module sheaves preserves colimits,
provided quasi-coherence is closed under them. This is the agreement of colimits asserted by
Stacks 06WN(1) for the fppf topology, with its mathematical half left as the hypothesis and no
smallness of `𝒳` assumed. -/
public theorem preservesColimits_quasicoherentInclusion
    (hclosed : ∀ (K : Type (max u v w m)) [Category.{max u v w m} K],
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, max u v w m}
        (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderColimitsOfShape K) :
    PreservesColimits
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, max u v w m}
        (ringStructureSheafCore B S hS p hp .fppf)).ι := by
  have := hasColimits_sheafOfModules_largeModuleUniverse.{u, v, w, m} B S hS p hp
  have : CreatesColimitsOfSize.{max u v w m, max u v w m}
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, max u v w m}
        (ringStructureSheafCore B S hS p hp .fppf)).ι := by
    constructor
    intro K _
    have := hclosed K
    infer_instance
  exact preservesColimits_of_createsColimits_and_hasColimits _

end AlgebraicGeometry.FibredSite

end
