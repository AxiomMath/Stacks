module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineColimitPresentations

/-!
# Colimits of quasi-coherent modules from the span condition alone

The colimit clause of Stacks 06WN(1) is stated in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.ColimitsClosure` with two
module-theoretic hypotheses on the affine slice sites: that a quasi-coherent module there is
locally spanned by its sections over the affine object, and that global presentations there are
closed under small colimits.  The second is a theorem,
`AlgebraicGeometry.FibredSite.hasAffineColimitPresentations`, so the clause holds with the span
condition as its only hypothesis.  This file records the resulting statements.

The restatements are here rather than in `ColimitsClosure` because
`AlgebraicGeometry.FibredSite.hasAffineColimitPresentations` is proved downstream of it: its
proof uses the surjectivity of a presenting morphism on the sections over an affine object,
which rests in turn on the sheaf condition for the presheaf cokernel of a presentation, and that
chain imports `ColimitsClosure`.  Supplying the argument where the clause is stated would be a
cycle, so the hypothesis-free forms are stated where the discharge is available.

## Main results

* `AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules_of_span`: quasi-coherent modules
  on a category fibred in groupoids over the big fppf site have all small colimits, given the span
  condition on the affine slice sites.
* `AlgebraicGeometry.FibredSite.inclusion_preservesColimits_of_span`: those colimits are computed
  in the ambient category of module sheaves for the associated fppf topology.
* `AlgebraicGeometry.FibredSite.isClosedUnderColimitsOfShape_isQuasicoherentOnSite_of_span` and
  `AlgebraicGeometry.FibredSite.hasColimitsOfShape_quasicoherentModules_of_span`: the
  shape-by-shape forms.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) [EssentiallySmall.{u} 𝒳]

/-- **Quasi-coherence is closed under colimits of a given shape**, given the span condition on
the affine slice sites.  The closure hypothesis on global presentations is discharged by
`AlgebraicGeometry.FibredSite.hasAffineColimitPresentations`. -/
theorem isClosedUnderColimitsOfShape_isQuasicoherentOnSite_of_span (K : Type u) [Category.{u} K]
    (hspan : IsAffineLocallySpanned B S hS p hp) :
    (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderColimitsOfShape K :=
  isClosedUnderColimitsOfShape_isQuasicoherentOnSite' B S hS p hp K hspan
    (hasAffineColimitPresentations B S hS p hp)

/-- **Quasi-coherent modules have colimits of a given shape**, given the span condition on the
affine slice sites. -/
theorem hasColimitsOfShape_quasicoherentModules_of_span (K : Type u) [Category.{u} K]
    (hspan : IsAffineLocallySpanned B S hS p hp) :
    HasColimitsOfShape K (quasicoherentModules.{u, v, w, u} B S hS p hp) :=
  hasColimitsOfShape_quasicoherentModules' B S hS p hp K hspan
    (hasAffineColimitPresentations B S hS p hp)

/-- **The inclusion of the quasi-coherent modules preserves colimits of a given shape**, given
the span condition on the affine slice sites. -/
theorem preservesColimitsOfShape_quasicoherentInclusion_of_span (K : Type u) [Category.{u} K]
    (hspan : IsAffineLocallySpanned B S hS p hp) :
    PreservesColimitsOfShape K
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  preservesColimitsOfShape_quasicoherentInclusion' B S hS p hp K hspan
    (hasAffineColimitPresentations B S hS p hp)

/-- **Quasi-coherent modules on a category fibred in groupoids have all small colimits**, given
the span condition on the affine slice sites.  This is the existence half of the colimits clause
of Stacks 06WN(1) with its second hypothesis discharged. -/
theorem hasColimits_quasicoherentModules_of_span
    (hspan : IsAffineLocallySpanned B S hS p hp) :
    HasColimitsOfSize.{u, u} (quasicoherentModules.{u, v, w, u} B S hS p hp) :=
  hasColimits_quasicoherentModules B S hS p hp hspan
    (hasAffineColimitPresentations B S hS p hp)

/-- **Colimits of quasi-coherent modules are fppf-module colimits**, given the span condition on
the affine slice sites.  This is the comparison half of the colimits clause of Stacks 06WN(1)
with its second hypothesis discharged: the inclusion of the quasi-coherent modules into all
module sheaves for the associated fppf topology preserves all small colimits. -/
theorem inclusion_preservesColimits_of_span
    (hspan : IsAffineLocallySpanned B S hS p hp) :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  inclusion_preservesColimits B S hS p hp hspan
    (hasAffineColimitPresentations B S hS p hp)

end AlgebraicGeometry.FibredSite

end
