module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FibredTensorProduct

/-!
# Colimits of quasi-coherent modules on a category fibred in groupoids

Quasi-coherent modules on the associated fppf site of an essentially small category fibred in
groupoids over the big fppf category of schemes over `S` have all small colimits, and those
colimits are the colimits of all fppf module sheaves.  This file assembles that clause from the
material of the surrounding directory, leaving as its two hypotheses exactly the two
module-theoretic conditions on the slice site at an affine object which the reduction cannot
discharge formally:

* `AlgebraicGeometry.FibredSite.IsAffineLocallySpanned`: a quasi-coherent module on the slice
  site at an affine object, and the relations between its generators, are each spanned —
  locally, after restriction along the arrows of a covering sieve — by their sections over that
  affine object itself.
* `AlgebraicGeometry.FibredSite.HasAffineColimitPresentations`: global presentations on those
  slice sites are closed under colimits of small shape.

Everything between those and the conclusion is formal, and is what the directory supplies: the
first condition becomes a global presentation on the affine slice sites
(`AlgebraicGeometry.FibredSite.presentingCoverOfAffineOfIsLocallySpannedBySections`), the affine
objects cover the final object (`AlgebraicGeometry.FibredSite.coversTop_affineObj`), and a family
covering the final object on whose slices quasi-coherent modules are globally presented turns
closure of global presentations into closure of quasi-coherence
(`Stacks.SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite`); the ambient
category of all module sheaves has the colimits because the site is essentially small
(`AlgebraicGeometry.FibredSite.hasColimits_sheafOfModules_ringStructureSheafCore`), and the two
together are the clause.

## Main definitions

* `AlgebraicGeometry.FibredSite.IsAffineLocallySpanned` and
  `AlgebraicGeometry.FibredSite.HasAffineColimitPresentations`: the two conditions above, named
  so that the statements below are readable.

## Main results

* `AlgebraicGeometry.FibredSite.hasAffineColimitPresentations_of_isAffineLocallySpanned`: the
  second condition follows from the first together with quasi-coherence of the colimit, which is
  a local condition.
* `AlgebraicGeometry.FibredSite.presentingCoverOfAffine'`: the affine objects as a presenting
  cover, from the two conditions.
* `AlgebraicGeometry.FibredSite.isClosedUnderColimitsOfShape_isQuasicoherentOnSite'`:
  quasi-coherence is closed under colimits of a small shape.
* `AlgebraicGeometry.FibredSite.hasColimitsOfShape_quasicoherentModules'` and
  `AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules`: **quasi-coherent modules have
  all small colimits.**
* `AlgebraicGeometry.FibredSite.preservesColimitsOfShape_quasicoherentInclusion'` and
  `AlgebraicGeometry.FibredSite.inclusion_preservesColimits`: **those colimits are the colimits
  of all fppf module sheaves.**
* `AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules_of_smallSite'` and
  `AlgebraicGeometry.FibredSite.inclusion_preservesColimits_of_smallSite`: the same two
  statements for a fibred category whose objects already form a `Type u`, in the unqualified
  `CategoryTheory.Limits.HasColimits` and `CategoryTheory.Limits.PreservesColimits` forms.

## Implementation notes

The objects and morphisms of the fibred category are at free universes; only the two
sheafification conditions tie it to the universe of the module sections, through essential
smallness.

The shape of a colimit ranges over the categories `K : Type u` with `Category.{u} K`, which is
the size of colimit the ambient category of module sheaves is known to have on an essentially
small site; the two unprimed results therefore conclude
`CategoryTheory.Limits.HasColimitsOfSize` and
`CategoryTheory.Limits.PreservesColimitsOfSize` at that size rather than the `HasColimits` and
`PreservesColimits` abbreviations, whose shape universe is that of the morphisms of the category
of module sheaves.  When the objects of the fibred category themselves form a `Type u` those
morphisms lie in `Type u` as well, and the two `_of_smallSite` results are the unqualified
forms; one universe higher they are not, and
`AddCommGrpCat.not_hasColimitsOfSize_succ` shows the colimits such a statement would refer to
do not exist.

`AlgebraicGeometry.FibredSite.HasAffineColimitPresentations` quantifies over the shape, because
`Stacks.SheafOfModules.PresentingCover` is a structure attached to one shape while the
conclusion is about all of them.

The sheafification data on the associated site itself, as opposed to on its slices, is produced
inside the proofs from essential smallness, exactly as in
`AlgebraicGeometry.FibredSite.hasColimits_sheafOfModules`; it is not assumed.

`AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules_of_smallSite'` carries a prime
because `AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules_of_smallSite` is the
statement it delegates to, which takes the closure of quasi-coherence as a hypothesis instead
of the two conditions of this file.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **The span condition on the affine slice sites.**  On the slice site at an affine object of
`𝒳`, whose terminal object is that affine object itself, a quasi-coherent module and the
relations between any family of generators of it are each locally spanned by their sections over
the affine object.

This is the section-level form of the statement that a quasi-coherent module over an affine is
the module associated with a module over a ring. -/
def IsAffineLocallySpanned : Prop :=
  ∀ (i : AffineObjects B S hS p)
    (N : SheafOfModules.{u}
      ((ringStructureSheafCore B S hS p hp .fppf).over (affineObj B S hS p i))),
    N.IsQuasicoherentOnSite →
      N.IsLocallySpannedBySections (Over.mkIdTerminal (X := affineObj B S hS p i)) ∧
        N.HasLocallySpannedRelations (Over.mkIdTerminal (X := affineObj B S hS p i))

/-- **Global presentations on the affine slice sites are closed under small colimits.**  A
colimit of globally presented modules on the slice site at an affine object of `𝒳` is globally
presented. -/
def HasAffineColimitPresentations : Prop :=
  ∀ (K : Type u) [Category.{u} K] (i : AffineObjects B S hS p)
    (D : K ⥤ SheafOfModules.{u}
      ((ringStructureSheafCore B S hS p hp .fppf).over (affineObj B S hS p i)))
    (c : Cocone D), IsColimit c → (∀ k, (D.obj k).HasGlobalPresentation) →
      c.pt.HasGlobalPresentation

/-- **The closure condition follows from the span condition together with quasi-coherence of the
colimit.**  The span condition makes every quasi-coherent module on the slice site at an affine
object globally presented, so a colimit of globally presented modules there is globally presented
as soon as it is quasi-coherent — which is a local condition, and so strictly weaker than the
global presentation asked for.  This is the reduction that keeps the two hypotheses of this file
from being independent. -/
theorem hasAffineColimitPresentations_of_isAffineLocallySpanned
    (hspan : IsAffineLocallySpanned B S hS p hp)
    (hqc : ∀ (K : Type u) [Category.{u} K] (i : AffineObjects B S hS p)
      (D : K ⥤ SheafOfModules.{u}
        ((ringStructureSheafCore B S hS p hp .fppf).over (affineObj B S hS p i)))
      (c : Cocone D), IsColimit c → (∀ k, (D.obj k).HasGlobalPresentation) →
        c.pt.IsQuasicoherentOnSite) :
    HasAffineColimitPresentations B S hS p hp := by
  intro K _ i D c hc hD
  have h := hspan i c.pt (hqc K i D c hc hD)
  exact SheafOfModules.HasGlobalPresentation.of_isGeneratedByUnit
    (SheafOfModules.isGeneratedByUnit_of_isLocallySpannedBySections _ h.1)
    (SheafOfModules.hasGeneratedRelations_of_isLocallySpannedBySections _ _ h.2)

/-- **The affine objects as a presenting cover**, from the two module-theoretic conditions on the
affine slice sites. -/
def presentingCoverOfAffine' (K : Type u) [Category.{u} K]
    (hspan : IsAffineLocallySpanned B S hS p hp)
    (hcolim : HasAffineColimitPresentations B S hS p hp) :
    Stacks.SheafOfModules.PresentingCover
      (ringStructureSheafCore B S hS p hp .fppf) K :=
  presentingCoverOfAffineOfIsLocallySpannedBySections B S hS p hp K hspan
    fun i D c => hcolim K i D c

variable [EssentiallySmall.{u} 𝒳]

/-- **Quasi-coherence of fppf module sheaves is closed under colimits of a small shape.**  The
affine objects cover the final object and carry a presenting cover, so
`Stacks.SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite` applies. -/
theorem isClosedUnderColimitsOfShape_isQuasicoherentOnSite' (K : Type u) [Category.{u} K]
    (hspan : IsAffineLocallySpanned B S hS p hp)
    (hcolim : HasAffineColimitPresentations B S hS p hp) :
    (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderColimitsOfShape K :=
  have _ := hasWeakSheafify_associatedTopology B S hS p .fppf
  have _ := wEqualsLocallyBijective_associatedTopology B S hS p .fppf
  Stacks.SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite
    (presentingCoverOfAffine' B S hS p hp K hspan hcolim)

/-- **Quasi-coherent modules have colimits of a small shape.** -/
theorem hasColimitsOfShape_quasicoherentModules' (K : Type u) [Category.{u} K]
    (hspan : IsAffineLocallySpanned B S hS p hp)
    (hcolim : HasAffineColimitPresentations B S hS p hp) :
    HasColimitsOfShape K (quasicoherentModules.{u, v, w, u} B S hS p hp) :=
  hasColimitsOfShape_quasicoherentModules B S hS p hp K
    (isClosedUnderColimitsOfShape_isQuasicoherentOnSite' B S hS p hp K hspan hcolim)

/-- **The inclusion of quasi-coherent modules into all fppf module sheaves preserves colimits of
a small shape.** -/
theorem preservesColimitsOfShape_quasicoherentInclusion' (K : Type u) [Category.{u} K]
    (hspan : IsAffineLocallySpanned B S hS p hp)
    (hcolim : HasAffineColimitPresentations B S hS p hp) :
    PreservesColimitsOfShape K
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  preservesColimitsOfShape_quasicoherentInclusion B S hS p hp K
    (isClosedUnderColimitsOfShape_isQuasicoherentOnSite' B S hS p hp K hspan hcolim)

/-- **Quasi-coherent modules on a category fibred in groupoids have all small colimits.**  This
is the existence half of the colimits clause of Stacks 06WN(1). -/
theorem hasColimits_quasicoherentModules
    (hspan : IsAffineLocallySpanned B S hS p hp)
    (hcolim : HasAffineColimitPresentations B S hS p hp) :
    HasColimitsOfSize.{u, u} (quasicoherentModules.{u, v, w, u} B S hS p hp) :=
  ⟨fun K _ => hasColimitsOfShape_quasicoherentModules' B S hS p hp K hspan hcolim⟩

/-- **Colimits of quasi-coherent modules are fppf-module colimits.**  This is the comparison
half of the colimits clause of Stacks 06WN(1): the inclusion of the quasi-coherent modules into
all module sheaves for the associated fppf topology preserves all small colimits. -/
theorem inclusion_preservesColimits
    (hspan : IsAffineLocallySpanned B S hS p hp)
    (hcolim : HasAffineColimitPresentations B S hS p hp) :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  ⟨fun {K} _ => preservesColimitsOfShape_quasicoherentInclusion' B S hS p hp K hspan hcolim⟩

section SmallSite

variable {𝒴 : Type u} [Category.{u} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hq : q.IsFiberedInGroupoids)

/-- **Quasi-coherent modules on a category fibred in groupoids whose objects form a `Type u`
have all colimits.**  This is
`AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules` for a fibred category whose
objects already lie in the universe of the module sections, where the shapes of
`CategoryTheory.Limits.HasColimits` are exactly the shapes the ambient category of module
sheaves is known to have colimits of, so that the unqualified form is available. -/
theorem hasColimits_quasicoherentModules_of_smallSite'
    (hspan : IsAffineLocallySpanned B S hS q hq)
    (hcolim : HasAffineColimitPresentations B S hS q hq) :
    HasColimits (quasicoherentModules.{u, u, u, u} B S hS q hq) :=
  hasColimits_quasicoherentModules_of_smallSite B S hS q hq
    fun K _ => isClosedUnderColimitsOfShape_isQuasicoherentOnSite' B S hS q hq K hspan hcolim

/-- **Colimits of quasi-coherent modules on a category fibred in groupoids whose objects form a
`Type u` are the colimits of all fppf module sheaves.**  This is the comparison half of the
colimits clause of Stacks 06WN(1) in the unqualified
`CategoryTheory.Limits.PreservesColimits` form. -/
theorem inclusion_preservesColimits_of_smallSite
    (hspan : IsAffineLocallySpanned B S hS q hq)
    (hcolim : HasAffineColimitPresentations B S hS q hq) :
    PreservesColimits
      (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (ringStructureSheafCore B S hS q hq .fppf)).ι :=
  preservesColimits_quasicoherentInclusion_of_smallSite B S hS q hq
    fun K _ => isClosedUnderColimitsOfShape_isQuasicoherentOnSite' B S hS q hq K hspan hcolim

end SmallSite

end AlgebraicGeometry.FibredSite

end
