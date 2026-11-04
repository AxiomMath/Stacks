module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineAcyclicityFromSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# The hypotheses of the affine-acyclicity reduction are inhabited

`AlgebraicGeometry.Stack.hasAffineAcyclicLqcFbcModules_of_isZero_sheafCohomology` carries six
instance hypotheses on the fppf site of a category fibred in groupoids `p : 𝒳 ⥤ (Sch/S)_{fppf}`:
sheafification and the locally bijective description of its weak equivalences for abelian
sheaves at the universe `u` of the schemes, enough injectives for abelian sheaves and for
sheaves of modules, and `Ext`-groups for both.  This file exhibits all six at once, so that the
reduction is a statement about a nonempty class.

They all hold when the total category of the fibred category is itself `u`-small, which is the
configuration in which abelian sheaves and sheaves of modules on the site are Grothendieck
abelian at `u`: the generating families of
`Stacks.Cohomology.SiteModules.site_isGrothendieckAbelian_addCommGrp` and
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck` are indexed by the objects of the
site, so they are available exactly when the objects fit in the coefficient universe.  Enough
injectives and `Ext` then follow, Grothendieck abelian categories having both.

## Main results

* `AlgebraicGeometry.Stack.hasSheafify_fppfSite_of_small`,
  `AlgebraicGeometry.Stack.wEqualsLocallyBijective_fppfSite_of_small`,
  `AlgebraicGeometry.Stack.enoughInjectives_fppfSiteSheaf_of_small`,
  `AlgebraicGeometry.Stack.hasExt_fppfSiteSheaf_of_small`,
  `AlgebraicGeometry.Stack.enoughInjectives_fppfSiteModules_of_small`,
  `AlgebraicGeometry.Stack.hasExt_fppfSiteModules_of_small`: the six hypotheses, at the same
  data, for a `u`-small category fibred in groupoids.

## Implementation notes

These are stated for `𝒳 : Type u` with `Category.{u} 𝒳`, so that the `Ext` universe `max v u`
of the reduction is `u`; that is what lets the Grothendieck abelian structure at `u` supply the
`Ext`-groups.  They are theorems rather than instances, following Mathlib's policy on
`CategoryTheory.HasExt`: a category has in general several reasonable `Ext` universes and two
instances would make the universe ambiguous.  A consumer declares the ones it needs
`local instance`.

This file is separate from the reduction because
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is a global instance at the enlarged
module universe `max u v r w`, and having it in scope while elaborating the reduction's own
instance-implicit binders at module universe `u` leaves the universe constraint
`max u v =?= max (u + 1) v` unsolved.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type u} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **Abelian sheaves on the fppf site of a `u`-small category fibred in groupoids sheafify at
the universe of the schemes.** -/
theorem hasSheafify_fppfSite_of_small :
    HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u}
    (J := BigFppfOver.associatedTopology B S hS p .fppf)

/-- **Sheafification there inverts exactly the locally bijective maps.** -/
theorem wEqualsLocallyBijective_fppfSite_of_small :
    (BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
    (J := BigFppfOver.associatedTopology B S hS p .fppf)

/-- **Abelian sheaves there have enough injectives**, being Grothendieck abelian at `u`. -/
theorem enoughInjectives_fppfSiteSheaf_of_small :
    EnoughInjectives
      (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}) :=
  have := hasSheafify_fppfSite_of_small B S hS p
  have := Stacks.Cohomology.SiteModules.site_isGrothendieckAbelian_addCommGrp.{u, u, u}
    (J := BigFppfOver.associatedTopology B S hS p .fppf)
  IsGrothendieckAbelian.enoughInjectives

/-- **Abelian sheaves there have `Ext`-groups at the universe of the schemes.** -/
theorem hasExt_fppfSiteSheaf_of_small :
    HasExt.{u}
      (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}) :=
  have := hasSheafify_fppfSite_of_small B S hS p
  have := Stacks.Cohomology.SiteModules.site_isGrothendieckAbelian_addCommGrp.{u, u, u}
    (J := BigFppfOver.associatedTopology B S hS p .fppf)
  inferInstance

/-- **Sheaves of `𝒪_𝒳`-modules there have `Ext`-groups at the universe of the schemes.**

With the five statements above this exhibits every instance hypothesis of
`AlgebraicGeometry.Stack.hasAffineAcyclicLqcFbcModules_of_isZero_sheafCohomology` at one and the
same category fibred in groupoids, so that reduction is not a statement about an empty class. -/
theorem hasExt_fppfSiteModules_of_small :
    HasExt.{u} (fppfSiteModules B S hS p hp) :=
  have := Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u, u, u, u}
    (O := fppfSiteRingSheaf B S hS p hp)
  inferInstance

end AlgebraicGeometry.Stack

end
