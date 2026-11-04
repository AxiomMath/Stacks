module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCohomologyVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedModuleAdjunction

/-!
# Sheaves of modules on a chosen big site have enough injectives

Let `B` be a chosen big `τ`-site over a scheme `S`. The sheaves of `𝒪`-modules on `B`, with
sections in the universe `u` of the schemes, form a Grothendieck abelian category, hence have
enough injectives. This is what makes the right derived functors of a functor out of them, such
as the higher direct images, available with no hypothesis beyond the site.

## Main results

* `Stacks.Adequate.BigSite.isGrothendieckAbelian_sheafOfModules` and
  `Stacks.Adequate.BigSite.enoughInjectives_sheafOfModules` — the category of sheaves of
  `𝒪`-modules on the site is Grothendieck abelian and has enough injectives, [Stacks, Tag 01DU]
  on the site.

## Implementation notes

The objects of a chosen big site live one universe above its morphisms, so neither Mathlib's
instance for sheaves of modules on a small site nor the `UnivLE` form applies at the module
universe `u`. The site is essentially small at `u` (`Stacks.Adequate.BigSite.essentiallySmall_
category`), and `SheafOfModules.isGrothendieckAbelian_of_essentiallySmall` transports Mathlib's
instance along the equivalence with a small model. The two sheafification hypotheses it asks for
are `Stacks.Adequate.BigSite.hasSheafify_addCommGrpCat` and
`Stacks.Adequate.BigSite.wEqualsLocallyBijective_addCommGrpCat`.

## References

* [Stacks Project, Tag 01DU](https://stacks.math.columbia.edu/tag/01DU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-- **Sheaves of `𝒪`-modules on a chosen big site form a Grothendieck abelian category** at the
universe of the schemes of the site. -/
public instance BigSite.isGrothendieckAbelian_sheafOfModules (B : BigSite τ S) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} B.structureSheaf) :=
  have := B.essentiallySmall_category
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (R := B.structureSheaf)

/-- **Sheaves of `𝒪`-modules on a chosen big site have enough injectives.** This is
[Stacks, Tag 01DU] on the site. -/
public instance BigSite.enoughInjectives_sheafOfModules (B : BigSite τ S) :
    EnoughInjectives (SheafOfModules.{u} B.structureSheaf) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

end Stacks.Adequate

end
