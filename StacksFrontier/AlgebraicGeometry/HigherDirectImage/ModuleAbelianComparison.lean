module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModulePushforwardComparison

/-!
# Higher direct images of a module on a scheme and of its underlying abelian sheaf

Let `f : X ⟶ Y` be a morphism of schemes. A sheaf of `𝒪_X`-modules has higher direct images
computed in two ways: push forward in sheaves of modules and derive there, forgetting the module
structure only at the end, or forget to a sheaf of abelian groups on the small Zariski site of `X`
first and derive the direct image of abelian sheaves. This file records that the two agree,

`R^p f_*^mod (-) ⋙ forget ≅ forget ⋙ R^p f_*^ab (-)`,

for an arbitrary morphism of schemes and every `p`.

Nothing is proved here. `AlgebraicGeometry.Scheme.Modules.pushforward f` is by definition
`SheafOfModules.pushforward f.toRingCatSheafHom`, the direct image of sheaves of modules along
the continuous functor `Opens.map f.base` between the small Zariski sites of `Y` and `X`, so the
site-level comparison
`Stacks.Cohomology.SiteModulePushforward.rightDerivedPushforwardToSheafIso` applies on the nose.
This module is the instantiation, so that a consumer working with schemes does not have to
produce the site data.

## Main definitions

* `Stacks.AlgebraicGeometry.HigherDirectImage.rightDerivedPushforwardToSheafIso`: the comparison
  above, for a morphism of schemes.

## Implementation notes

The abelian direct image is spelled as the direct image of abelian sheaves along the continuous
functor `Opens.map f.base` between the Grothendieck topologies of open covers of `Y` and of `X`.
That is the same functor as the one appearing in
`Stacks.Cohomology.ModulePushforwardComparison.rightDerived_modulePushforward_forget_iso`, the
ringed-space form of the same comparison ([Stacks, Tag 01F1] part (2)); a morphism of schemes is
in particular a morphism of ringed spaces, but the module categories are spelled through
`AlgebraicGeometry.Scheme.Modules` rather than through `RingedSpace`, which is why the
instantiation is recorded separately.

No stacks attribute is attached: [Stacks, Tag 01F1] part (2) is stated for ringed spaces and is
already carried by the declaration just named, and [Stacks, Tag 0D6J] part (3), the site-level
statement, is about `Rf_*` of an unbounded complex rather than the `ℕ`-indexed `R^p f_*` of a
single module.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.HigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The higher direct images of a sheaf of modules on a scheme and of its underlying abelian
sheaf agree.** Deriving `Scheme.Modules.pushforward f` and then forgetting the module structure
is, naturally in the module, forgetting first and then deriving the direct image of abelian
sheaves along `Opens.map f.base`.

This is `Stacks.Cohomology.SiteModulePushforward.rightDerivedPushforwardToSheafIso` at the small
Zariski sites of `Y` and `X`, the continuous functor `Opens.map f.base` and the morphism of
structure sheaves `f.toRingCatSheafHom`. -/
def rightDerivedPushforwardToSheafIso (p : ℕ) :
    (Scheme.Modules.pushforward f).rightDerived p ⋙
        SheafOfModules.toSheaf.{u} Y.ringCatSheaf ≅
      SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙
        ((Opens.map f.base).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).rightDerived p :=
  Stacks.Cohomology.SiteModulePushforward.rightDerivedPushforwardToSheafIso
    (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier)
    (Opens.map f.base) X.ringCatSheaf Y.ringCatSheaf f.toRingCatSheafHom p

end Stacks.AlgebraicGeometry.HigherDirectImage

end
