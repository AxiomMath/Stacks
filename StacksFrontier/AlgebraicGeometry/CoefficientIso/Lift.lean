module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CoveringResolution

/-!
# The universe enlargement of [Stacks, Tag 02FU] at equal universes

[Stacks, Tag 02FU] is proved in this repository for a ringed space `(X, R)` with four independent
universes — that of the space, that of the rings, that of the module sections and that of the
index type of the covering — and its Čech complex lives over the enlarged module universe
`max u v w t`, the enlargement being
  `Stacks.CechTotalComplex.CoveringResolution.moduleUniverseLift`, a `ULift` of every module of
sections.  [Stacks, Tag 01XL] is applied at a scheme, where all four universes coincide, and there
the enlargement is a `ULift.{u}` of a `Type u`, hence invertible.

This file supplies that inverse, and factors the degree-`p` coefficient functor of
[Stacks, Tag 02FU] through it.

## Main results

* `Stacks.Tag01XLCoefficientIso.infDirectImage`:
  `Stacks.CechTotalComplex.CoveringResolution.infPushforward` as a
  `SheafOfModules.pushforward` along the continuous functor
    `Stacks.CechTotalComplex.CoveringResolution.infFunctor` — i.e. with the
  `ULift` removed.
* `Stacks.Tag01XLCoefficientIso.infPushforwardFunctor_eq`: **the coefficient functor of
  [Stacks, Tag 02FU] is the universe enlargement followed by that pushforward**, as an equality of
  functors.  Both sides are `PresheafOfModules.pushforward` applied to the `ULift`ed sheaf, so
  there is nothing to prove.
* `Stacks.Tag01XLCoefficientIso.moduleUniverseLiftIso`:
  **`Stacks.CechTotalComplex.CoveringResolution.moduleUniverseLift` is the
  identity** once the module universe is at least that of the space, the rings and the index type.
* `Stacks.Tag01XLCoefficientIso.infPushforwardFunctorIso`: consequently the coefficient functor of
  [Stacks, Tag 02FU] is isomorphic to `infDirectImage`, with no `ULift`.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w t z

namespace Stacks.Tag01XLCoefficientIso

variable (X : TopCat.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})

/-! ### The direct image of a restriction, without the universe enlargement -/

/-- **`Stacks.CechTotalComplex.CoveringResolution.infRestriction` as a morphism of sheaves of
  rings.**  It is already a morphism
`R ⟶ (infFunctor X V).op ⋙ R` of presheaves of rings, and
  `Stacks.CechTotalComplex.CoveringResolution.infFunctor` is continuous,
so no condition has to be checked. -/
noncomputable def infSheafHom (V : Opens X) :
    R ⟶ ((Stacks.CechTotalComplex.CoveringResolution.infFunctor X V).sheafPushforwardContinuous
      RingCat.{v}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology X)).obj R :=
  ⟨Stacks.CechTotalComplex.CoveringResolution.infRestriction X R V⟩

/-- **The direct image of the restriction of a module sheaf to a fixed open set**, with no
universe enlargement: the pushforward of sheaves of modules along
  `Stacks.CechTotalComplex.CoveringResolution.infFunctor X V`
and `Stacks.CechTotalComplex.CoveringResolution.infRestriction X R V`. -/
noncomputable def infDirectImage (V : Opens X) :
    SheafOfModules.{z} R ⥤ SheafOfModules.{z} R :=
  SheafOfModules.pushforward.{z} (infSheafHom X R V)

/-- **The degree-`p` coefficient functor of [Stacks, Tag 02FU] is the universe enlargement
followed by `infDirectImage`.**  This is an equality, not merely an isomorphism:
`Stacks.CechTotalComplex.CoveringResolution.infPushforward` is `PresheafOfModules.pushforward
  (infRestriction X R V)` applied to
the enlarged sheaf, and that is exactly what the right-hand side computes. -/
theorem infPushforwardFunctor_eq (V : Opens X) :
    Stacks.CechTotalComplex.CoveringResolution.infPushforwardFunctor.{u, v, w, t} X R V =
      Stacks.CechTotalComplex.CoveringResolution.moduleUniverseLift.{u, v, w, t} X R ⋙
        infDirectImage.{u, v, max u v w t} X R V :=
  rfl

/-! ### The universe enlargement is invertible at equal universes -/

/-- **The `ULift` of [Stacks, Tag 02FU] is invertible** once the module universe already contains
those of the space, the rings and the index type: `ULift.moduleEquiv` on each open set, which is
linear for the scalars because the module structure of
  `Stacks.CechTotalComplex.CoveringResolution.uliftPresheaf` is the one
transported along it. -/
noncomputable def uliftSheafIso (F : SheafOfModules.{max u v w t} R) :
    Stacks.CechTotalComplex.CoveringResolution.uliftSheaf.{u, v, max u v w t, t} X R F ≅ F :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ (ULift.moduleEquiv
      (R := R.obj.obj V) (M := F.val.obj V)).toModuleIso) (fun {_ _} _ ↦ by
        ext x
        rfl))

/-- **`Stacks.CechTotalComplex.CoveringResolution.moduleUniverseLift` is the identity functor** at
  the universes in which
[Stacks, Tag 01XL] applies it, namely those with `max u v w t = w`. -/
noncomputable def moduleUniverseLiftIso :
    Stacks.CechTotalComplex.CoveringResolution.moduleUniverseLift.{u, v, max u v w t, t} X R ≅
      𝟭 (SheafOfModules.{max u v w t} R) :=
  NatIso.ofComponents (uliftSheafIso.{u, v, w, t} X R) (fun {_ _} _ ↦ by
    apply SheafOfModules.hom_ext
    ext V x
    rfl)

/-- **The coefficient functor of [Stacks, Tag 02FU] carries no universe enlargement** once the
module universe contains the other three: it is `infDirectImage`, the direct image of the
restriction to the open set. -/
noncomputable def infPushforwardFunctorIso (V : Opens X) :
    Stacks.CechTotalComplex.CoveringResolution.infPushforwardFunctor.{u, v, max u v w t, t} X R V ≅
      infDirectImage.{u, v, max u v w t} X R V :=
  eqToIso (infPushforwardFunctor_eq.{u, v, max u v w t, t} X R V) ≪≫
    Functor.isoWhiskerRight (moduleUniverseLiftIso.{u, v, w, t} X R)
      (infDirectImage.{u, v, max u v w t} X R V) ≪≫
    Functor.leftUnitor _

end Stacks.Tag01XLCoefficientIso

end
