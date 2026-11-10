module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPerfection.Descent
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatUntensoredBaseChangeCartesian
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# The derived direct image of a flat module along a proper morphism of finite presentation

Let `f : X ⟶ S` be a proper morphism of finite presentation and `ℱ` an `𝒪_X`-module of finite
presentation, flat over `S`. Then `Rf_*ℱ` is a perfect object of `D(𝒪_S)`. This is the
perfection half of [Stacks, Tag 0B91] (2), the Prop
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.PerfectDerivedPushforward`.

The proof is the source's, through [Stacks, Tag 0A1H]. Perfectness is local on `S`
([Stacks, Tag 08CR]) and derived direct image commutes with restriction to an open of `S`
([Stacks, Tag 08FE]), so `S` may be taken affine. Then `(f, ℱ)` is the base change of a proper
family `(f₀, ℱ₀)` of finite presentation, flat over a Noetherian `T`
(`AlgebraicGeometry.ProperFlatPerfection.exists_noetherianModel`); `R(f₀)_*ℱ₀` is perfect
(`AlgebraicGeometry.isPerfect_derivedPushforwardModules_single_of_isNoetherian`); its formation
commutes with the base change `S ⟶ T` (the base-change half of [Stacks, Tag 0B91] (2),
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.baseChangeDerivedPushforward`); and the
derived pullback of a perfect object is perfect ([Stacks, Tag 09UA]).

## Main results

All in the namespace `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic`.

* `isPerfect_derivedPushforwardModule_of_isAffine_of_baseChange`: the case of an affine base.
* `perfectDerivedPushforward_of_baseChange`: the perfection half of [Stacks, Tag 0B91] (2) from
  its base-change half.
* `perfectDerivedPushforward`: **the perfection half of [Stacks, Tag 0B91] (2)**, unconditionally.

## Implementation notes

The two reductions are `isPerfect_derivedPushforward_singleFunctor_of_isAffine_of_baseChange` and
`isPerfect_derivedPushforward_singleFunctor_of_baseChange` in
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatModuleDirectImage.lean`, stated there without
the abbreviation `derivedPushforwardModule`; this file restates them with it.

The reduction takes the base-change half `BaseChangeDerivedPushforward` as an explicit argument;
the unconditional statement supplies it with `baseChangeDerivedPushforward`.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

attribute [local instance 10000] HasDerivedCategory.standard

/-- Assuming `BaseChangeDerivedPushforward`: for `V` affine, `f : X ⟶ V` proper of finite
presentation and `ℱ` of finite presentation and flat over `V`, `Rf_*ℱ` is perfect. -/
theorem isPerfect_derivedPushforwardModule_of_isAffine_of_baseChange
    (hbc : BaseChangeDerivedPushforward.{u}) {X V : Scheme.{u}} [IsAffine V] (f : X ⟶ V)
    (hfp : FinitePresentation f) [IsProper f] (F : X.Modules) [F.IsFinitePresentation]
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := V.toRingedSpace)
      (derivedPushforwardModule f F) :=
  isPerfect_derivedPushforward_singleFunctor_of_isAffine_of_baseChange hbc f hfp F hF

/-- `BaseChangeDerivedPushforward` implies `PerfectDerivedPushforward`. -/
theorem perfectDerivedPushforward_of_baseChange (hbc : BaseChangeDerivedPushforward.{u}) :
    PerfectDerivedPushforward.{u} := by
  intro X S f hfp hprop F hFfp hFflat
  exact isPerfect_derivedPushforward_singleFunctor_of_baseChange hbc f hfp hprop F hFfp hFflat

/-- Let `f : X ⟶ S` be a proper morphism of finite presentation and `ℱ` an `𝒪_X`-module of
finite presentation, flat over `S`. Then `Rf_*ℱ` is a perfect object of `D(𝒪_S)`. -/
@[stacks 0B91 "clause (2), the perfection half: for f proper of finite presentation and a module \
of finite presentation flat over S, Rf_*F is a perfect object of D(O_S), over an arbitrary base. \
Proved by Noetherian approximation of (f, F), the Noetherian case, base change and stability of \
perfection under derived pullback; nothing is granted", sga "6 IV 3.3.2" "3.3.2.3, special case"]
theorem perfectDerivedPushforward : PerfectDerivedPushforward.{u} :=
  perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic
