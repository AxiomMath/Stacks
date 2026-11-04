module

public import StacksFrontier.AlgebraicGeometry.Blowup.PerfectHomomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackSingleTorVanishing

/-!
# `Lf^*(ℳ[0]) ≅ (f^*ℳ)[0]` under Tor vanishing at the stalks

Let `f : X ⟶ Y` be a morphism of ringed spaces and `ℳ` a sheaf of `𝒪_Y`-modules such that at
every point `x` of `X` the positive Tor modules `Tor_n^{𝒪_{Y,f(x)}}(𝒪_{X,x}, ℳ_{f(x)})` vanish.
Then the canonical comparison `Lf^*(ℳ[0]) ⟶ (f^*ℳ)[0]` is an isomorphism: the derived pullback
of a module placed in degree zero again sits in degree zero, and is the ordinary pullback.

This is step 4 of the proof of [Stacks, Tag 08IB], at the shape the tag's assembly uses it, and
with the geometric Tor hypothesis of that tag replaced by the stalkwise vanishing it supplies.

## Main results

* `Stacks.Cohomology.PullbackSingleTor.isIso_derivedToOrdinaryPullbackSingle_of_stalkTorVanishing`
  — the comparison `Lf^*(ℳ[0]) ⟶ (f^*ℳ)[0]` of
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` is invertible.
* `Stacks.Cohomology.PullbackSingleTor.derivedPullbackSingleIso` — the resulting isomorphism
  `Lf^*(ℳ[0]) ≅ (f^*ℳ)[0]`.
* `Stacks.Cohomology.PullbackSingleTor.isIso_derivedToOrdinaryPullbackSingle_pushforward_unit`
  and `Stacks.Cohomology.PullbackSingleTor.derivedPullbackPushforwardUnitIso` — the same two at
  the sheaf `ℳ = g_*𝒪_{S'}` of [Stacks, Tag 08IB], for a morphism of schemes `g : S' ⟶ S`.

## Implementation notes

`AlgebraicGeometry.isIso_derivedToOrdinaryPullbackSingle` reduces the invertibility of the
four-factor comparison to the invertibility of its one nontrivial factor, the derived-pullback
comparison of [Stacks, Tag 06YJ] at the single complex on `ℳ`, and that is the theorem
`isIso_derivedPullbackComparison_app_single_of_stalkTorVanishing` in the namespace
`Stacks.Cohomology.PullbackSingleTor`. No other input is used, and the Tor hypothesis is spent
entirely inside the latter.

The model of the derived categories is `CategoryTheory.HasDerivedCategory.standard`, which is
what `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` and the
locality statement `Stacks.Cohomology.isIso_of_isIso_derivedPullback_ofRestrict` are pinned at.
The invertibility of the comparison it rests on carries free model binders, so nothing is lost
by the pin here.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace Stacks.Cohomology.PullbackSingleTor

attribute [local instance] HasDerivedCategory.standard

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **`Lf^*(ℳ[0]) ⟶ (f^*ℳ)[0]` is invertible under Tor vanishing at the stalks.**

The comparison is a composite of four maps, three of which are components of natural
isomorphisms; `AlgebraicGeometry.isIso_derivedToOrdinaryPullbackSingle` reduces its
invertibility to the invertibility of the fourth, the derived-pullback comparison of
[Stacks, Tag 06YJ] at the single complex on `ℳ`, which is
`isIso_derivedPullbackComparison_app_single_of_stalkTorVanishing`. -/
theorem isIso_derivedToOrdinaryPullbackSingle_of_stalkTorVanishing
    {ℳ : SheafOfModules.{u} (structureSheafRing Y)} (hTor : StalkTorVanishing f ℳ) :
    IsIso (derivedToOrdinaryPullbackSingle f ℳ 0) :=
  AlgebraicGeometry.isIso_derivedToOrdinaryPullbackSingle f ℳ 0
    (isIso_derivedPullbackComparison_app_single_of_stalkTorVanishing f hTor)

/-- **`Lf^*(ℳ[0]) ≅ (f^*ℳ)[0]`**: the comparison
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle`, made an
isomorphism by `isIso_derivedToOrdinaryPullbackSingle_of_stalkTorVanishing`. -/
def derivedPullbackSingleIso
    {ℳ : SheafOfModules.{u} (structureSheafRing Y)} (hTor : StalkTorVanishing f ℳ) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj ℳ) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
        ((modulePullback f).obj ℳ) :=
  haveI := isIso_derivedToOrdinaryPullbackSingle_of_stalkTorVanishing f hTor
  asIso (derivedToOrdinaryPullbackSingle f ℳ 0)

/-! ### The pushed-forward structure sheaf of [Stacks, Tag 08IB] -/

section Pushforward

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

/-- **Step 4 of the proof of [Stacks, Tag 08IB]:
`Lf^*(g_*𝒪_{S'}) ⟶ (f^*(g_*𝒪_{S'}))[0]` is invertible.**

The Tor hypothesis is the stalkwise vanishing of
`Stacks.Cohomology.PullbackSingleTor.StalkTorVanishing` at the sheaf `g_*𝒪_{S'}`, which is what
Tor independence of `X` and `S'` over `S` supplies when `g` is affine. Neither the square nor
quasi-compactness of `f` enters: the statement is about `f` and `g_*𝒪_{S'}` alone. -/
theorem isIso_derivedToOrdinaryPullbackSingle_pushforward_unit
    (hTor : StalkTorVanishing f.toLRSHom.toShHom
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit S'.ringCatSheaf))) :
    IsIso (derivedToOrdinaryPullbackSingle f.toLRSHom.toShHom
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit S'.ringCatSheaf)) 0) :=
  isIso_derivedToOrdinaryPullbackSingle_of_stalkTorVanishing f.toLRSHom.toShHom hTor

/-- **`Lf^*(g_*𝒪_{S'}) ≅ (f^*(g_*𝒪_{S'}))[0]`**, step 4 of the proof of [Stacks, Tag 08IB] as
an isomorphism. -/
def derivedPullbackPushforwardUnitIso
    (hTor : StalkTorVanishing f.toLRSHom.toShHom
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit S'.ringCatSheaf))) :
    (derivedPullback f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) 0).obj
          ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit S'.ringCatSheaf))) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
        ((modulePullback f.toLRSHom.toShHom).obj
          ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit S'.ringCatSheaf))) :=
  derivedPullbackSingleIso f.toLRSHom.toShHom hTor

end Pushforward

end Stacks.Cohomology.PullbackSingleTor

end
