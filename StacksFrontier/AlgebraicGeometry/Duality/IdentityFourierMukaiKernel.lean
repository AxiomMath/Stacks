module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of the identity Fourier-Mukai kernel

Let `X` be a smooth proper scheme over a field `k` and let `K` be a perfect object of
`D(𝒪_{X ×_k X})`. If the Fourier-Mukai functor `Φ_K` of [Stacks, Tag 0FYQ] induces on
`D_perf(𝒪_X)` an endofunctor isomorphic to the identity, then

`K ≅ Δ_*𝒪_X`,

the derived direct image of the structure sheaf along the diagonal `Δ : X ⟶ X ×_k X`.  This is
[Stacks, Tag 0G0E], proved as `Stacks.Duality.nonempty_iso_diagonalFourierMukaiKernel` in
`StacksFrontier/AlgebraicGeometry/Duality/IdentityKernelStepThree.lean`; this file defines the
objects in its statement.

## Main definitions

* `Stacks.Duality.perfectDerivedObjects` — the perfect objects of `D(𝒪_X)` for a scheme `X`, the
  predicate `Stacks.Cohomology.PerfectComplexes.IsPerfect` of [Stacks, Tag 08CM] read on
  `X.toRingedSpace`, packaged as an `ObjectProperty`.
* `Stacks.Duality.diagonalFourierMukaiKernel` — `Δ_*𝒪_X`, the derived direct image along the
  diagonal of the structure sheaf placed in degree zero; the kernel of the identity functor.
* `Stacks.Duality.RepresentsIdentityOnPerfect` — `Φ_K` carries perfect objects to perfect objects
  and the induced endofunctor of `D_perf(𝒪_X)` is isomorphic to the identity.

## Implementation notes

*Which `IsPerfect`.*  The library states [Stacks, Tag 08CM] twice: as
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, in `StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/Defs.lean`, at independent
space and section universes, and as `AlgebraicGeometry.RingedSpace.IsPerfect`, in
`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/BasicProperties.lean`, at a single universe.  The first is used here, because
it is the one `AlgebraicGeometry.perfectDerived` of
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/TransformedDiagonal/Basic.lean` already reads
for a scheme, and this file's `perfectDerivedObjects` agrees with it.

*The model of the derived categories.*  `HasDerivedCategory.standard` is activated as a local
instance, as in `StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/Basic.lean`: the
exactness of `Φ_K`, and the derived pullback it is built from, are available only at that model.
`perfectDerivedObjects` performs the single crossing between the scheme spelling `X.Modules` of
the category of `𝒪_X`-modules and the ringed-space spelling that Tag 08CM is stated in, so no
other declaration in this file mentions both.

*Why the conclusion is `Nonempty`.*  The source says `K` "is isomorphic to" `Δ_*𝒪_X` and names
no isomorphism; `Nonempty (K ≅ _)` is that statement, and the isomorphism of functors in the
hypothesis is read the same way, as in Tag 0FYQ's `AlgebraicGeometry.IsFourierMukaiKernel`.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
* [Stacks Project, Tag 0FZP](https://stacks.math.columbia.edu/tag/0FZP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Duality

attribute [local instance] HasDerivedCategory.standard

/-- The perfect objects of `D(𝒪_X)` for a scheme `X`, as an object property: the predicate
`Stacks.Cohomology.PerfectComplexes.IsPerfect` of [Stacks, Tag 08CM], read on the ringed space
underlying `X`.  This is the only place where the scheme spelling `X.Modules` of the category of
`𝒪_X`-modules meets the ringed-space spelling that Tag 08CM is stated in. -/
def perfectDerivedObjects (X : Scheme.{u}) : ObjectProperty (DerivedCategory X.Modules) :=
  fun K => Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K

/-- `Δ_*𝒪_X`, the kernel of the identity Fourier-Mukai functor: the derived direct image along
the diagonal `Δ : X ⟶ X ×_S X` of the structure sheaf of `X` placed in degree zero. -/
def diagonalFourierMukaiKernel {X S : Scheme.{u}} (f : X ⟶ S) :
    DerivedCategory (Limits.pullback f f).Modules :=
  (derivedPushforward (Limits.pullback.diagonal f).toLRSHom.toShHom).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))

/-- `K` represents the identity on perfect complexes: the Fourier-Mukai functor `Φ_K` of
[Stacks, Tag 0FYQ] carries every perfect object of `D(𝒪_X)` to a perfect object, and the
endofunctor of `D_perf(𝒪_X)` it induces is isomorphic to the identity. -/
def RepresentsIdentityOnPerfect {X S : Scheme.{u}} (f : X ⟶ S)
    (K : DerivedCategory (Limits.pullback f f).Modules) : Prop :=
  ∃ hΦ : ∀ M : (perfectDerivedObjects X).FullSubcategory,
      perfectDerivedObjects X ((fourierMukai f f K).obj M.obj),
    Nonempty (fourierMukaiOn f f K (perfectDerivedObjects X) (perfectDerivedObjects X) hΦ ≅ 𝟭 _)

end Stacks.Duality

end
