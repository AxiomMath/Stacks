module

public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictFree
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# The global sections of a free module on an affine scheme

Let `T` be an affine scheme with ring of functions `A = Γ(T, ⊤)` and let `ι` be a type in the
universe of `A`. The free `𝒪_T`-module `SheafOfModules.free ι`, the coproduct of `ι` copies of
the structure sheaf, has global sections the free `A`-module `ι →₀ A`.

Mathlib's `AlgebraicGeometry.tildeFinsupp` is this computation on `Spec A` and in the opposite
direction: it identifies the sheaf `(ι →₀ A)^~` associated with the free module with the free
sheaf of modules. Composing it with the counit of the tilde–global-sections adjunction turns it
into a statement about sections, and the affine dictionary of
`Stacks.AlgebraicGeometry.CoherentFinite.specSectionsEquiv` transports that statement from
`Spec A` to an arbitrary affine scheme with ring of functions `A`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.free`: the free module on a type, as an object of
  `X.Modules` rather than of `SheafOfModules X.ringCatSheaf`.
* `AlgebraicGeometry.freeSpecRestrictIso` and `AlgebraicGeometry.freeSpecModuleIso`: the free
  module of an affine scheme, read on the spectrum of its ring of functions, is the free sheaf
  there, and its module of sections is the free module.
* `AlgebraicGeometry.freeSectionsEquiv`: **the global sections of the free `𝒪_T`-module on `ι`
  are the free `Γ(T, ⊤)`-module on `ι`.**

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.free` exists only to place the free sheaf in `X.Modules`.
`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, so the
instance `Module Γ(X, U) Γ(M, U)`, whose module argument ranges over `X.Modules`, is not found
for a term whose type is spelled `SheafOfModules X.ringCatSheaf`: instance synthesis does not
unfold the `def`. Writing `Γ(SheafOfModules.free ι, ⊤)` in a statement therefore fails, while
`Γ(Scheme.Modules.free T ι, ⊤)` succeeds. The abbreviation is reducible, so a morphism out of
`SheafOfModules.free ι` — the form in which `AlgebraicGeometry.DevissageStage.alpha` records its
free module — is accepted wherever one out of `Scheme.Modules.free` is expected, with no
transport.

The transport from `Spec A` to `T` is the one already built for Stacks 01PB: `specRestrict`
reads a module on `T` as a module on `Spec Γ(T, ⊤)` by restricting twice along open immersions,
and `specSectionsEquiv` identifies its module of sections with the sections on `T`, scalar
structures included. Restriction along an open immersion is a left adjoint carrying the
structure sheaf to the structure sheaf, so it carries free modules to free modules
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorObjFree`); that is the whole of
`AlgebraicGeometry.freeSpecRestrictIso`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.CoherentFinite Stacks.AlgebraicGeometry.CoherentTFAE

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

/-- The free `𝒪_X`-module on a type `ι`, as an object of `X.Modules`. -/
public abbrev free (X : Scheme.{u}) (ι : Type u) : X.Modules := SheafOfModules.free ι

end Scheme.Modules

/-- The free module of an affine scheme, read on the spectrum of its ring of functions, is the
free sheaf of modules there. Restriction along an open immersion carries free modules to free
modules, and `Stacks.AlgebraicGeometry.CoherentTFAE.specRestrict` is a composite of two such
restrictions. -/
public def freeSpecRestrictIso (T : Scheme.{u}) [IsAffine T] (ι : Type u) :
    specRestrict (Scheme.Modules.free T ι) (isAffineOpen_top T) ≅
      Scheme.Modules.free (Spec Γ(T, (⊤ : T.Opens))) ι :=
  (Scheme.Modules.restrictFunctor (isAffineOpen_top T).isoSpec.inv).mapIso
      (Scheme.Modules.restrictFunctorObjFree (⊤ : T.Opens).ι ι) ≪≫
    Scheme.Modules.restrictFunctorObjFree (isAffineOpen_top T).isoSpec.inv ι

/-- The `Γ(T, ⊤)`-module attached to the free module of an affine scheme `T` is the free
`Γ(T, ⊤)`-module. This is Mathlib's `AlgebraicGeometry.tildeFinsupp`, composed with the unit of
the tilde–global-sections adjunction and read through
`AlgebraicGeometry.freeSpecRestrictIso`. -/
public def freeSpecModuleIso (T : Scheme.{u}) [IsAffine T] (ι : Type u) :
    specModule (Scheme.Modules.free T ι) (isAffineOpen_top T) ≅
      ModuleCat.of Γ(T, (⊤ : T.Opens)) (ι →₀ Γ(T, (⊤ : T.Opens))) :=
  moduleSpecΓFunctor.mapIso (freeSpecRestrictIso T ι) ≪≫
    moduleSpecΓFunctor.mapIso (tildeFinsupp (R := Γ(T, (⊤ : T.Opens))) ι).symm ≪≫
    (tilde.isoTop (ModuleCat.of Γ(T, (⊤ : T.Opens)) (ι →₀ Γ(T, (⊤ : T.Opens))))).symm

/-- **The global sections of the free `𝒪_T`-module on `ι` are the free `Γ(T, ⊤)`-module on `ι`**,
for `T` an affine scheme. -/
public def freeSectionsEquiv (T : Scheme.{u}) [IsAffine T] (ι : Type u) :
    Γ(Scheme.Modules.free T ι, (⊤ : T.Opens)) ≃ₗ[Γ(T, (⊤ : T.Opens))]
      (ι →₀ Γ(T, (⊤ : T.Opens))) :=
  (specSectionsEquiv (Scheme.Modules.free T ι) (isAffineOpen_top T)).symm.trans
    (freeSpecModuleIso T ι).toLinearEquiv

end AlgebraicGeometry

end
