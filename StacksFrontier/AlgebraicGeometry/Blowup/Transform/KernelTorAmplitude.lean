module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingKernel
public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DirectSummands
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.Restriction

/-!
# Tor amplitude of the kernel of an epimorphism onto a finite locally free module

Let `f : ℳ ⟶ 𝒩` be an epimorphism of modules on a scheme `Y` with `𝒩` finite locally free. Then
`ker f` is a direct summand of `ℳ` locally on `Y`, so it inherits any Tor-amplitude bound of
`ℳ`. The local-to-global property of Tor amplitude is also stated with restriction given by
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`.

## Main results

* `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top_restrictFunctor`:
  **Tor amplitude in `[a, b]` is local on an open covering of a scheme**, with the restriction
  read as `AlgebraicGeometry.Scheme.Modules.restrictFunctor` along the open immersion of a member
  of the covering.
* `AlgebraicGeometry.hasTorAmplitude_single_kernel_of_isFiniteLocallyFree`: **the kernel of an
  epimorphism onto a finite locally free module inherits a Tor-amplitude bound from the source.**

## Implementation notes

Restriction of modules to an open subscheme has two forms,
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` along `U.ι` and
`AlgebraicGeometry.RingedSpace.restrictModules`, identified on modules by
`AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor` and on derived categories by
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`.

Restriction to an open subspace is exact, so it commutes with the degree-zero single functor into
the derived category (`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`).

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, made a local
instance.

## References

* [Stacks Project, Tag 08CK](https://stacks.math.columbia.edu/tag/08CK)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 0ESN](https://stacks.math.columbia.edu/tag/0ESN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.TorAmplitude

/-! ### Retracts and restriction, at a module placed in degree zero -/

/-- A retract of a module whose degree-zero placement has Tor amplitude in `[a, b]` again has
Tor amplitude in `[a, b]` when placed in degree zero. -/
theorem hasTorAmplitude_single_of_retract (X : RingedSpace.{u, u}) {A B : OXMod.{u, u} X}
    (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A) (a b : ℤ)
    (h : HasTorAmplitude X ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj B) a b) :
    HasTorAmplitude X ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj A) a b :=
  hasTorAmplitude_of_retract (X := X) a b
    ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).map i)
    ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).map r)
    (by rw [← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id]) h

/-- **Tor amplitude in `[a, b]` of a module placed in degree zero restricts to an open
subspace.** If `ℳ[0]` has Tor amplitude in `[a, b]` with `a ≤ b`, then so does `(ℳ|_U)[0]`
for every open `U`. -/
theorem hasTorAmplitude_single_restrictModules (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (M : OXMod.{u, u} X) (a b : ℤ) (hab : a ≤ b)
    (h : HasTorAmplitude X ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M) a b) :
    HasTorAmplitude (X.restrict U.isOpenEmbedding)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).obj
        ((restrictModules.{u, u} X U).obj M)) a b :=
  hasTorAmplitude_of_retract (X := X.restrict U.isOpenEmbedding) a b
    (((restrictModules.{u, u} X U).mapDerivedCategorySingleFunctor 0).app M).inv
    (((restrictModules.{u, u} X U).mapDerivedCategorySingleFunctor 0).app M).hom
    (((restrictModules.{u, u} X U).mapDerivedCategorySingleFunctor 0).app M).inv_hom_id
    (hasTorAmplitude_restrictModules U _ a b hab h)

/-- If `(ℳ|_U)[0]` has Tor amplitude in `[a, b]`, then so does the derived restriction of `ℳ[0]`
to `U`. -/
theorem hasTorAmplitude_derivedRestrictModules_single (X : RingedSpace.{u, u})
    (U : Opens X.carrier) (M : OXMod.{u, u} X) (a b : ℤ)
    (h : HasTorAmplitude (X.restrict U.isOpenEmbedding)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).obj
        ((restrictModules.{u, u} X U).obj M)) a b) :
    HasTorAmplitude (X.restrict U.isOpenEmbedding)
      ((derivedRestrictModules X U).obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M)) a b :=
  hasTorAmplitude_of_retract (X := X.restrict U.isOpenEmbedding) a b
    (((restrictModules.{u, u} X U).mapDerivedCategorySingleFunctor 0).app M).hom
    (((restrictModules.{u, u} X U).mapDerivedCategorySingleFunctor 0).app M).inv
    (((restrictModules.{u, u} X U).mapDerivedCategorySingleFunctor 0).app M).hom_inv_id h

/-- **Tor amplitude in `[a, b]` is local on an open covering of a scheme.** If the restriction of
an object of `D(𝒪_Z)` along the open immersion of each member of an open covering of `Z` has Tor
amplitude in `[a, b]`, then the object has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitude_of_iSup_eq_top_restrictFunctor (Z : Scheme.{u})
    (E : DerivedCategory (OXMod.{u, u} Z.toRingedSpace)) (a b : ℤ) {ι : Type*}
    (V : ι → Z.Opens) (hV : iSup V = ⊤)
    (h : ∀ i : ι, HasTorAmplitude (Z.toRingedSpace.restrict (V i).isOpenEmbedding)
      ((Scheme.Modules.restrictFunctor (V i).ι).mapDerivedCategory.obj E) a b) :
    HasTorAmplitude Z.toRingedSpace E a b :=
  hasTorAmplitude_of_iSup_eq_top Z.toRingedSpace E a b V hV fun i =>
    hasTorAmplitude_of_retract
      (X := Z.toRingedSpace.restrict (V i).isOpenEmbedding) a b
      ((derivedRestrictModulesIsoRestrictFunctor Z (V i)).app E).hom
      ((derivedRestrictModulesIsoRestrictFunctor Z (V i)).app E).inv
      ((derivedRestrictModulesIsoRestrictFunctor Z (V i)).app E).hom_inv_id (h i)

end Stacks.Cohomology.TorAmplitude

namespace AlgebraicGeometry

open Stacks.Cohomology.TorAmplitude

/-- **The kernel of an epimorphism onto a finite locally free module inherits a Tor-amplitude
bound from the source.** Let `f : ℳ ⟶ 𝒩` be an epimorphism of modules on a scheme `Y` with `𝒩`
finite locally free, and suppose `ℳ[0]` has Tor amplitude in `[a, b]` with `a ≤ b`. Then
`(ker f)[0]` has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitude_single_kernel_of_isFiniteLocallyFree {Y : Scheme.{u}} {M N : Y.Modules}
    (f : M ⟶ N) [Epi f] [SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (a b : ℤ) (hab : a ≤ b)
    (h : HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj M) a b) :
    HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj (kernel f)) a b := by
  classical
  choose V hyV hsplit using fun y : Y => exists_isSplitEpi_restrictFunctor_map f y
  refine hasTorAmplitude_of_iSup_eq_top Y.toRingedSpace _ a b V
    (eq_top_iff.mpr fun y _ => Opens.mem_iSup.mpr ⟨y, hyV y⟩) fun y => ?_
  have hsp : IsSplitEpi ((restrictModules.{u, u} Y.toRingedSpace (V y)).map f) :=
    @isSplitEpi_map_of_iso_functor _ _ _ _ _ _
      (restrictModulesIsoRestrictFunctor Y (V y)).symm _ _ f (hsplit y)
  have := hsp
  let : (restrictModules.{u, u} Y.toRingedSpace (V y)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext _ _; rfl⟩
  have e : (restrictModules.{u, u} Y.toRingedSpace (V y)).obj (kernel f) ≅
      kernel ((restrictModules.{u, u} Y.toRingedSpace (V y)).map f) :=
    PreservesKernel.iso (restrictModules.{u, u} Y.toRingedSpace (V y)) f
  refine hasTorAmplitude_derivedRestrictModules_single Y.toRingedSpace (V y) _ a b ?_
  refine hasTorAmplitude_single_of_retract _
    (e.hom ≫ kernel.ι ((restrictModules.{u, u} Y.toRingedSpace (V y)).map f))
    (kernelRetraction ((restrictModules.{u, u} Y.toRingedSpace (V y)).map f) ≫ e.inv)
    (kernelι_comp_kernelRetraction_of_iso _ e) a b
    (hasTorAmplitude_single_restrictModules Y.toRingedSpace (V y) M a b hab h)

end AlgebraicGeometry

end
