module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardBounds

/-!
# The derived direct image along a qcqs morphism has quasi-coherent cohomology

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `Y`
quasi-compact, and let `E` be an object of `D(𝒪_X)` whose cohomology sheaves are quasi-coherent.
Then every cohomology sheaf of `Rf_*E` is quasi-coherent: `Rf_*` carries `D_QCoh(𝒪_X)` into
`D_QCoh(𝒪_Y)`. This is part (1) of [Stacks, Tag 08D5].

The argument is the one the source gives. Fix a degree `i` and let `N` be the integer of
[Stacks, Tag 01XJ] produced by `AlgebraicGeometry.exists_isLE_derivedPushforward_obj`. The
truncation `τ_{≥ i-N}E` has the same `H ⁱ(Rf_*-)` as `E`, by
`AlgebraicGeometry.exists_isIso_homologyFunctor_map_derivedPushforward_truncGEπ`, and it is
*bounded below*. On a bounded below object the statement is formal: `Rf_*` is exact, preserves
lower cohomological bounds, and carries a single quasi-coherent sheaf placed in one degree into
`D⁺_QCoh` by the quasi-coherence clause of [Stacks, Tag 01XJ]; and the quasi-coherent modules on
a scheme form a weak Serre subcategory, so
`DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE` applies.

## Main results

* `AlgebraicGeometry.derivedCategoryBPlus_derivedPushforward_singleFunctor_obj` — `Rf_*` of a
  quasi-coherent sheaf placed in degree `0` lies in `D⁺_QCoh(𝒪_Y)`, for `f` quasi-compact and
  quasi-separated.
* `AlgebraicGeometry.derivedCategoryBPlus_derivedPushforward_obj_of_isGE` — `Rf_*` carries a
  bounded below object of `D_QCoh(𝒪_X)` into `D⁺_QCoh(𝒪_Y)`, for `f` quasi-compact and
  quasi-separated, with no hypothesis on `Y`.
* `AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward` — **[Stacks, Tag 08D5]
  part (1)** for a quasi-compact quasi-separated morphism with quasi-compact target.

## Implementation notes

The bounded below case needs nothing of the uniform bound: only the quasi-coherence clause of
[Stacks, Tag 01XJ], which holds for an arbitrary quasi-compact quasi-separated morphism. The
uniform bound enters exactly once, to cut an *unbounded* `E` down to a bounded below object
without changing `H ⁱ(Rf_*E)`, and that is why the general case of part (1) carries the
hypothesis `CompactSpace Y` while the bounded below case does not.

**The two spellings of quasi-coherence.** `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules (structureSheafRing X.toRingedSpace)` are definitionally equal
but instance search does not cross them, so the weak Serre structure and the quasi-coherence
clause of [Stacks, Tag 01XJ] are supplied explicitly rather than by `inferInstance`.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit isIso_derivedPushforwardUnit_app_of_isKInjective)

namespace AlgebraicGeometry

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnboundedHigherDirectImage.isGrothendieckAbelian_moduleSheaves

variable {X Y : Scheme.{u}}

/-- The shift commutation of `Rf_*`, as a right derived functor of `f_*`. -/
private noncomputable abbrev derivedPushforwardCommShift (f : X ⟶ Y)
    [IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))] :
    (derivedPushforward f.toLRSHom.toShHom).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) ℤ

/-- **`Rf_*` of a quasi-coherent sheaf placed in degree zero is bounded below with
quasi-coherent cohomology.** For a quasi-compact quasi-separated `f` and a quasi-coherent
`𝒪_X`-module `M`, the object `Rf_*(M[0])` lies in `D⁺_QCoh(𝒪_Y)`.

Boundedness below is `AlgebraicGeometry.isGE_derivedPushforward_obj`, which holds for any
morphism; quasi-coherence of the cohomology is the quasi-coherence clause of [Stacks, Tag 01XJ]
read through `Stacks.SmallDerivedCategory.prop_homologyFunctor_obj_singleFunctor_obj`, since on a
bounded below object `Rf_*` is computed by the bounded below right derived functor of `f_*`. -/
public theorem derivedCategoryBPlus_derivedPushforward_singleFunctor_obj (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (hM : M.IsQuasicoherent) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace))
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)) := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X.toRingedSpace)
  let _ := derivedPushforwardCommShift f
  refine ⟨(DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2
    ⟨0, isGE_derivedPushforward_obj f _ 0 inferInstance⟩, fun n ↦ ?_⟩
  exact Stacks.SmallDerivedCategory.prop_homologyFunctor_obj_singleFunctor_obj
    (modulePushforward f.toLRSHom.toShHom) (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (fun I hI ↦ isIso_derivedPushforwardUnit_app_of_isKInjective f.toLRSHom.toShHom I hI)
    (SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)) M
    (fun p ↦ @Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage
      X Y f ‹_› ‹_› M (hM : (M : X.Modules).IsQuasicoherent) p) 0 n

/-- **`Rf_*` carries a bounded below object of `D_QCoh(𝒪_X)` into `D⁺_QCoh(𝒪_Y)`.** For `f`
quasi-compact and quasi-separated — with no hypothesis on the target — and `E` an object of
`D(𝒪_X)` with quasi-coherent cohomology sheaves living in degrees `≥ a`, every cohomology sheaf
of `Rf_*E` is quasi-coherent and vanishes below `a`.

`Rf_*` is a triangulated functor preserving lower cohomological bounds, the quasi-coherent
modules on `Y` form a weak Serre subcategory, and the value of `Rf_*` at a single quasi-coherent
sheaf lies in `D⁺_QCoh(𝒪_Y)`; so this is
`DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE`. -/
public theorem derivedCategoryBPlus_derivedPushforward_obj_of_isGE (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (a : ℤ) (hE : E.IsGE a) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace))
      ((derivedPushforward f.toLRSHom.toShHom).obj E) := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X.toRingedSpace)
  let _ := derivedPushforwardCommShift f
  have _ : (derivedPushforward f.toLRSHom.toShHom).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated
      (modulePushforward f.toLRSHom.toShHom) _ (derivedPushforwardUnit f.toLRSHom.toShHom)
  exact DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE
    (derivedPushforward f.toLRSHom.toShHom) _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre Y)
    (fun L m hL ↦ isGE_derivedPushforward_obj f L m hL) E a hE
    (fun q ↦ derivedCategoryBPlus_derivedPushforward_singleFunctor_obj f _ (hcoh q))

/-- **[Stacks, Tag 08D5] part (1).** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated
morphism of schemes with `Y` quasi-compact, and let `E` be an object of `D(𝒪_X)` whose cohomology
sheaves are quasi-coherent. Then every cohomology sheaf of `Rf_*E` is quasi-coherent; that is,
`Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`.

Fix `i`. By `AlgebraicGeometry.exists_isIso_homologyFunctor_map_derivedPushforward_truncGEπ` there
is an `N`, independent of `E` and of `i`, with `H ⁱ(Rf_*E) ≅ H ⁱ(Rf_*(τ_{≥ i-N}E))`; the
truncation is bounded below and still has quasi-coherent cohomology sheaves, so
`AlgebraicGeometry.derivedCategoryBPlus_derivedPushforward_obj_of_isGE` applies to it. -/
public theorem isQuasicoherent_homologyFunctor_derivedPushforward (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
      ((derivedPushforward f.toLRSHom.toShHom).obj E)).IsQuasicoherent := by
  obtain ⟨N, hN⟩ := exists_isIso_homologyFunctor_map_derivedPushforward_truncGEπ f
  let PX := SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)
  have hcohGE : ∀ j : ℤ, PX ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj
      ((DerivedCategory.TStructure.t.truncGE (i - (N : ℤ))).obj E)) := fun j ↦
    @Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj _ _ _ _ PX _
      (containsZero_isQuasicoherent X) E hcoh (i - (N : ℤ)) j
  have hBplus := derivedCategoryBPlus_derivedPushforward_obj_of_isGE f
    ((DerivedCategory.TStructure.t.truncGE (i - (N : ℤ))).obj E) hcohGE (i - (N : ℤ))
    inferInstance
  have _ := hN E hcoh (i - (N : ℤ)) i (by omega)
  exact (SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)).prop_of_iso
    (asIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
      ((derivedPushforward f.toLRSHom.toShHom).map
        ((DerivedCategory.TStructure.t.truncGEπ (i - (N : ℤ))).app E)))).symm (hBplus.2 i)

end AlgebraicGeometry

end
