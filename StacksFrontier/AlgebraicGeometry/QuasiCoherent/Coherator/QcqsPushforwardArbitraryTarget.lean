module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage

/-!
# The derived direct image along a qcqs morphism, at an arbitrary derived category and target

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes. That `Rf_*` carries
`D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)` — part (1) of [Stacks, Tag 08D5] — is
`AlgebraicGeometry.isQuasicoherent_derivedPushforward`, with no hypothesis on `Y`, but stated at
`CategoryTheory.HasDerivedCategory.standard`. `HasDerivedCategory` carries the localized category
as *data*, so that statement says nothing about the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model at which the
quasi-coherent derived categories `Stacks.Duality.quasiCoherentDerivedCategory` and the duality
statements built on them live.

`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/QcqsPushforwardAnyModel.lean` removes that
pin, but from the weaker input available to it at the time: it transports the quasi-compact-target
form `AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward`, and so carries
`[CompactSpace Y]` along. This file runs the same transport on the input with no hypothesis on the
target, which is what [Stacks, Tag 0CR1] needs: that tag assumes of `f` exactly
quasi-compactness and quasi-separatedness, and nothing of `Y`.

The route is unchanged: the statement is first re-expressed with **no derived category in it at
all** — the cohomology sheaves of `f_*I`, for `I` a K-injective resolution of a complex with
quasi-coherent cohomology, are quasi-coherent — and then read back at an arbitrary
`[HasDerivedCategory.{w}]`, where `AlgebraicGeometry.AnyModel.derivedPushforwardObjIso` identifies
`Rf_*E` with the object represented by `f_*I`.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_modulePushforward_of_qcqs_anyTarget` —
  **part (1) of [Stacks, Tag 08D5] for a quasi-compact quasi-separated morphism, with no
  derived category in the statement and no hypothesis on the target.**
* `AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs_anyTarget`
  — the same at an arbitrary chosen model of the two derived categories.
* `Stacks.Duality.isQuasicoherent_homology_derivedPushforward` — that result at the locally small
  model, in the form of the hypothesis `hpush` of
  `Stacks.Duality.quasiCoherentDerivedPushforward`. This is what discharges `hpush` in
  [Stacks, Tag 0CR1].

## Implementation notes

**No `@[stacks 08D5]` attribute is placed**, for the reason already recorded in the files whose
result is transported: the tag has three parts and the integer `N` of [Stacks, Tag 01XJ], and
part (3) — that `N` survives an arbitrary base change — is not available, so the covering set of
the tag is incomplete.

**`attribute [local instance 10000] HasDerivedCategory.standard`, not a plain `local instance`.**
The import closure contains the locally small instances
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `SheafOfModules.hasDerivedCategory`; at
equal priority instance search picks those for the sheaf categories, which would make the statement
of the standard-model section mention a model its input is not stated at. The attribute is scoped
to `section Standard`, so the statements after it are at the locally small model, as the
quasi-coherent derived categories they mention require.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0CR1](https://stacks.math.columbia.edu/tag/0CR1)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit isIso_derivedPushforwardUnit_app_of_isKInjective)

universe w u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The result with no derived category in the statement -/

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Part (1) of [Stacks, Tag 08D5] for a quasi-compact quasi-separated morphism, with no
derived category in the statement and no hypothesis on the target.** Let `f : X ⟶ Y` be a
quasi-compact and quasi-separated morphism of schemes, let `K` be a complex of `𝒪_X`-modules whose
cohomology sheaves are quasi-coherent, and let `s : K ⟶ I` be a quasi-isomorphism into a
K-injective complex. Then the cohomology sheaves of `f_*I` — the complex computing `Rf_*K` — are
quasi-coherent.

This is `AlgebraicGeometry.isQuasicoherent_derivedPushforward` read at the object represented by
`K`. That object is `Rf_*K`, and the isomorphism identifying it with the object represented by
`f_*I` is assembled here from the invertibility of the comparison map at the K-injective `I` and
the invertibility of `s` in the derived category. -/
public theorem isQuasicoherent_homology_modulePushforward_of_qcqs_anyTarget
    [QuasiCompact f] [QuasiSeparated f]
    {K I : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ}
    (hqc : ∀ n : ℤ, (K.homology n).IsQuasicoherent) (s : K ⟶ I) (hI : I.IsKInjective)
    (hs : QuasiIso s) (i : ℤ) :
    ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology i).IsQuasicoherent := by
  set E := DerivedCategory.Qh.obj ((HomotopyCategory.quotient
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)).obj K)
  have hcoh : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj
      E).IsQuasicoherent := fun n =>
    (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).mapIso
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))).app K) ≪≫
        (DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).app K).symm) (hqc n)
  have _ := (Stacks.SmallDerivedCategory.isIso_Qh_map_quotient_map_iff s).2 hs
  have _ := isIso_derivedPushforwardUnit_app_of_isKInjective f.toLRSHom.toShHom I hI
  let objIso : (derivedPushforward f.toLRSHom.toShHom).obj E ≅
      DerivedCategory.Q.obj (((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    (derivedPushforward f.toLRSHom.toShHom).mapIso (asIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) ≪≫
      (asIso ((derivedPushforwardUnit f.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
      (Stacks.SmallDerivedCategory.mapHomotopyCategoryCompQhFactors
        (modulePushforward f.toLRSHom.toShHom)).app I
  exact (SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).mapIso objIso ≪≫
      (DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).app _)
    (isQuasicoherent_derivedPushforward f ⟨E, hcoh⟩ i)

end Standard

/-! ### The same at an arbitrary model -/

namespace AnyModel

/-- **Part (1) of [Stacks, Tag 08D5] for a quasi-compact quasi-separated morphism, at an arbitrary
chosen model of the derived categories and with no hypothesis on the target.** If every cohomology
sheaf of `E` is quasi-coherent then so is every cohomology sheaf of `Rf_*E`; that is, `Rf_*`
carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`.

Every object of the derived category is represented by a complex `K`, and
`AlgebraicGeometry.AnyModel.derivedPushforwardObjIso` identifies `Rf_*E` with the object
represented by `f_*I` for a K-injective resolution `K ⟶ I`; the cohomology sheaves of that complex
are quasi-coherent by the model-free
`AlgebraicGeometry.isQuasicoherent_homology_modulePushforward_of_qcqs_anyTarget`. -/
public theorem isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs_anyTarget
    [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} Y.ringCatSheaf)]
    [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} Y.ringCatSheaf) i).obj
      ((AnyModel.derivedPushforward.{w} f).obj E)).IsQuasicoherent := by
  set K := DerivedCategory.Q.objPreimage E
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eE : DerivedCategory.Qh.obj ((HomotopyCategory.quotient
      (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)).obj K) ≅ E :=
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} X.ringCatSheaf)).app K ≪≫ eQ
  have hKcoh : ∀ n : ℤ, (K.homology n).IsQuasicoherent := fun n =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) n).mapIso eQ).symm ≪≫
        (DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} X.ringCatSheaf) n).app K) (hcoh n)
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective_ringCatSheaf X K
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} Y.ringCatSheaf) i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} Y.ringCatSheaf) i).mapIso
        ((AnyModel.derivedPushforwardObjIso.{w} f s hI hs).symm ≪≫
          (AnyModel.derivedPushforward.{w} f).mapIso eE))
    (isQuasicoherent_homology_modulePushforward_of_qcqs_anyTarget f hKcoh s hI hs i)

end AnyModel

end AlgebraicGeometry

/-! ### The hypothesis `hpush` at the locally small model -/

namespace Stacks.Duality

/-- **Derived direct image along a quasi-compact quasi-separated morphism preserves quasi-coherent
cohomology.** This is part (1) of [Stacks, Tag 08D5] in the form of the hypothesis `hpush` of
`Stacks.Duality.quasiCoherentDerivedPushforward`, at the locally small model in force in the
`Stacks.Duality` namespace, under exactly the hypotheses [Stacks, Tag 0CR1] makes on `f` and with
none on the target.

It is
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs_anyTarget`;
being stated at an arbitrary chosen model of the two derived categories, that result is available
here, which the `HasDerivedCategory.standard` form
`AlgebraicGeometry.isQuasicoherent_derivedPushforward` would not be. -/
theorem isQuasicoherent_homology_derivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent :=
  AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs_anyTarget
    f K.obj K.2 i

end Stacks.Duality

end
