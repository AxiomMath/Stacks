module

public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardQuasiCoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived direct image along a qcqs morphism, at an arbitrary derived category

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `Y`
quasi-compact. That `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)` — part (1) of
[Stacks, Tag 08D5] — is proved in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/QcqsPushforwardQuasiCoherence.lean` at
`CategoryTheory.HasDerivedCategory.standard`. `HasDerivedCategory` carries the localized category
as *data*, so that statement says nothing about the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model at which the
quasi-coherent derived categories `Stacks.Duality.quasiCoherentDerivedCategory` and the duality
statements built on them live. This file removes the pin.

The route is the one
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardAnyModel.lean` takes for an
affine morphism, and the proofs below are that file's with the affine input replaced by the
quasi-compact quasi-separated one: the statement is first re-expressed with **no derived category
in it at all** — the cohomology sheaves of `f_*I`, for `I` a K-injective resolution of a complex
with quasi-coherent cohomology, are quasi-coherent — and then read back at an arbitrary
`[HasDerivedCategory.{w}]`, where `AlgebraicGeometry.AnyModel.derivedPushforwardObjIso` identifies
`Rf_*E` with the object represented by `f_*I`.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_modulePushforward_of_qcqs` — **part (1) of
  [Stacks, Tag 08D5] for a quasi-compact quasi-separated morphism with quasi-compact target, with
  no derived category in the statement.**
* `AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs` — the
  same at an arbitrary chosen model of the two derived categories.
* `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` — that result at the
  locally small model, in the form of the hypothesis `hpush` of
  `Stacks.Duality.quasiCoherentDerivedPushforward`.
* `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_opens` — the open-immersion case:
  for `W` a quasi-compact open of a quasi-compact quasi-separated scheme `X`, `Rj_{W,*}` preserves
  quasi-coherence of cohomology.
* `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_opens_inf` — the same along
  `j_{U ∩ V}` for two quasi-compact opens `U`, `V`.
* `AlgebraicGeometry.Scheme.Opens.compactSpace_inf` — the intersection of two quasi-compact opens
  of a quasi-separated scheme is quasi-compact.

## Implementation notes

**No `@[stacks 08D5]` attribute is placed**, for the reason already recorded in the two files whose
results are transported: the tag has three parts and the integer `N` of [Stacks, Tag 01XJ], and
part (3) — that `N` survives an arbitrary base change — is not available, so the covering set of
the tag is incomplete.

**`attribute [local instance 10000] HasDerivedCategory.standard`, not a plain `local instance`.**
The import closure contains the locally small instances
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `SheafOfModules.hasDerivedCategory`; at
equal priority instance search picks those for the sheaf categories, which would make the statement
of the standard-model section mention a model its input is not stated at. The attribute is scoped
to `section Standard`, so the two statements after it are at the locally small model, as the
quasi-coherent derived categories they mention require.

**The open-immersion case.** `j_W : W ⟶ X` for `W` an open of `X` is a monomorphism, hence
quasi-separated, and it is quasi-compact when `W` is a quasi-compact space and `X` is a
quasi-separated one; both are found by instance search, so the hypotheses of the corollary are the
geometric ones — `W` quasi-compact and `X` quasi-compact quasi-separated. This is the case the
Mayer--Vietoris triangle of [Stacks, Tag 0CR2] consumes, along `j_U`, `j_V` and `j_{U ∩ V}`.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 0CR2](https://stacks.math.columbia.edu/tag/0CR2)
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

/-- If `E ≅ Q K` then the cohomology sheaves of `E` are quasi-coherent iff those of `K` are. -/
private theorem isQuasicoherent_homologyFunctor_iff_of_iso
    [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    {K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ}
    {E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)} (e : DerivedCategory.Q.obj K ≅ E)
    (n : ℤ) : ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) n).obj E
      ).IsQuasicoherent ↔ (K.homology n).IsQuasicoherent :=
  have e' := ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) n).mapIso
    e).symm ≪≫ (DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} X.ringCatSheaf) n).app K
  ⟨fun h => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e' h,
    fun h => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e'.symm h⟩

/-! ### The result with no derived category in the statement -/

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Part (1) of [Stacks, Tag 08D5] for a quasi-compact quasi-separated morphism with
quasi-compact target, with no derived category in the statement.** Let `f : X ⟶ Y` be a
quasi-compact and quasi-separated morphism of schemes with `Y` quasi-compact, let `K` be a complex
of `𝒪_X`-modules whose cohomology sheaves are quasi-coherent, and let `s : K ⟶ I` be a
quasi-isomorphism into a K-injective complex. Then the cohomology sheaves of `f_*I` — the complex
computing `Rf_*K` — are quasi-coherent.

This is `AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward` read at the object
represented by `K`. That object is `Rf_*K`, and the isomorphism identifying it with the object
represented by `f_*I` is assembled here from the invertibility of the comparison map at the
K-injective `I` and the invertibility of `s` in the derived category. -/
public theorem isQuasicoherent_homology_modulePushforward_of_qcqs
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    {K I : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ}
    (hqc : ∀ n : ℤ, (K.homology n).IsQuasicoherent) (s : K ⟶ I) (hI : I.IsKInjective)
    (hs : QuasiIso s) (i : ℤ) :
    ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology i).IsQuasicoherent := by
  set E := DerivedCategory.Qh.obj ((HomotopyCategory.quotient
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)).obj K) with hE
  have hcoh : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj E).IsQuasicoherent :=
    fun n => (isQuasicoherent_homologyFunctor_iff_of_iso (X := X)
      ((DerivedCategory.quotientCompQhIso _).app K).symm n).2 (hqc n)
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
    (isQuasicoherent_homologyFunctor_derivedPushforward f E hcoh i)

end Standard

/-! ### The same at an arbitrary model -/

namespace AnyModel

/-- **Part (1) of [Stacks, Tag 08D5] for a quasi-compact quasi-separated morphism with
quasi-compact target, at an arbitrary chosen model of the derived categories.** If every
cohomology sheaf of `E` is quasi-coherent then so is every cohomology sheaf of `Rf_*E`; that is,
`Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`. -/
public theorem isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs
    [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} Y.ringCatSheaf)]
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} Y.ringCatSheaf) i).obj
      ((AnyModel.derivedPushforward.{w} f).obj E)).IsQuasicoherent := by
  set K := DerivedCategory.Q.objPreimage E
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hKcoh : ∀ n : ℤ, (K.homology n).IsQuasicoherent := fun n =>
    (isQuasicoherent_homologyFunctor_iff_of_iso eQ n).1 (hcoh n)
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective_ringCatSheaf X K
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} Y.ringCatSheaf) i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} Y.ringCatSheaf) i).mapIso
        ((AnyModel.derivedPushforwardObjIso.{w} f s hI hs).symm ≪≫
          (AnyModel.derivedPushforward.{w} f).mapIso
            ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} X.ringCatSheaf)).app K ≪≫ eQ)))
    (isQuasicoherent_homology_modulePushforward_of_qcqs f hKcoh s hI hs i)

end AnyModel

/-! ### Quasi-compactness of the intersection of two quasi-compact opens -/

/-- **The intersection of two quasi-compact opens of a quasi-separated scheme is quasi-compact.**
This is the defining property of a quasi-separated space, read for the opens of a scheme and in
the form `CompactSpace` of the open subscheme. -/
public theorem Scheme.Opens.compactSpace_inf {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U V : X.Opens) [CompactSpace U.toScheme] [CompactSpace V.toScheme] :
    CompactSpace (U ⊓ V).toScheme :=
  isCompact_iff_compactSpace.1 (QuasiSeparatedSpace.inter_isCompact _ _ U.2
    (isCompact_iff_compactSpace.2 ‹_›) V.2 (isCompact_iff_compactSpace.2 ‹_›))

end AlgebraicGeometry

/-! ### The hypothesis `hpush` at the locally small model -/

namespace Stacks.Duality

/-- **Derived direct image along a quasi-compact quasi-separated morphism with quasi-compact
target preserves quasi-coherent cohomology.** This is part (1) of [Stacks, Tag 08D5] in the form of
the hypothesis `hpush` of `Stacks.Duality.quasiCoherentDerivedPushforward`, at the locally small
model in force in the `Stacks.Duality` namespace.

It is `AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs`;
being stated at an arbitrary chosen model of the two derived categories, that result is available
here, which the `HasDerivedCategory.standard` form
`AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward` would not be. -/
theorem isQuasicoherent_homology_derivedPushforward_of_qcqs {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent :=
  AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs
    f K.obj K.2 i

/-- **Derived direct image along the inclusion of a quasi-compact open preserves quasi-coherent
cohomology**, part (1) of [Stacks, Tag 08D5] for `j_W : W ⟶ X` with `W` a quasi-compact open of a
quasi-compact quasi-separated scheme `X`.

An open immersion is a monomorphism, hence quasi-separated, and it is quasi-compact because `W` is
a quasi-compact space and `X` a quasi-separated one; so this is
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` along `j_W`. These are the
three instances of [Stacks, Tag 08D5] part (1) that the Mayer--Vietoris triangle of
[Stacks, Tag 0CR2] consumes. -/
@[ega "III 6.2.3" "special case"]
theorem isQuasicoherent_homology_derivedPushforward_opens {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (W : X.Opens) [CompactSpace W.toScheme]
    (L : quasiCoherentDerivedCategory W.toScheme) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward W.ι).obj L.obj)).IsQuasicoherent :=
  isQuasicoherent_homology_derivedPushforward_of_qcqs W.ι L i

/-- **Derived direct image along the inclusion of the intersection of two quasi-compact opens
preserves quasi-coherent cohomology**, part (1) of [Stacks, Tag 08D5] for `j_{U ∩ V}`.

This is `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_opens` at the open `U ⊓ V`,
which is quasi-compact because `X` is quasi-separated
(`AlgebraicGeometry.Scheme.Opens.compactSpace_inf`). It is stated separately because that
quasi-compactness is not an instance. -/
@[ega "III 6.2.3" "special case"]
theorem isQuasicoherent_homology_derivedPushforward_opens_inf {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U V : X.Opens)
    [CompactSpace U.toScheme] [CompactSpace V.toScheme]
    (L : quasiCoherentDerivedCategory (U ⊓ V).toScheme) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward (U ⊓ V).ι).obj L.obj)).IsQuasicoherent :=
  have := AlgebraicGeometry.Scheme.Opens.compactSpace_inf U V
  isQuasicoherent_homology_derivedPushforward_opens (U ⊓ V) L i

end Stacks.Duality

end
