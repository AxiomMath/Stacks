module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineSheafPerfectHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeIsoModel
public import StacksFrontier.AlgebraicGeometry.Perfect.RestrictionOfPerfectObjects
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineDerivedPresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Part (2) of Tag 0A6H on an arbitrary scheme

Part (2) of [Stacks, Tag 0A6H] says that for `E` a *perfect* object of `D(𝒪_X)` and `F` an object
of `D_QCoh(𝒪_X)` the derived internal Hom `R𝓗om_{𝒪_X}(E, F)` has quasi-coherent cohomology
sheaves. The affine statement
`AlgebraicGeometry.derivedCategoryB_affineDerivedSheafHom_of_isPerfect` proves this on the
spectrum of a ring; this file proves it on an arbitrary scheme.

The shape of the argument is the one part (1) takes in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent`:
quasi-coherence of a module and the hypotheses on `E` and `F` are all local, so the statement is
proved by restricting to a cover, twice.

* To an affine open `U ⊆ X`, along `U.ι`. The derived internal Hom commutes with it by
  [Stacks, Tag 08DL] in the form `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`,
  perfectness travels along it by [Stacks, Tag 09UA] in the form
  `AlgebraicGeometry.Scheme.Modules.isPerfect_restrictFunctor_mapDerivedCategory`, and
  `D_QCoh` is preserved because restriction is exact and carries quasi-coherent modules to
  quasi-coherent modules.
* From an affine scheme `W` to `Spec Γ(W, ⊤)`, along `W.isoSpec.inv`. The derived internal Hom
  commutes with it by `Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso` and perfectness travels
  along it by
  `AlgebraicGeometry.Scheme.Modules.isPerfect_restrictFunctor_mapDerivedCategory_of_isIso`.

In each case quasi-coherence of the cohomology sheaves is carried back down the restriction by
`Stacks.Descent.isQuasicoherent_of_restrictFunctor_zariski`, the locality of quasi-coherence of
[Stacks, Tag 01BE].

## Main results

* `AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPerfect_of_isAffine`: part (2) of
  [Stacks, Tag 0A6H] on an affine scheme.
* `AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPerfect`: **part (2) of
  [Stacks, Tag 0A6H] on an arbitrary scheme.**

## Implementation notes

**No boundedness anywhere.** Part (1) asserts a lower bound on the degrees in which
`R𝓗om_{𝒪_X}(E, F)` has cohomology, locally on `X`; part (2) asserts none, and none holds, since
`F` is an arbitrary object of `D_QCoh(𝒪_X)`. The conclusion here is exactly membership of
`D_QCoh(𝒪_X)`.

**Why the derived model is pinned with priority, and why the exactness of restriction to a slice
site is named rather than synthesized.** Both are as recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent`:
the import closure reaches `StacksFrontier.Homology.DerivedCategory.LocallySmall`, whose
`HasDerivedCategory` instances are global, so the local attribute carries priority `10000`; and
the two `PreservesFiniteLimits`/`PreservesFiniteColimits` arguments of
`derivedSheafHomSchemeRestrictionIso` are theorems rather than instances in this development, so
they are supplied by name.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 01BE](https://stacks.math.columbia.edu/tag/01BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules

/-- **Part (2) of [Stacks, Tag 0A6H] on an affine scheme.** For `E` a perfect object of `D(𝒪_W)`
on an affine scheme `W` and `F` an object of `D_QCoh(𝒪_W)`, the derived internal Hom
`R𝓗om_{𝒪_W}(E, F)` has quasi-coherent cohomology sheaves.

Everything is transported along the isomorphism `W.isoSpec.inv : Spec Γ(W, ⊤) ⟶ W`, over which
the statement is the one proved for the spectrum of a ring: perfectness of `E` travels along it,
`F` stays in `D_QCoh`, the derived internal Hom commutes with it, and quasi-coherence of the
cohomology sheaves comes back down because the range of an isomorphism is the whole scheme. -/
theorem derivedCategoryB_derivedSheafHom_of_isPerfect_of_isAffine (W : Scheme.{u})
    [IsAffine W] (E F : DerivedCategory (StructureSheafModules W.sheaf))
    (hE : RingedSpace.IsPerfect (X := W.toRingedSpace) E)
    (hF : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent W.ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent W.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj (op E)).obj F) := by
  have h := derivedCategoryB_affineDerivedSheafHom_of_isPerfect Γ(W, ⊤) _
    (Scheme.Modules.isPerfect_restrictFunctor_mapDerivedCategory_of_isIso
      W.isoSpec.inv E hE) _
    (fun n => isQuasicoherent_homology_restrictFunctor_mapDerivedCategory W.isoSpec.inv hF n)
  intro n
  refine Stacks.Descent.isQuasicoherent_of_restrictFunctor_zariski
    (fun _ : PUnit.{u + 1} => W.isoSpec.inv)
    (by simpa using Scheme.Hom.opensRange_of_isIso W.isoSpec.inv) _ fun _ => ?_
  refine (SheafOfModules.isQuasicoherent (Spec Γ(W, ⊤)).ringCatSheaf).prop_of_iso
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor W.isoSpec.inv) n).app _) ?_
  exact (SheafOfModules.isQuasicoherent (Spec Γ(W, ⊤)).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      (Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso W.isoSpec.inv E F)).symm (h n)

/-- **Stacks Project, Tag 0A6H, part (2).** Let `Y` be a scheme, let `E` be a perfect object of
`D(𝒪_Y)` and let `F` be an object of `D_QCoh(𝒪_Y)`. Then the derived internal Hom
`R𝓗om_{𝒪_Y}(E, F)` lies in `D_QCoh(𝒪_Y)`: all of its cohomology sheaves are quasi-coherent.

The affine opens of `Y` cover it, so by the locality of quasi-coherence it is enough to see that
each cohomology sheaf restricts to a quasi-coherent module on every affine open `U`. Restriction
along `U.ι` commutes with the derived internal Hom by [Stacks, Tag 08DL], keeps `E` perfect by
[Stacks, Tag 09UA] and keeps `F` in `D_QCoh`, so the restriction is the derived internal Hom of
the restrictions on the affine scheme `U`, where
`derivedCategoryB_derivedSheafHom_of_isPerfect_of_isAffine` applies. -/
@[stacks 0A6H "part (2) on an arbitrary scheme: the derived internal Hom out of a perfect \
object into an object of D_QCoh has quasi-coherent cohomology sheaves"]
theorem derivedCategoryB_derivedSheafHom_of_isPerfect (Y : Scheme.{u})
    (E F : DerivedCategory (StructureSheafModules Y.sheaf))
    (hE : RingedSpace.IsPerfect (X := Y.toRingedSpace) E)
    (hF : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj F) := by
  intro n
  refine Stacks.Descent.isQuasicoherent_of_restrictFunctor_zariski
    (fun U : Y.affineOpens => (U : Y.Opens).ι)
    (by simpa only [Scheme.Opens.opensRange_ι] using iSup_affineOpens_eq_top Y) _ fun U => ?_
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := Y.ringCatSheaf) (U : Y.Opens)
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := Y.ringCatSheaf) (U : Y.Opens)
  let _ : IsAffine (U : Y.Opens).toScheme := U.2
  have hres := derivedCategoryB_derivedSheafHom_of_isPerfect_of_isAffine
    (U : Y.Opens).toScheme
    ((Scheme.Modules.restrictFunctor (U : Y.Opens).ι).mapDerivedCategory.obj E)
    ((Scheme.Modules.restrictFunctor (U : Y.Opens).ι).mapDerivedCategory.obj F)
    (Scheme.Modules.isPerfect_restrictFunctor_mapDerivedCategory Y (U : Y.Opens) E hE)
    (fun m => isQuasicoherent_homology_restrictFunctor_mapDerivedCategory
      (U : Y.Opens).ι hF m)
  refine (SheafOfModules.isQuasicoherent (U : Y.Opens).toScheme.ringCatSheaf).prop_of_iso
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor (U : Y.Opens).ι) n).app _) ?_
  exact (SheafOfModules.isQuasicoherent (U : Y.Opens).toScheme.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      (Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso (U : Y.Opens) E F)).symm
    (hres n)

end AlgebraicGeometry

end
