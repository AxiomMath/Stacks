module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeIsoModel
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeRestriction
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineDerivedPresentation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictFunctorAlongIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Homology.PseudoCoherent.Locality
import StacksCore.Tactic.StacksAttribute

/-!
# Part (1) of Tag 0A6H on an arbitrary scheme

Part (1) of [Stacks, Tag 0A6H] says that for `E` a pseudo-coherent object of `D(𝒪_X)` and `F` an
object of `D⁺_QCoh(𝒪_X)` the derived internal Hom `R𝓗om_{𝒪_X}(E, F)` has quasi-coherent
cohomology sheaves. The affine statement
`derivedCategoryBPlus_affineDerivedSheafHom_of_isPseudoCoherent_of_derivedCategoryBPlus`
proves this on the spectrum of a ring; this file proves it on an arbitrary scheme.

Both quasi-coherence of a module and the hypotheses on `E` and `F` are local, so the statement is
proved by restricting to a cover. Two restrictions are used.

* To an affine open `U ⊆ X`, along `U.ι`. The derived internal Hom commutes with it by
  [Stacks, Tag 08DL] in the form `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`,
  pseudo-coherence travels along it by [Stacks, Tag 08CC], and `D⁺_QCoh` is preserved because
  restriction is exact and carries quasi-coherent modules to quasi-coherent modules.
* From an affine scheme `W` to `Spec Γ(W, ⊤)`, along `W.isoSpec.inv`. The derived internal Hom
  commutes with it by `Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso` and pseudo-coherence
  travels along it by
  `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_restrictFunctor_mapDerivedCategory_of_isIso`.

In each case quasi-coherence of the cohomology sheaves is carried back down the restriction by
`Stacks.Descent.isQuasicoherent_of_restrictFunctor_zariski`, the locality of quasi-coherence of
[Stacks, Tag 01BE]: the images of the restrictions used cover the scheme — the affine opens
because they form a basis, and an isomorphism because its range is everything.

## Main results

* `AlgebraicGeometry.isBoundedBelow_restrictFunctor_mapDerivedCategory` and
  `AlgebraicGeometry.derivedCategoryBPlus_restrictFunctor_mapDerivedCategory`: restriction along
  an open immersion of schemes preserves cohomological boundedness below, and carries
  `D⁺_QCoh` into `D⁺_QCoh`.
* `AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent_of_isAffine`: part (1)
  of [Stacks, Tag 0A6H] on an affine scheme.
* `AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent`: **part (1) of
  [Stacks, Tag 0A6H] on an arbitrary scheme.**

## Implementation notes

**What the conclusion is.** `R𝓗om_{𝒪_X}(E, F)` is placed in `D_QCoh(𝒪_X)`: every cohomology
sheaf is quasi-coherent. A uniform lower bound on the degrees in which it has cohomology is not
claimed, and does not follow by this argument — each affine open of the cover supplies a bound
of its own, and on a scheme that is not quasi-compact there is no reason for the family of
bounds to be bounded. On the spectrum of a ring the bound is available, as the first component
of `derivedCategoryBPlus_affineDerivedSheafHom_of_isPseudoCoherent_of_derivedCategoryBPlus`.

The *local* lower bound, which is what part (1) of the tag asserts alongside quasi-coherence, is
the other half of the clause. It is proved as
`AlgebraicGeometry.isLocallyBoundedBelow_derivedSheafHom_of_isPseudoCoherent`, in the file
`DerivedTilde/SchemeSheafPseudoCoherentHomLocallyBounded.lean` of this directory; the two
declarations together are the covering set of part (1) on an arbitrary scheme.

**Why the derived model is pinned with priority.** The affine input is stated at
`CategoryTheory.HasDerivedCategory.standard`, and the import closure reaches
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose `HasDerivedCategory` instances
are *global*; the local attribute below therefore carries priority `10000`, as
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean` requires of
its importers.

**The exactness of restriction to a slice site is named rather than synthesized.** The two
`PreservesFiniteLimits`/`PreservesFiniteColimits` instance arguments of
`derivedSheafHomSchemeRestrictionIso` are supplied from
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits` and its colimit
companion; they are theorems rather than instances in this development, so synthesis does not
find them.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Tag 01BE](https://stacks.math.columbia.edu/tag/01BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules

/-- Restriction along an open immersion of schemes preserves cohomological boundedness below:
it is exact, so it commutes with taking cohomology, and it carries a zero object to a zero
object. -/
theorem isBoundedBelow_restrictFunctor_mapDerivedCategory {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (K : DerivedCategory (StructureSheafModules Y.sheaf))
    (hK : DerivedCategoryB.IsBoundedBelow K) :
    DerivedCategoryB.IsBoundedBelow
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K) := by
  obtain ⟨n₀, hn₀⟩ := hK
  exact ⟨n₀, fun m hm => ((Scheme.Modules.restrictFunctor g).map_isZero (hn₀ m hm)).of_iso
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso (Scheme.Modules.restrictFunctor g) m).app K)⟩

/-- Restriction along an open immersion of schemes carries `D⁺_QCoh` into `D⁺_QCoh`: it
preserves boundedness below, and the restriction of a quasi-coherent module is
quasi-coherent. -/
theorem derivedCategoryBPlus_restrictFunctor_mapDerivedCategory {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (K : DerivedCategory (StructureSheafModules Y.sheaf))
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) K) :
    DerivedCategoryB.derivedCategoryBPlus (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K) :=
  ⟨isBoundedBelow_restrictFunctor_mapDerivedCategory g K hK.1,
    isQuasicoherent_homology_restrictFunctor_mapDerivedCategory g hK.2⟩

/-- **Part (1) of [Stacks, Tag 0A6H] on an affine scheme.** For `E` a pseudo-coherent object of
`D(𝒪_W)` on an affine scheme `W` and `F` an object of `D⁺_QCoh(𝒪_W)`, the derived internal Hom
`R𝓗om_{𝒪_W}(E, F)` has quasi-coherent cohomology sheaves.

Everything is transported along the isomorphism `W.isoSpec.inv : Spec Γ(W, ⊤) ⟶ W`, over which
the statement is the one proved for the spectrum of a ring:
pseudo-coherence of `E` travels along it, `F` stays in `D⁺_QCoh`, the derived internal Hom
commutes with it, and quasi-coherence of the cohomology sheaves comes back down because the
range of an isomorphism is the whole scheme. -/
theorem derivedCategoryB_derivedSheafHom_of_isPseudoCoherent_of_isAffine (W : Scheme.{u})
    [IsAffine W] (E F : DerivedCategory (StructureSheafModules W.sheaf))
    (hE : RingedSpace.IsPseudoCoherent (X := W.toRingedSpace) E)
    (hF : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent W.ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent W.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj (op E)).obj F) := by
  have h := derivedCategoryBPlus_affineDerivedSheafHom_of_isPseudoCoherent_of_derivedCategoryBPlus
    Γ(W, ⊤) _
    (Scheme.Modules.isPseudoCoherent_restrictFunctor_mapDerivedCategory_of_isIso
      W.isoSpec.inv E hE) _
    (derivedCategoryBPlus_restrictFunctor_mapDerivedCategory W.isoSpec.inv F hF)
  intro n
  refine Stacks.Descent.isQuasicoherent_of_restrictFunctor_zariski
    (fun _ : PUnit.{u + 1} => W.isoSpec.inv)
    (by simpa using Scheme.Hom.opensRange_of_isIso W.isoSpec.inv) _ fun _ => ?_
  refine (SheafOfModules.isQuasicoherent (Spec Γ(W, ⊤)).ringCatSheaf).prop_of_iso
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor W.isoSpec.inv) n).app _) ?_
  exact (SheafOfModules.isQuasicoherent (Spec Γ(W, ⊤)).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      (Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso W.isoSpec.inv E F)).symm (h.2 n)

/-- **Stacks Project, Tag 0A6H, part (1).** Let `Y` be a scheme, let `E` be a pseudo-coherent
object of `D(𝒪_Y)` and let `F` be an object of `D⁺_QCoh(𝒪_Y)`. Then the derived internal Hom
`R𝓗om_{𝒪_Y}(E, F)` lies in `D_QCoh(𝒪_Y)`: all of its cohomology sheaves are quasi-coherent.

The affine opens of `Y` cover it, so by the locality of quasi-coherence it is enough to see that
each cohomology sheaf restricts to a quasi-coherent module on every affine open `U`. Restriction
along `U.ι` commutes with the derived internal Hom by [Stacks, Tag 08DL], keeps `E`
pseudo-coherent by [Stacks, Tag 08CC] and keeps `F` in `D⁺_QCoh`, so the restriction is the
derived internal Hom of the restrictions on the affine scheme `U`, where
`derivedCategoryB_derivedSheafHom_of_isPseudoCoherent_of_isAffine` applies. -/
@[stacks 0A6H "part (1) on an arbitrary scheme: the derived internal Hom out of a \
pseudo-coherent object into an object of D⁺_QCoh has quasi-coherent cohomology sheaves"]
theorem derivedCategoryB_derivedSheafHom_of_isPseudoCoherent (Y : Scheme.{u})
    (E F : DerivedCategory (StructureSheafModules Y.sheaf))
    (hE : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) E)
    (hF : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj F) := by
  intro n
  refine Stacks.Descent.isQuasicoherent_of_restrictFunctor_zariski
    (fun U : Y.affineOpens => (U : Y.Opens).ι)
    (by simpa only [Scheme.Opens.opensRange_ι] using iSup_affineOpens_eq_top Y) _ fun U => ?_
  have := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := Y.ringCatSheaf) (U : Y.Opens)
  have := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := Y.ringCatSheaf) (U : Y.Opens)
  have : IsAffine (U : Y.Opens).toScheme := U.2
  have hres := derivedCategoryB_derivedSheafHom_of_isPseudoCoherent_of_isAffine
    (U : Y.Opens).toScheme
    ((Scheme.Modules.restrictFunctor (U : Y.Opens).ι).mapDerivedCategory.obj E)
    ((Scheme.Modules.restrictFunctor (U : Y.Opens).ι).mapDerivedCategory.obj F)
    ((RingedSpace.isPseudoCoherent_derivedRestrictModules E hE (U : Y.Opens)).of_iso
      ((RingedSpace.derivedRestrictModulesIsoRestrictFunctor Y (U : Y.Opens)).app E))
    (derivedCategoryBPlus_restrictFunctor_mapDerivedCategory (U : Y.Opens).ι F hF)
  refine (SheafOfModules.isQuasicoherent (U : Y.Opens).toScheme.ringCatSheaf).prop_of_iso
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor (U : Y.Opens).ι) n).app _) ?_
  exact (SheafOfModules.isQuasicoherent (U : Y.Opens).toScheme.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      (Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso (U : Y.Opens) E F)).symm
    (hres n)

end AlgebraicGeometry

end
