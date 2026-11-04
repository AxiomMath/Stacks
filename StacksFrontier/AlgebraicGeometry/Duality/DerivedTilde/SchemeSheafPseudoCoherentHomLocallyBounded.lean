module

public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import
  StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow
import StacksCore.Tactic.StacksAttribute

/-!
# The local lower bound of part (1) of Tag 0A6H

For `E` pseudo-coherent in `D(𝒪_Y)` and `F` in `D⁺_QCoh(𝒪_Y)` on a scheme `Y`, the derived
internal Hom `R𝓗om_{𝒪_Y}(E, F)` is locally bounded below. Its quasi-coherence, the other half of
part (1) of [Stacks, Tag 0A6H], is
`AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent`.

No uniform bound holds: each affine open has a bound of its own, and on a scheme that is not
quasi-compact the family of bounds need not be bounded.

## Main results

* `AlgebraicGeometry.isZero_of_isZero_restrictFunctor_inv` and
  `AlgebraicGeometry.isBoundedBelow_of_isBoundedBelow_restrictFunctor_inv`: restriction of
  modules along an isomorphism of schemes reflects vanishing, hence reflects boundedness below.
* `AlgebraicGeometry.derivedCategoryBPlus_derivedSheafHom_of_isPseudoCoherent_of_isAffine`: on an
  affine scheme `W`, `R𝓗om_{𝒪_W}(E, F)` lies in `D⁺_QCoh(𝒪_W)`.
* `AlgebraicGeometry.isLocallyBoundedBelow_derivedSheafHom_of_isPseudoCoherent`: on an arbitrary
  scheme `Y`, `R𝓗om_{𝒪_Y}(E, F)` is locally bounded below.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules

/-- Restriction of modules along an isomorphism of schemes reflects vanishing: a module whose
restriction is a zero object is a zero object. -/
theorem isZero_of_isZero_restrictFunctor_inv {Y Z : Scheme.{u}} (e : Y ≅ Z) (M : Y.Modules)
    (h : IsZero ((Scheme.Modules.restrictFunctor e.inv).obj M)) : IsZero M :=
  ((Scheme.Modules.restrictFunctor e.inv).inv.map_isZero h).of_iso
    ((Scheme.Modules.restrictFunctor e.inv).asEquivalence.unitIso.app M)

/-- Restriction of modules along an isomorphism of schemes reflects boundedness below: an object
of the derived category whose restriction is bounded below is bounded below. -/
theorem isBoundedBelow_of_isBoundedBelow_restrictFunctor_inv {Y Z : Scheme.{u}} (e : Y ≅ Z)
    (K : DerivedCategory Y.Modules)
    (h : DerivedCategoryB.IsBoundedBelow
      ((Scheme.Modules.restrictFunctor e.inv).mapDerivedCategory.obj K)) :
    DerivedCategoryB.IsBoundedBelow K := by
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨n₀, fun m hm => isZero_of_isZero_restrictFunctor_inv e _ ?_⟩
  exact (hn₀ m hm).of_iso
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor e.inv) m).app K).symm

/-- For `E` a pseudo-coherent object of `D(𝒪_W)` on an affine scheme `W` and `F` an object of
`D⁺_QCoh(𝒪_W)`, the derived internal Hom `R𝓗om_{𝒪_W}(E, F)` lies in `D⁺_QCoh(𝒪_W)`: its
cohomology sheaves are quasi-coherent and vanish in sufficiently negative degrees. -/
theorem derivedCategoryBPlus_derivedSheafHom_of_isPseudoCoherent_of_isAffine (W : Scheme.{u})
    [IsAffine W] (E F : DerivedCategory (StructureSheafModules W.sheaf))
    (hE : RingedSpace.IsPseudoCoherent (X := W.toRingedSpace) E)
    (hF : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent W.ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryBPlus (SheafOfModules.isQuasicoherent W.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj (op E)).obj F) := by
  have h := derivedCategoryBPlus_affineDerivedSheafHom_of_isPseudoCoherent_of_derivedCategoryBPlus
    Γ(W, ⊤) _
    (Scheme.Modules.isPseudoCoherent_restrictFunctor_mapDerivedCategory_of_isIso
      W.isoSpec.inv E hE) _
    (derivedCategoryBPlus_restrictFunctor_mapDerivedCategory W.isoSpec.inv F hF)
  refine ⟨isBoundedBelow_of_isBoundedBelow_restrictFunctor_inv W.isoSpec _ ?_,
    derivedCategoryB_derivedSheafHom_of_isPseudoCoherent_of_isAffine W E F hE hF⟩
  exact DerivedCategoryB.isBoundedBelow_of_iso
    (Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso W.isoSpec.inv E F).symm h.1

/-- Let `Y` be a scheme, let `E` be a pseudo-coherent object of `D(𝒪_Y)` and let `F` be an
object of `D⁺_QCoh(𝒪_Y)`. Then `R𝓗om_{𝒪_Y}(E, F)` is locally bounded below: every point of `Y`
has an open neighbourhood over which the cohomology sheaves vanish in all sufficiently negative
degrees. -/
@[stacks 0A6H "part (1) on an arbitrary scheme: the derived internal Hom out of a \
pseudo-coherent object into an object of D⁺_QCoh is locally bounded below"]
theorem isLocallyBoundedBelow_derivedSheafHom_of_isPseudoCoherent (Y : Scheme.{u})
    (E F : DerivedCategory (StructureSheafModules Y.sheaf))
    (hE : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) E)
    (hF : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) F) :
    RingedSpace.IsLocallyBoundedBelow Y.toRingedSpace
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj F) := by
  refine (RingedSpace.isLocallyBoundedBelow_iff_forall_exists_isBoundedBelow
    Y.toRingedSpace _).2 fun x => ?_
  obtain ⟨U, hxU⟩ := Opens.mem_iSup.1
    (iSup_affineOpens_eq_top Y ▸ trivial : x ∈ ⨆ U : Y.affineOpens, (U : Y.Opens))
  refine ⟨(U : Y.Opens), hxU, ?_⟩
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := Y.ringCatSheaf) (U : Y.Opens)
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := Y.ringCatSheaf) (U : Y.Opens)
  let _ : IsAffine (U : Y.Opens).toScheme := U.2
  have hres := derivedCategoryBPlus_derivedSheafHom_of_isPseudoCoherent_of_isAffine
    (U : Y.Opens).toScheme
    ((Scheme.Modules.restrictFunctor (U : Y.Opens).ι).mapDerivedCategory.obj E)
    ((Scheme.Modules.restrictFunctor (U : Y.Opens).ι).mapDerivedCategory.obj F)
    ((RingedSpace.isPseudoCoherent_derivedRestrictModules E hE (U : Y.Opens)).of_iso
      ((RingedSpace.derivedRestrictModulesIsoRestrictFunctor Y (U : Y.Opens)).app E))
    (derivedCategoryBPlus_restrictFunctor_mapDerivedCategory (U : Y.Opens).ι F hF)
  exact DerivedCategoryB.isBoundedBelow_of_iso
    ((Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso (U : Y.Opens) E F).symm ≪≫
      ((RingedSpace.derivedRestrictModulesIsoRestrictFunctor Y (U : Y.Opens)).app _).symm) hres.1

end AlgebraicGeometry

end
