module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCoveringFpqc
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteFiniteLocallyFreeAgreement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Finite local freeness of `𝓕ᵃ` on the small étale site

Descent, Lemma 05VG asserts, for each of the properties of modules of Modules on Sites,
Definitions 03DE, 03DL and 03ER, that a quasi-coherent `𝒪_S`-module `𝓕` has the property if and
only if `𝓕ᵃ` has it as an `𝒪`-module on the site. This file proves the two implications for
finite local freeness, Definition 03DL (2), at the small étale site `S_étale`, for `𝓕`
quasi-coherent.

## Main definitions

* `AlgebraicGeometry.SmallEtale.objRestrictFunctorUnitIso`: the crossover of Stacks 06WI at the
  small étale site carries the structure sheaf of the localization at `U` to the structure sheaf
  of the small étale site of the scheme of `U`.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_isColimitCofan_associatedModuleOver`: a finite free cofan
  of `𝓕|_V` gives one of `(𝓕ᵃ)|_{V_étale}`.
* `AlgebraicGeometry.SmallEtale.isFiniteFree_objRestrict`: the crossover restriction to the small
  étale site of the scheme of `U` carries a finite free module to a finite free module.
* `AlgebraicGeometry.SmallEtale.isFiniteFree_pullback_of_isFiniteFree_over`: the pullback of `𝓕`
  along the structure morphism of `U` is finite free when the restriction of `𝓕ᵃ` to `U` is.
* `SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_of_isFiniteLocallyFreeOnSite`:
  if `𝓕` is finite locally free, so is `𝓕ᵃ`.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_of_associatedModule`: if `𝓕` is
  quasi-coherent and `𝓕ᵃ` is finite locally free, so is `𝓕`.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The pullback direction -/

/-- **A finite free cofan of `𝓕|_V` gives a finite free cofan of `(𝓕ᵃ)|_{V_étale}`.** -/
public theorem exists_isColimitCofan_associatedModuleOver (V : S.Opens) (𝓕 : S.Modules)
    (h : ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit (S.ringCatSheaf.over V) ⟶
        SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V,
      Nonempty (IsColimit (Cofan.mk (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V) ι))) :
    ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit ((structureSheaf B S hS).over ((opensToSmallEtale B S hS).obj V)) ⟶
        ((associatedModule B S hS).obj 𝓕).over ((opensToSmallEtale B S hS).obj V),
      Nonempty (IsColimit (Cofan.mk
        (((associatedModule B S hS).obj 𝓕).over ((opensToSmallEtale B S hS).obj V)) ι)) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := h
  have : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)) :=
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (sliceStructureMap B S hS V)).leftAdjoint_preservesColimits
  let Φ := SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)
  let u := asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V))
  let e := associatedModuleOverObjIso B S hS V 𝓕
  exact ⟨n, fun b => (u.inv ≫ Φ.map (ι b)) ≫ e.hom,
    ⟨(Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap Φ u ι hc).ofIsoColimit
      (Cocone.ext e (fun _ => rfl))⟩⟩

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2): the pullback direction, at
the small étale site.** If an `𝒪_S`-module `𝓕` is finite locally free on the small Zariski site
of `S`, then its associated module `𝓕ᵃ` is finite locally free as an `𝒪`-module on `S_étale`. -/
public theorem isFiniteLocallyFreeOnSite_associatedModule_of_isFiniteLocallyFreeOnSite
    (𝓕 : S.Modules)
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite (R := S.ringCatSheaf) 𝓕) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      ((AlgebraicGeometry.SmallEtale.associatedModule B S hS).obj 𝓕) := by
  obtain ⟨I, V, hV, hfree⟩ :=
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
      S.zariskiRingedSite 𝓕).1 h
  exact (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
    (smallEtaleRingedSite B S hS) ((associatedModule B S hS).obj 𝓕)).2
      ⟨ULift.{u + 1} I, fun i => (opensToSmallEtale B S hS).obj (V i.down),
        coversTop_opensToSmallEtale_ulift B S hS V hV,
        fun i => exists_isColimitCofan_associatedModuleOver B S hS (V i.down) 𝓕 (hfree i.down)⟩

/-! ### The descent direction -/

section Object

variable (U : SmallEtale B S hS)

/-- The crossover of Stacks 06WI carries the structure sheaf of the localization of `S_étale` at
`U` to the structure sheaf of the small étale site of the scheme of `U`. -/
public def objRestrictFunctorUnitIso :
    (objRestrictFunctor B S hS U).obj
        (SheafOfModules.unit ((structureSheaf B S hS).over U)) ≅
      SheafOfModules.unit
        (structureSheaf B (objScheme B S hS U) (contains_objScheme B S hS U)) :=
  Iso.refl _

/-- **Finite freeness of the restriction of `𝒢` to the localization of `S_étale` at `U` is finite
freeness of its crossover restriction to the small étale site of the scheme of `U`.** -/
public theorem isFiniteFree_objRestrict (𝒢 : SheafOfModules.{u} (structureSheaf B S hS))
    (h : SheafOfModules.IsFiniteFree ((structureSheaf B S hS).over U) (𝒢.over U)) :
    SheafOfModules.IsFiniteFree
      (structureSheaf B (objScheme B S hS U) (contains_objScheme B S hS U))
      ((objRestrict B S hS U).obj 𝒢) := by
  rw [SheafOfModules.isFiniteFree_iff_exists_isColimit] at h ⊢
  obtain ⟨n, ι, ⟨hc⟩⟩ := h
  exact ⟨n, _, ⟨Stacks.SheafOfModules.isColimitCofanTransport
    (objRestrictEquivalence B S hS U) (objRestrictFunctorUnitIso B S hS U) (Iso.refl _) ι hc⟩⟩

/-- **The pullback of `𝓕` along the structure morphism of `U` is finite free as soon as the
restriction of `𝓕ᵃ` to the localization of `S_étale` at `U` is.** -/
public theorem isFiniteFree_pullback_of_isFiniteFree_over (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent]
    (h : SheafOfModules.IsFiniteFree ((structureSheaf B S hS).over U)
      (((associatedModule B S hS).obj 𝓕).over U)) :
    SheafOfModules.IsFiniteFree (objScheme B S hS U).ringCatSheaf
      ((Scheme.Modules.pullback (objHom B S hS U)).obj 𝓕) :=
  (isFiniteFree_iff_associatedModule B (objScheme B S hS U) (contains_objScheme B S hS U)
    ⟨(Scheme.Modules.pullback (objHom B S hS U)).obj 𝓕,
      Stacks.Modules.isQuasicoherent_pullback _ 𝓕 h𝓕⟩).2
    (Stacks.SheafOfModules.isFiniteFree_of_iso
      (associatedModuleObjRestrictObjIso B S hS U 𝓕).symm
      (isFiniteFree_objRestrict B S hS U ((associatedModule B S hS).obj 𝓕) h))

end Object

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2): the descent direction, at
the small étale site.** If the associated module `𝓕ᵃ` of a quasi-coherent `𝒪_S`-module is finite
locally free as an `𝒪`-module on `S_étale`, then `𝓕` is finite locally free on the small Zariski
site of `S`. -/
public theorem isFiniteLocallyFreeOnSite_of_associatedModule (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent]
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite ((associatedModule B S hS).obj 𝓕)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (R := S.ringCatSheaf) 𝓕 := by
  classical
  obtain ⟨I, X, hX, hfree⟩ :=
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
      (smallEtaleRingedSite B S hS) ((associatedModule B S hS).obj 𝓕)).1 h
  let 𝒰 : S.Cover.{u + 1} Scheme.fpqcPrecoverage :=
    ⟨coveringHypercover B S hS X, presieve₀_mem_fpqcPrecoverage_coveringHypercover B S hS X hX⟩
  have key : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (𝒰.f i)).obj 𝓕) := fun i =>
    AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteFree _
      (isFiniteFree_pullback_of_isFiniteFree_over B S hS (X i) 𝓕
        ((SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).2 (hfree i)))
  exact Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree 𝓕
    (isFiniteLocallyFree_of_pullback_fpqcCover 𝓕 𝒰 key)

end AlgebraicGeometry.SmallEtale

end
