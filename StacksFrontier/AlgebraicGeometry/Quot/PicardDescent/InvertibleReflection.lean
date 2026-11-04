module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.CategoryTheory.Sites.Modules.InvertibleRankOneEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# Invertibility of a quasi-coherent module is detected on the small étale site

Let `S` be a scheme and let `𝓕` be a quasi-coherent `𝒪_S`-module.  If the associated module
`𝓕^a` on the small étale site of `S` is finite locally free of rank one, then `𝓕` is invertible.

The argument is the one of the reflection half of Stacks 05VG for finite local freeness, with
the rank kept.  The rank clause is local on a family `{U i}` covering the final object of
`S_étale`, over each member of which `𝓕^a` is a coproduct of one copy of the structure sheaf.
Read on the small étale site of the scheme `Y i` of `U i`, that restriction is the associated
module of the Zariski pullback `f_i^*𝓕` (Stacks 03DV), and an isomorphism of associated modules of
quasi-coherent modules descends (Stacks 03DX (2) at `τ = étale`), so `f_i^*𝓕` is isomorphic to
the free module of rank one and hence invertible.  The family `{Y i ⟶ S}` is an fpqc covering of
schemes, along which invertibility descends.

## Main results

* `AlgebraicGeometry.SmallEtale.isInvertible_of_isFiniteLocallyFreeOfRank_one_associatedModule`:
  a quasi-coherent module whose associated module on the small étale site has rank one is
  invertible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A sheaf of modules on a scheme isomorphic to the free module of rank one is finite locally
free of rank one on the small Zariski ringed site: the top open alone trivializes it. -/
theorem isFiniteLocallyFreeOfRank_one_of_iso_free {Y : Scheme.{u}} (M : Y.Modules)
    (e : _root_.SheafOfModules.free.{u} (R := Y.ringCatSheaf) (ULift.{u} (Fin 1)) ≅ M) :
    RingedSite.IsFiniteLocallyFreeOfRank Y.zariskiRingedSite M 1 := by
  obtain ⟨ι, ⟨hc⟩⟩ := Stacks.SheafOfModules.exists_isColimitCofan_of_iso_free e
  refine (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover_isColimit
    Y.zariskiRingedSite M 1).2
    ⟨PUnit.{u + 1}, fun _ => (⊤ : Y.Opens), Stacks.SheafOfModules.coversTop_top Y, fun _ => ?_⟩
  let T := _root_.SheafOfModules.overFunctor Y.ringCatSheaf (⊤ : Y.Opens)
  let : T.Additive := ⟨rfl⟩
  have hc' := (Cofan.isColimitMapCoconeEquiv T _ _).toFun (isColimitOfPreserves T hc)
  exact ⟨fun j => T.map (ι ⟨j⟩),
    ⟨(Cofan.isColimitEquivOfEquiv Equiv.ulift.symm _) hc'⟩⟩

/-- The Zariski pullback of `𝓕` to the scheme of an object `U` of the small étale site is
invertible as soon as `𝓕^a` is a coproduct of one copy of the structure sheaf on the slice at
`U`. -/
theorem isInvertible_pullback_objHom (𝓕 : S.Modules) [𝓕.IsQuasicoherent]
    (U : SmallEtale B S hS)
    (h : ∃ ι : ∀ _ : Fin 1, _root_.SheafOfModules.unit ((structureSheaf B S hS).over U) ⟶
        ((associatedModule B S hS).obj 𝓕).over U,
      Nonempty (IsColimit (Cofan.mk (((associatedModule B S hS).obj 𝓕).over U) ι))) :
    Stacks.SheafOfModules.IsInvertible (objScheme B S hS U).presheaf
      (objScheme B S hS U).ringCatSheaf.2
      ((Scheme.Modules.pullback (objHom B S hS U)).obj 𝓕) := by
  have hYc : B.Contains (objScheme B S hS U) := contains_objScheme B S hS U
  have hcross : ∃ ι : ∀ _ : Fin 1,
      _root_.SheafOfModules.unit (structureSheaf B (objScheme B S hS U) hYc) ⟶
        (objRestrict B S hS U).obj ((associatedModule B S hS).obj 𝓕),
      Nonempty (IsColimit (Cofan.mk
        ((objRestrict B S hS U).obj ((associatedModule B S hS).obj 𝓕)) ι)) :=
    Stacks.SheafOfModules.exists_isColimitCofan_reindex
      (localizationEquivalence B S hS U) ((structureSheaf B S hS).over U) _ h
  obtain ⟨ι, ⟨hc⟩⟩ := Stacks.SheafOfModules.exists_isColimitCofan_of_iso
    (associatedModuleObjRestrictObjIso B S hS U 𝓕).symm hcross
  have := Stacks.SheafOfModules.schemePullback_isQuasicoherent (objHom B S hS U) 𝓕
  let Y := objScheme B S hS U
  let P := (Scheme.Modules.pullback (objHom B S hS U)).obj 𝓕
  let I := ULift.{u} (Fin 1)
  let e : _root_.SheafOfModules.free.{u} (R := structureSheaf B Y hYc) I ≅
      (associatedModule B Y hYc).obj P :=
    (_root_.SheafOfModules.isColimitFreeCofan I).coconePointUniqueUpToIso
      ((Cofan.isColimitEquivOfEquiv Equiv.ulift (Cofan.mk _ ι)) hc)
  have := isEquivalence_associatedModuleQcohOnSite' B Y hYc
  let Pq : (_root_.SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
    ⟨P, inferInstance⟩
  let Fq : (_root_.SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
    ⟨_root_.SheafOfModules.free.{u} I,
      Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I⟩
  let eobj : (associatedModuleQcohOnSite B Y hYc).obj Fq ≅
      (associatedModuleQcohOnSite B Y hYc).obj Pq :=
    (ObjectProperty.ι _).preimageIso (associatedModuleFreeIso B Y hYc I ≪≫ e)
  exact RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one_of_essentiallySmall
    Y.zariskiRingedSite P (isFiniteLocallyFreeOfRank_one_of_iso_free P
      ((ObjectProperty.ι _).mapIso ((associatedModuleQcohOnSite B Y hYc).preimageIso eobj)))

/-- **Invertibility of a quasi-coherent module is detected by its associated module on the small
étale site.**  If `𝓕^a` is finite locally free of rank one on `S_étale`, then `𝓕` is invertible:
over the members of a family covering the final object of `S_étale` the Zariski pullbacks of `𝓕`
are free of rank one, and invertibility descends along the fpqc covering they form. -/
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one_associatedModule (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent]
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS)
      ((associatedModule B S hS).obj 𝓕) 1) :
    Stacks.SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 𝓕 := by
  obtain ⟨I, U, hU, hfree⟩ :=
    (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover_isColimit
      (smallEtaleRingedSite B S hS) ((associatedModule B S hS).obj 𝓕) 1).1 h
  exact Stacks.Picard.isInvertible_of_pullback_fpqcCover 𝓕 inferInstance
    { toPreZeroHypercover := coveringHypercover B S hS U
      mem₀ := presieve₀_mem_fpqcPrecoverage_coveringHypercover B S hS U hU }
    fun i => isInvertible_pullback_objHom B S hS 𝓕 (U i) (hfree i)

end AlgebraicGeometry.SmallEtale

end
