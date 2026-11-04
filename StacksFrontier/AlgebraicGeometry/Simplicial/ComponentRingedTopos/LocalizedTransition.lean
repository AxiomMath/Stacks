module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModulePushforward
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.TransitionRingedSite
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.UnitTransition
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.SliceTransition

/-!
# The transitions of a case (A) simplicial site as transitions of restrictions

For a simplicial site of case (A) (Stacks 09WE) and a sheaf of commutative rings `O` on its total
site, the transition `f_φ^*ℱ_m ⟶ ℱ_n` of Stacks 09WF is the transposed transition of
restrictions of modules attached to the morphism of ringed sites `f_φ`, the component
inclusions and the arrows `(φ, 𝟙)` of the total site. This puts the transitions in the setting
where they localize at slices.

## Main results

* `SimplicialSite.transitionRingCompatible_localizedTransition`: the ring compatibility of the
  transition data.
* `SimplicialSite.isIso_siteTransitionPullback_app_iff_localizedTransition`: the transposed
  transition of restrictions at a module is invertible exactly when the transition of Stacks 09WF
  is.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSite

variable (C : SimplicialSite.{u})
  (O : Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology CommRingCat.{u})

/-- The component inclusion of degree `n` is continuous for the topology of the component ringed
site. -/
theorem isContinuous_componentFunctor_componentRingedSite_localizedTransition
    (n : SimplexCategory) :
    (SimplicialSiteSituation.componentFunctor
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).IsContinuous
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite O n).J
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology :=
  SimplicialSiteSituation.componentFunctor_isContinuous _ n

/-- The identity of the component ring sheaf, read as a ring map into the restriction of the
total ring sheaf. -/
noncomputable abbrev componentRingMapLocalizedTransition (n : SimplexCategory) :
    haveI := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n
    (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
          O n).J)
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
          O n).O) ⟶
      ((SimplicialSiteSituation.componentFunctor
          (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).sheafPushforwardContinuous
        RingCat.{u}
          ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
            O n).J
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology).obj
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O) :=
  𝟙 _

/-- The arrows `(φ, 𝟙)` of the total site, read between the component inclusions. -/
noncomputable abbrev transitionArrowsLocalizedTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    (C.transitionRingedSiteHomTransitionRingedSite O φ).u ⋙
        SimplicialSiteSituation.componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n ⟶
      SimplicialSiteSituation.componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m :=
  SimplicialSiteSituation.continuousInclusionTransition C φ

/-- **The ring compatibility of the transition data**: the structure map of `f_φ` is the
restriction of the total ring sheaf along the arrows `(φ, 𝟙)`. -/
theorem transitionRingCompatible_localizedTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    (C.transitionRingedSiteHomTransitionRingedSite O φ).RingCompatible
      (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
      (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O m)
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)
      (C.transitionArrowsLocalizedTransition O φ)
      (C.componentRingMapLocalizedTransition O n) (C.componentRingMapLocalizedTransition O m) := by
  apply Sheaf.hom_ext
  ext W x
  exact (congrArg (fun g ↦ g.hom.app W x)
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionRingedToposHom_forgetFSharp O φ)).symm

/-- **The transposed transition of restrictions is the transition of Stacks 09WF**, up to
invertibility: at every module the two are invertible together. -/
theorem isIso_siteTransitionPullback_app_iff_localizedTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{u} ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)) :
    IsIso (((C.transitionRingedSiteHomTransitionRingedSite O φ).siteTransitionPullback
        (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
        (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O m)
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)
        (C.transitionArrowsLocalizedTransition O φ)
        (C.componentRingMapLocalizedTransition O n)
        (C.componentRingMapLocalizedTransition O m)
        (C.transitionRingCompatible_localizedTransition O φ)).app F) ↔
      IsIso ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).fiberTransitionModules O φ F) :=
  AlgebraicGeometry.RingedSite.Hom.isIso_siteTransitionPullback_app_iff
    (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
    (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O m) _ _ _ _ _
    (C.transitionRingCompatible_localizedTransition O φ) F
    (C.transitionRingedSiteHom_ringedToposHom_transitionRingedSite O φ) rfl rfl _ HEq.rfl

end CategoryTheory.SimplicialSite

end
