module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationOverMapObj
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModulePairFunctor
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModulePushforward
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.TransitionRingedSite
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.UnitTransition
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.CocontinuousSliceTransition
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.SliceTransitionIso

/-!
# Quasi-coherent modules on the total site of a simplicial site of case (B)

For a simplicial site of case (B) (Stacks 09WE), whose transitions are given by cocontinuous
functors `v_φ : C_n ⥤ C_m`, and a sheaf of commutative rings `O` on its total site, the two halves
of Stacks 0D7M that need a localization of the total site:

* a quasi-coherent module `F` is cartesian: the transition `f_φ^*F_m ⟶ F_n` is the transposed
  transition of restrictions along the component inclusions and the arrows `G_n(V) ⟶ G_m(v_φ V)`
  of the total site, and it is invertible on the slices `C_n/V` over the objects `V` with `F`
  globally presented on `G_m(v_φ V)`, which cover `C_n` by cocontinuity of `G_m` and `v_φ`;
* a cartesian module whose components are quasi-coherent is quasi-coherent: a global
  presentation of `F_n` on `C_n/V` lifts to a module `P` on `C_{total}/G_n(V)` with a global
  presentation and a map `c : P ⟶ F|_{G_n(V)}` invertible on `C_n/V`; every object of
  `C_{total}/G_n(V)` is an arrow `G_k(W) ⟶ G_n(v_ψ W) ⟶ G_n(V)`, and the cartesian property
  makes `c` invertible there.

## Main results

In the namespace `CategoryTheory.CocontinuousSimplicialSite`:

* `isIso_fiberTransitionModules_of_isQuasicoherentOnSite_quasicoherentCartesianInl`: a
  quasi-coherent module on the total site is cartesian.
* `hasGlobalPresentation_over_componentFunctor_quasicoherentCartesianInl`: a cartesian module
  whose degree `n` component is globally presented on `C_n/V` is globally presented on
  `C_{total}/G_n(V)`.
* `isQuasicoherentOnSite_of_isCartesianModule_quasicoherentCartesianInl`: a cartesian module with
  quasi-coherent components is quasi-coherent.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward Opposite

universe u

namespace Stacks.AlgebraicGeometry.QcohRestrictEquiv

universe v₁ v₂ u₁ u₂ w

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}

/-- A component of the pushforward of a morphism of sheaves of modules along a site functor is
invertible exactly when the component of the morphism at the image object is: the two have the
same underlying morphism of abelian groups. The continuity of `F` is an explicit argument, so that
it is read off `ψ` by unification. -/
theorem isIso_pushforward_map_val_app_iff_quasicoherentCartesianInr
    (hF : Functor.IsContinuous F J K)
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    {M N : SheafOfModules.{w} R} (φ : M ⟶ N) (W : Cᵒᵖ) :
    IsIso (((SheafOfModules.pushforward.{w} ψ).map φ).val.app W) ↔
      IsIso (φ.val.app (op (F.obj W.unop))) := by
  refine (isIso_iff_of_reflects_iso _
    (forget₂ (ModuleCat.{w} (S.obj.obj W)) AddCommGrpCat.{w})).symm.trans
    (isIso_iff_of_reflects_iso (φ.val.app (op (F.obj W.unop)))
      (forget₂ (ModuleCat.{w} (R.obj.obj (op (F.obj W.unop)))) AddCommGrpCat.{w}))

end Stacks.AlgebraicGeometry.QcohRestrictEquiv

namespace CategoryTheory.CocontinuousSimplicialSite

variable (C : CocontinuousSimplicialSite.{u})
  (O : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology CommRingCat.{u})

/-- The component inclusion of degree `n` is continuous for the topology of the component ringed
site. -/
theorem isContinuous_componentFunctor_componentRingedSite_localizedTransition
    (n : SimplexCategory) :
    (SimplicialSiteSituation.componentFunctor
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).IsContinuous
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite O n).J
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology :=
  SimplicialSiteSituation.componentFunctor_isContinuous _ n

/-- The component inclusion of degree `n` is cocontinuous for the topology of the component
ringed site (Stacks 09WG). -/
theorem isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl
    (n : SimplexCategory) :
    (SimplicialSiteSituation.componentFunctor
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).IsCocontinuous
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite O n).J
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology :=
  SimplicialSiteSituation.componentFunctor_isCocontinuous _ n

/-- The transition functor `v_φ : C_n ⥤ C_m` of a simplex map `φ : m ⟶ n`, between the sites of
the component ringed sites. -/
abbrev transitionFunctorQuasicoherentCartesianInr {m n : SimplexCategory} (φ : m ⟶ n) :
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite O n).C ⥤
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite O m).C :=
  (C.underlying.map φ.op).toFunctor

/-- The transition functor is cocontinuous for the topologies of the component ringed sites. -/
theorem isCocontinuous_transitionFunctor_quasicoherentCartesianInr {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (C.transitionFunctorQuasicoherentCartesianInr O φ).IsCocontinuous
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite O n).J
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite O m).J :=
  C.isCocontinuous φ.op

/-- The structure map of the transition morphism of ringed topoi, in direct-image form. -/
noncomputable abbrev transitionFSharpQuasicoherentCartesianInr {m n : SimplexCategory} (φ : m ⟶ n) :
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite O m).O ⟶
      (pushforwardCommRingFunctor (RingedSite.cocontinuousToposHomCocontinuousMorphism
        (C.transitionFunctorQuasicoherentCartesianInr O φ)
        (C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O φ))).obj
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
          O n).O :=
  ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).transitionRingedToposHom O φ).fSharp

/-- The transition morphism of ringed topoi is the morphism given by the cocontinuous functor
`v_φ` and its structure map. -/
theorem cocontinuousRingedToposHom_eq_quasicoherentCartesianInr {m n : SimplexCategory}
    (φ : m ⟶ n) :
    RingedSite.cocontinuousRingedToposHomCocontinuousMorphism
        (C.transitionFunctorQuasicoherentCartesianInr O φ)
        (C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O φ)
        (C.transitionFSharpQuasicoherentCartesianInr O φ) =
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).transitionRingedToposHom O φ :=
  rfl

/-- The identity of the component ring sheaf, read as a ring map into the restriction of the
total ring sheaf. -/
noncomputable abbrev componentRingMapLocalizedTransition (n : SimplexCategory) :
    haveI := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
        O n).J)
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
        O n).O) ⟶
      ((SimplicialSiteSituation.componentFunctor
          (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).sheafPushforwardContinuous
        RingCat.{u}
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
          O n).J
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology).obj
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O) :=
  𝟙 _

/-- The arrows `G_n(V) ⟶ G_m(v_φ V)` of the total site, read between the component
inclusions. -/
noncomputable abbrev transitionArrowsLocalizedTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    SimplicialSiteSituation.componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n ⟶
      C.transitionFunctorQuasicoherentCartesianInr O φ ⋙
        SimplicialSiteSituation.componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m :=
  Grothendieck.ιNatTrans (F := C.underlying) φ.op

/-- **The ring compatibility of the transition data**: the structure map of `f_φ` is the
transition of the total ring sheaf. -/
theorem transitionRingCompatible_localizedTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    RingedSite.CocontinuousRingCompatibleCocontinuousSliceTransition
      (hv := C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O φ)
      (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
      (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O m)
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)
      (C.transitionFunctorQuasicoherentCartesianInr O φ)
      (C.transitionFSharpQuasicoherentCartesianInr O φ) (C.transitionArrowsLocalizedTransition O φ)
      (C.componentRingMapLocalizedTransition O n) (C.componentRingMapLocalizedTransition O m) := by
  have h := ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).transitionRingedToposHom_fSharpRing_forget
    O φ).symm
  refine ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
    ((Category.id_comp _).trans h)).trans ?_
  refine (Category.comp_id _).symm.trans (congrArg (_ ≫ ·) ?_)
  refine (Category.id_comp _).symm.trans (congrArg (_ ≫ ·) ?_)
  exact (CategoryTheory.Functor.map_id (RingedSite.cocontinuousToposHomCocontinuousMorphism
      (C.transitionFunctorQuasicoherentCartesianInr O φ)
      (C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O φ)).pushforward _).symm.trans
    (congrArg (RingedSite.cocontinuousToposHomCocontinuousMorphism
      (C.transitionFunctorQuasicoherentCartesianInr O φ)
      (C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O φ)).pushforward.map
      (CategoryTheory.Functor.map_id (sheafCompose _ (forget RingCat.{u})) _).symm)

/-- The transposed transition of restrictions of the case (B) data. -/
noncomputable abbrev siteTransitionPullbackQuasicoherentCartesianInr {m n : SimplexCategory}
    (φ : m ⟶ n) :=
  RingedSite.cocontinuousSiteTransitionPullbackCocontinuousSliceTransition
    (hv := C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O φ)
    (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
    (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O m)
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)
    (C.transitionFunctorQuasicoherentCartesianInr O φ)
    (C.transitionFSharpQuasicoherentCartesianInr O φ) (C.transitionArrowsLocalizedTransition O φ)
    (C.componentRingMapLocalizedTransition O n) (C.componentRingMapLocalizedTransition O m)
    (C.transitionRingCompatible_localizedTransition O φ)

/-- **The transposed transition of restrictions is the transition of Stacks 09WF**, up to
invertibility: at every module the two are invertible together. -/
theorem isIso_siteTransitionPullback_app_iff_localizedTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{u} ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)) :
    IsIso ((C.siteTransitionPullbackQuasicoherentCartesianInr O φ).app F) ↔
      IsIso ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).fiberTransitionModules O φ F) := by
  have e := RingedSite.cocontinuousSiteTransitionPullback_app_cocontinuousSliceTransition
    (hv := C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O φ)
    (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
    (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O m)
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)
    (C.transitionFunctorQuasicoherentCartesianInr O φ)
    (C.transitionFSharpQuasicoherentCartesianInr O φ) (C.transitionArrowsLocalizedTransition O φ)
    (C.componentRingMapLocalizedTransition O n) (C.componentRingMapLocalizedTransition O m)
    (C.transitionRingCompatible_localizedTransition O φ) F
  exact (iff_of_eq (congrArg IsIso e)).trans
    (RingedToposHom.isIso_homEquiv_symm_iff_of_eq _
      (C.cocontinuousRingedToposHom_eq_quasicoherentCartesianInr O φ)
      rfl rfl _ _ HEq.rfl)

/-- The transposed transition of restrictions is invertible at the structure sheaf. -/
theorem isIso_siteTransitionPullback_app_unit_quasicoherentCartesianInl {m n : SimplexCategory}
    (φ : m ⟶ n) :
    IsIso ((C.siteTransitionPullbackQuasicoherentCartesianInr O φ).app (SheafOfModules.unit _)) :=
  (C.isIso_siteTransitionPullback_app_iff_localizedTransition O φ _).mpr
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).isIso_fiberTransitionModules_unit_unitTransition
      O φ)

/-- **A quasi-coherent module is cartesian**, the second half of the forward implication of
Stacks 0D7M in case (B). -/
theorem isIso_fiberTransitionModules_of_isQuasicoherentOnSite_quasicoherentCartesianInl
    (F : SheafOfModules.{u} ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O))
    (hF : F.IsQuasicoherentOnSite) {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).fiberTransitionModules O φ F) := by
  refine (C.isIso_siteTransitionPullback_app_iff_localizedTransition O φ F).mp ?_
  refine
    RingedSite.isIso_cocontinuousSiteTransitionPullback_app_of_locally_cocontinuousSliceTransition
    (hv := C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O φ)
    (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
    (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O m)
    (hGc := C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl O n)
    (hG'c := C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl O m)
    _ _ _ _ _ _ _
    (C.isIso_siteTransitionPullback_app_unit_quasicoherentCartesianInl O φ) F fun U ↦ ?_
  obtain ⟨I, V, f, hcov, hpres⟩ := hF.locally_hasGlobalPresentation
    ((SimplicialSiteSituation.componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m).obj
      ((C.transitionFunctorQuasicoherentCartesianInr O φ).obj U))
  refine ⟨(((Sieve.ofArrows V f).functorPullback
    (SimplicialSiteSituation.componentFunctor
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m)).functorPullback
      (C.transitionFunctorQuasicoherentCartesianInr O φ)).arrows, ?_, fun W g hg ↦ ?_⟩
  · exact GrothendieckTopology.superset_covering _ (fun Y g hg ↦ Sieve.le_generate _ Y g hg)
      ((C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O φ).cover_lift
        ((C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl
          O m).cover_lift hcov))
  · obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    exact Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap F a
      (hpres i)

/-- A map `c : P ⟶ F|_{G_n(V)}` invertible on `C_n/V` stays invertible on `C_n/U` after
restriction along `G_n(f)` for `f : U ⟶ V`. -/
theorem isIso_pushforward_overMap_map_quasicoherentCartesianInl {n : SimplexCategory}
    {U V : ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
      O n).C}
    (f : U ⟶ V)
    (F : SheafOfModules.{u} ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)) :
    haveI := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n
    haveI := RingedSite.Hom.isContinuous_sliceLeft
      (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n) U
    haveI := RingedSite.Hom.isContinuous_sliceLeft
      (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n) V
    ∀ {P : SheafOfModules.{u} (RingedSite.Hom.sliceRing
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O) V)}
      (c : P ⟶ (restrictionModules ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology.over
          ((SimplicialSiteSituation.componentFunctor
            (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).obj V))
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
        (Over.forget ((SimplicialSiteSituation.componentFunctor
          (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).obj V))
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)).obj F),
      IsIso ((SheafOfModules.pushforward (RingedSite.Hom.sliceRingMapLeft
        (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O) V
          (C.componentRingMapLocalizedTransition O n))).map c) →
      IsIso ((SheafOfModules.pushforward (RingedSite.Hom.sliceRingMapLeft
        (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O) U
          (C.componentRingMapLocalizedTransition O n))).map
        ((SheafOfModules.overMap ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)
          ((SimplicialSiteSituation.componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
            n).map f)).map c)) := by
  open Stacks.AlgebraicGeometry.QcohRestrictEquiv in
  intro P c hc
  refine isIso_of_isIso_val_app _ fun Z ↦ ?_
  induction Z using Opposite.rec with | op Z => ?_
  refine (isIso_pushforward_map_val_app_iff_quasicoherentCartesianInr _ _ _ _).mpr
    ((isIso_pushforward_map_val_app_iff_quasicoherentCartesianInr _ _ c _).mpr ?_)
  refine isIso_val_app_congr c ?_
    ((isIso_pushforward_map_val_app_iff_quasicoherentCartesianInr _ _ c _).mp
      (@isIso_val_app _ _ _ _ _ _ _ hc
        (op (Over.mk (Z.hom ≫ f)))))
  exact congrArg op (congrArg Over.mk
    ((SimplicialSiteSituation.componentFunctor
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).map_comp Z.hom f))

/-- **The cartesian property propagates invertibility from `C_n/V` to `C_{total}/G_n(V)`.** If `F`
is cartesian, a map `c : P ⟶ F|_{G_n(V)}` from a globally presented module that is invertible on
`C_n/V` is invertible. -/
theorem isIso_of_isIso_pushforward_map_quasicoherentCartesianInl
    (F : SheafOfModules.{u} ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O))
    (hF : (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).IsCartesianModule O F) {n : SimplexCategory}
    (V : ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
      O n).C) :
    haveI := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n
    haveI := RingedSite.Hom.isContinuous_sliceLeft
      (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n) V
    ∀ {P : SheafOfModules.{u} (RingedSite.Hom.sliceRing
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O) V)}
      (c : P ⟶ (restrictionModules ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology.over
          ((SimplicialSiteSituation.componentFunctor
            (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).obj V))
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
        (Over.forget ((SimplicialSiteSituation.componentFunctor
          (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).obj V))
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)).obj F),
      P.HasGlobalPresentation →
      IsIso ((SheafOfModules.pushforward (RingedSite.Hom.sliceRingMapLeft
        (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O) V
          (C.componentRingMapLocalizedTransition O n))).map c) → IsIso c := by
  open Stacks.AlgebraicGeometry.QcohRestrictEquiv
    Stacks.SheafOfModules.GlobalPresentationTransport in
  intro P c hP hc
  refine isIso_of_isIso_val_app c fun Z ↦ ?_
  induction Z using Opposite.rec with | op Z => ?_
  obtain ⟨⟨Zb, Zf⟩, ⟨⟨⟩⟩, b⟩ := Z
  induction Zb using Opposite.rec with | op k => ?_
  let b' : (⟨op k, Zf⟩ : Grothendieck C.underlying) ⟶ ⟨op n, V⟩ := b
  let ψ : n ⟶ k := b'.base.unop
  let W : ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
    O k).C := Zf
  let fib : (C.transitionFunctorQuasicoherentCartesianInr O ψ).obj W ⟶ V := b'.fiber
  let g := (SimplicialSiteSituation.componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
    n).map fib
  let c' := (SheafOfModules.overMap ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)
    g).map c
  have := (C.isIso_siteTransitionPullback_app_iff_localizedTransition O ψ F).mpr (hF ψ)
  have h := RingedSite.isIso_cocontinuousSliceRight_map_of_isIso_cocontinuousSliceTransition
    (hv := C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O ψ)
    (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O k)
    (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)
    (C.transitionFunctorQuasicoherentCartesianInr O ψ)
    (C.transitionFSharpQuasicoherentCartesianInr O ψ) (C.transitionArrowsLocalizedTransition O ψ)
    (C.componentRingMapLocalizedTransition O k)
    (C.componentRingMapLocalizedTransition O n)
    (C.transitionRingCompatible_localizedTransition O ψ) W c'
    (C.isIso_pushforward_overMap_map_quasicoherentCartesianInl O fib F c hc) ?hP ?hN
  case hP =>
    exact RingedSite.isIso_cocontinuousSliceTransitionPullback_app_of_hasGlobalPresentation_cocontinuousSliceTransition
      (hv := C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O ψ)
      (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O k)
      (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
      (hGc := C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl O k)
      (hG'c := C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl O n)
      _ _ _ _ _ _ _ W
      (C.isIso_siteTransitionPullback_app_unit_quasicoherentCartesianInl O ψ)
      (hasGlobalPresentation_overMap_obj_globalPresentationOverMapObj g P hP)
  case hN =>
    refine (NatTrans.isIso_app_iff_of_iso _ ((SheafOfModules.overFunctorMap
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O) g).app F)).mpr ?_
    exact (RingedSite.isIso_cocontinuousSliceTransitionPullback_app_iff_cocontinuousSliceTransition
      (hv := C.isCocontinuous_transitionFunctor_quasicoherentCartesianInr O ψ)
      (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O k)
      (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
      _ _ _ _ _ _ _ W F).mpr (Functor.map_isIso _ _)
  refine isIso_val_app_congr c ?_
    ((isIso_pushforward_map_val_app_iff_quasicoherentCartesianInr _ _ c _).mp
      ((isIso_pushforward_map_val_app_iff_quasicoherentCartesianInr _ _ c' _).mp
        (@isIso_val_app _ _ _ _ _ _ _ h
          (op (Over.mk (𝟙 W))))))
  have hb : ((SimplicialSiteSituation.componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
      k).map (𝟙 W) ≫ (C.transitionArrowsLocalizedTransition O ψ).app W) ≫ g = b := by
    refine (congrArg (· ≫ g) ((congrArg (· ≫ (C.transitionArrowsLocalizedTransition O ψ).app W)
      ((SimplicialSiteSituation.componentFunctor
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) k).map_id W)).trans
        (Category.id_comp _))).trans ?_
    exact Grothendieck.ιNatTrans_app_comp_ι_map _ _
  exact congrArg (fun t ↦ op (Over.mk t)) hb

/-- **A cartesian module is globally presented wherever its component is.** If `F` is cartesian
and the restriction of `F_n` to `C_n/V` has a global presentation, then so does the restriction
of `F` to `C_{total}/G_n(V)`: the presentation lifts to a globally presented `P` with a map
`c : P ⟶ F|_{G_n(V)}` invertible on `C_n/V`. An object of `C_{total}/G_n(V)` is an arrow
`G_k(W) ⟶ G_n(v_ψ W) ⟶ G_n(V)`; restricting `c` along the second arrow, the cartesian property
at `ψ` makes it invertible on `C_k/W`, in particular at the object itself. -/
theorem hasGlobalPresentation_over_componentFunctor_quasicoherentCartesianInl
    (F : SheafOfModules.{u} ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O))
    (hF : (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).IsCartesianModule O F) {n : SimplexCategory}
    (V : ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
      O n).C)
    (hV : (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentModule O F n).over
      V).HasGlobalPresentation) :
    (F.over ((SimplicialSiteSituation.componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
      n).obj V)).HasGlobalPresentation := by
  obtain ⟨P, c, hP, hc⟩ := RingedSite.exists_hasGlobalPresentation_isIso_sliceLeft_map
    (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
    (hG'c := C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl O n)
    _ (C.componentRingMapLocalizedTransition O n)
    (IsIso.id _) V F hV
  exact SheafOfModules.HasGlobalPresentation.of_iso (@asIso _ _ _ _ c
    (C.isIso_of_isIso_pushforward_map_quasicoherentCartesianInl O F hF V c hP hc)) hP

/-- **A cartesian module with quasi-coherent components is quasi-coherent**, the converse
implication of Stacks 0D7M in case (B). An object of degree `n` of the total site is covered by
the images of a covering of `C_n` on whose members `F_n` is globally presented, and on each of
them `F` is globally presented by
`hasGlobalPresentation_over_componentFunctor_quasicoherentCartesianInl`. -/
theorem isQuasicoherentOnSite_of_isCartesianModule_quasicoherentCartesianInl
    (F : SheafOfModules.{u} ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O))
    (hF : (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).IsCartesianModule O F)
    (hn : ∀ n : SimplexCategory,
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentModule O F n).IsQuasicoherentOnSite) :
    F.IsQuasicoherentOnSite := by
  refine ⟨fun X ↦ ?_⟩
  let X' : Grothendieck C.underlying := X
  obtain ⟨I, V, f, hcov, hpres⟩ := (hn X'.base.unop).locally_hasGlobalPresentation X'.fiber
  have hc := (@CoverPreserving.of_isContinuous _ _ _ _ (SimplicialSiteSituation.componentFunctor
    (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) X'.base.unop)
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentRingedTopos O X'.base.unop).J
    (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
    (C.isContinuous_componentFunctor_componentRingedSite_localizedTransition
      O X'.base.unop)).cover_preserve hcov
  refine ⟨I, _, fun i ↦ (SimplicialSiteSituation.componentFunctor
    (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) X'.base.unop).map (f i),
    GrothendieckTopology.superset_covering _ ?_ hc,
    fun i ↦ C.hasGlobalPresentation_over_componentFunctor_quasicoherentCartesianInl O F hF (V i)
      (hpres i)⟩
  rintro Y g ⟨Y', a, h, ha, rfl⟩
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp ha
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i, h ≫ (SimplicialSiteSituation.componentFunctor
    (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) X'.base.unop).map b,
      (congrArg (h ≫ ·) ((SimplicialSiteSituation.componentFunctor
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) X'.base.unop).map_comp b (f i))).trans
        (Category.assoc _ _ _).symm⟩

end CategoryTheory.CocontinuousSimplicialSite

end
