module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFinalPresentation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModulePairFunctor
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.LocalizedTransition
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.SliceTransitionIso

/-!
# Quasi-coherent modules on the total site of a simplicial site of case (A)

For a simplicial site of case (A) (Stacks 09WE) and a sheaf of commutative rings `O` on its total
site, the two halves of Stacks 0D7M that need a localization of the total site:

* a quasi-coherent module `F` is cartesian: for `φ : [m] → [n]` the transition
  `f_φ^*F_m ⟶ F_n` is invertible on the slices `C_n/u_φ(U)` over the objects `U` of `C_m` on
  which `F` has a global presentation, since there it is the transition of restrictions of a
  globally presented module, and these slices cover `C_n` by Stacks 08H2;
* a cartesian module whose components are quasi-coherent is quasi-coherent: a global
  presentation of `F_n` on `C_n/V` lifts to a module `P` on `C_{total}/V` with a global
  presentation and a map `c : P ⟶ F|_V` whose restriction to `C_n/V` is invertible, and the
  cartesian property makes `c` invertible on every slice `C_k/u_ψ(V)`, which together exhaust
  the objects of `C_{total}/V`.

## Main results

In the namespace `CategoryTheory.SimplicialSite`:

* `isIso_fiberTransitionModules_of_isQuasicoherentOnSite_quasicoherentCartesianInl`: a
  quasi-coherent module on the total site is cartesian.
* `hasGlobalPresentation_over_componentFunctor_quasicoherentCartesianInl`: a cartesian module is
  globally presented over `V` wherever its component `F_n` is globally presented on `C_n/V`.
* `isQuasicoherentOnSite_of_isCartesianModule_quasicoherentCartesianInl`: a cartesian module with
  quasi-coherent components is quasi-coherent.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 08H2](https://stacks.math.columbia.edu/tag/08H2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Sheaves.ToposPullback Opposite

universe u

namespace CategoryTheory.SimplicialSite

variable (C : SimplicialSite.{u})
  (O : Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology CommRingCat.{u})

/-- The component inclusion of degree `n` is cocontinuous for the topology of the component
ringed site (Stacks 09WG). -/
theorem isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl
    (n : SimplexCategory) :
    (SimplicialSiteSituation.componentFunctor
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).IsCocontinuous
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite O n).J
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology :=
  SimplicialSiteSituation.componentFunctor_isCocontinuous _ n

/-- The transposed transition of restrictions is invertible at the structure sheaf: this is the
cartesian property of the structure sheaf. -/
theorem isIso_siteTransitionPullback_app_unit_quasicoherentCartesianInl
    {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (((C.transitionRingedSiteHomTransitionRingedSite O φ).siteTransitionPullback
        (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
        (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O m)
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)
        (C.transitionArrowsLocalizedTransition O φ)
        (C.componentRingMapLocalizedTransition O n) (C.componentRingMapLocalizedTransition O m)
        (C.transitionRingCompatible_localizedTransition O φ)).app
      (SheafOfModules.unit _)) :=
  (C.isIso_siteTransitionPullback_app_iff_localizedTransition O φ _).mpr
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).isIso_fiberTransitionModules_unit_unitTransition
      O φ)

/-- **A quasi-coherent module is cartesian**, the second half of the forward implication of
Stacks 0D7M in case (A). -/
theorem isIso_fiberTransitionModules_of_isQuasicoherentOnSite_quasicoherentCartesianInl
    (F : SheafOfModules.{u} ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O))
    (hF : F.IsQuasicoherentOnSite) {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).fiberTransitionModules O φ F) := by
  refine (C.isIso_siteTransitionPullback_app_iff_localizedTransition O φ F).mp ?_
  refine RingedSite.Hom.isIso_siteTransitionPullback_app_of_locally
    (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
    (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O m)
    (hGc := C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl O n)
    (hG'c := C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl O m)
    _ _ _ _ _ _
    (C.isIso_siteTransitionPullback_app_unit_quasicoherentCartesianInl O φ) F fun U ↦ ?_
  obtain ⟨I, V, f, hcov, hpres⟩ := hF.locally_hasGlobalPresentation
    ((SimplicialSiteSituation.componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m).obj U)
  refine ⟨((Sieve.ofArrows V f).functorPullback
    (SimplicialSiteSituation.componentFunctor
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m)).arrows,
    ?_, fun W g hg ↦ ?_⟩
  · exact GrothendieckTopology.superset_covering _ (fun Y g hg ↦ Sieve.le_generate _ Y g hg)
      ((C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl
        O m).cover_lift hcov)
  · obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    exact Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap F a
      (hpres i)

/-- **A cartesian module is globally presented wherever its component is.** If `F` is cartesian
and the restriction of `F_n` to `C_n/V` has a global presentation, then so does the restriction
of `F` to `C_{total}/V`: the presentation lifts to a globally presented `P` with a map
`c : P ⟶ F|_V` invertible on `C_n/V`, and on each slice `C_k/u_ψ(V)` the cartesian property makes
`c` invertible as well; every object over `V` lies in one of those slices. -/
theorem hasGlobalPresentation_over_componentFunctor_quasicoherentCartesianInl
    (F : SheafOfModules.{u} ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O))
    (hF : (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).IsCartesianModule O F) {n : SimplexCategory}
    (V : ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite
      O n).C)
    (hV : (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentModule O F n).over
      V).HasGlobalPresentation) :
    (F.over ((SimplicialSiteSituation.componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})
      n).obj V)).HasGlobalPresentation := by
  obtain ⟨P, c, hP, hc⟩ := RingedSite.exists_hasGlobalPresentation_isIso_sliceLeft_map
    (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
    (hG'c := C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl O n)
    _ (C.componentRingMapLocalizedTransition O n)
    (IsIso.id _) V F hV
  have hcI : IsIso c := by
    refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app c fun Z ↦ ?_
    induction Z using Opposite.rec with | op Z => ?_
    obtain ⟨⟨Zb, Zf⟩, ⟨⟨⟩⟩, b⟩ := Z
    induction Zb using Opposite.rec with | op k => ?_
    let b' : (⟨op k, Zf⟩ : Pseudofunctor.CoGrothendieck C.totalPseudofunctor) ⟶ ⟨op n, V⟩ := b
    let ψ : n ⟶ k := b'.base.unop
    have hΘ := (C.isIso_siteTransitionPullback_app_iff_localizedTransition O ψ F).mpr (hF ψ)
    have hθF := ((C.transitionRingedSiteHomTransitionRingedSite
      O ψ).isIso_sliceTransitionPullback_app_iff
      (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O k)
      (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n) _
      (C.transitionArrowsLocalizedTransition O ψ)
      (C.componentRingMapLocalizedTransition O k) (C.componentRingMapLocalizedTransition O n)
      (C.transitionRingCompatible_localizedTransition O ψ) V F).mpr
      (Functor.map_isIso _ _)
    have hθP := (C.transitionRingedSiteHomTransitionRingedSite
      O ψ).isIso_sliceTransitionPullback_app_of_hasGlobalPresentation
      (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O k)
      (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
      (hGc := C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl O k)
      (hG'c := C.isCocontinuous_componentFunctor_componentRingedSite_quasicoherentCartesianInl O n)
      _ (C.transitionArrowsLocalizedTransition O ψ) (C.componentRingMapLocalizedTransition O k)
      (C.componentRingMapLocalizedTransition O n)
      (C.transitionRingCompatible_localizedTransition O ψ) V
      (C.isIso_siteTransitionPullback_app_unit_quasicoherentCartesianInl O ψ) hP
    have h := (C.transitionRingedSiteHomTransitionRingedSite O ψ).isIso_sliceRight_map_of_isIso
      (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O k)
      (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n) _
      (C.transitionArrowsLocalizedTransition O ψ)
      (C.componentRingMapLocalizedTransition O k) (C.componentRingMapLocalizedTransition O n)
      (C.transitionRingCompatible_localizedTransition O ψ) V c hc
      hθP hθF
    have := (C.transitionRingedSiteHomTransitionRingedSite O ψ).isContinuous_sliceRight
      (hG := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O k)
      (hG' := C.isContinuous_componentFunctor_componentRingedSite_localizedTransition O n)
      (C.transitionArrowsLocalizedTransition O ψ) V
    have h₂ := Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward _ c h
      (op (Over.mk b'.fiber))
    have key : ∀ Z₁ : Over ((SimplicialSiteSituation.componentFunctor
          (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).obj V),
        Z₁ = Over.mk b → IsIso (c.val.app (op Z₁)) → IsIso (c.val.app (op (Over.mk b))) :=
      fun _ e h ↦ e ▸ h
    refine key _ ?_ h₂
    exact congrArg Over.mk
      (Pseudofunctor.CoGrothendieck.ι_map_comp_ιNatTrans_app C.totalPseudofunctor b'.base b'.fiber)
  exact SheafOfModules.HasGlobalPresentation.of_iso (@asIso _ _ _ _ c hcI) hP

/-- **A cartesian module with quasi-coherent components is quasi-coherent**, the converse
implication of Stacks 0D7M in case (A). An object of degree `n` of the total site is covered by
the images of a covering of `C_n` on whose members `F_n` is globally presented, and on each of
them `F` is globally presented by
`hasGlobalPresentation_over_componentFunctor_quasicoherentCartesianInl`. -/
theorem isQuasicoherentOnSite_of_isCartesianModule_quasicoherentCartesianInl
    (F : SheafOfModules.{u} ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O))
    (hF : (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).IsCartesianModule O F)
    (hn : ∀ n : SimplexCategory,
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentModule O F n).IsQuasicoherentOnSite) :
    F.IsQuasicoherentOnSite := by
  refine ⟨fun X ↦ ?_⟩
  let X' : Pseudofunctor.CoGrothendieck C.totalPseudofunctor := X
  obtain ⟨I, V, f, hcov, hpres⟩ := (hn X'.base.unop).locally_hasGlobalPresentation X'.fiber
  have hc := (@CoverPreserving.of_isContinuous _ _ _ _ (SimplicialSiteSituation.componentFunctor
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) X'.base.unop)
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentRingedTopos O X'.base.unop).J
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
    (C.isContinuous_componentFunctor_componentRingedSite_localizedTransition
      O X'.base.unop)).cover_preserve hcov
  refine ⟨I, _, fun i ↦ (SimplicialSiteSituation.componentFunctor
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) X'.base.unop).map (f i),
    GrothendieckTopology.superset_covering _ ?_ hc,
    fun i ↦ C.hasGlobalPresentation_over_componentFunctor_quasicoherentCartesianInl O F hF (V i)
      (hpres i)⟩
  rintro Y g ⟨Y', a, h, ha, rfl⟩
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp ha
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i, h ≫ (SimplicialSiteSituation.componentFunctor
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) X'.base.unop).map b,
      (congrArg (h ≫ ·) ((SimplicialSiteSituation.componentFunctor
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) X'.base.unop).map_comp b (f i))).trans
        (Category.assoc _ _ _).symm⟩

end CategoryTheory.SimplicialSite

end
