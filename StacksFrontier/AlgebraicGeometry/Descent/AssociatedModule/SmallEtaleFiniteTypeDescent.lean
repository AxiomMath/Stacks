module

public import StacksFrontier.AlgebraicGeometry.Coherent.IdealSheafFiniteTypeBridge
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineFiniteTypeSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel

/-!
# Finite type descends along `ε` for a quasi-coherent module

Let `S` be a scheme contained in a big étale site and let
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of [Stacks, Tag 08H7]. A
quasi-coherent `𝒪_S`-module `𝓕` whose associated module `ε^*𝓕` is of finite type on the small
étale site is itself of finite type. This is the converse of [Stacks, Tag 08HD] for a
quasi-coherent module; the tag itself is stated for an arbitrary `𝒪_S`-module.

## Main results

* `Stacks.module_finite_compHom_of_surjective`: finiteness of a module descends along a
  surjective ring map, for the restriction of scalars `Module.compHom`.
* `AlgebraicGeometry.SmallEtale.module_finite_sections_affineOpen_of_isFiniteTypeOnSite`: for a
  quasi-coherent `𝓕` with `ε^*𝓕` of finite type, the sections of `𝓕` over an affine open form a
  finite module.
* `AlgebraicGeometry.SmallEtale.isFiniteType_of_isFiniteTypeOnSite_associatedModule` and
  `AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_of_isFiniteTypeOnSite_associatedModule`: a
  quasi-coherent `𝓕` with `ε^*𝓕` of finite type is of finite type, in Mathlib's finite-type
  condition and in the categorical one of [Stacks, Tag 03DL] (5).

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks

/-- If `f : R →+* T` is surjective and `M` is a finite `T`-module, then `M` is a finite `R`-module
for the restriction of scalars along `f`. -/
theorem module_finite_compHom_of_surjective {R T M : Type u} [Ring R] [Ring T]
    [AddCommGroup M] (inst : Module T M) (f : R →+* T) (hf : Function.Surjective f)
    (h : @Module.Finite T M _ _ inst) :
    letI := inst
    @Module.Finite R M _ _ (Module.compHom M f) := by
  classical
  let := inst
  have h := h
  let : Module R M := Module.compHom M f
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := T) (M := M)
  refine Module.Finite.of_surjective (Fintype.linearCombination R s) fun x ↦ ?_
  have hx : x ∈ Submodule.span T (Set.range s) := hs.ge Submodule.mem_top
  rw [← Fintype.range_linearCombination] at hx
  obtain ⟨c, hc⟩ := hx
  obtain ⟨r, hr⟩ := hf.hasRightInverse
  refine ⟨fun i ↦ r (c i), ?_⟩
  rw [Fintype.linearCombination_apply, ← hc, Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change f (r (c i)) • s i = c i • s i
  rw [hr (c i)]

end Stacks

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sections of a quasi-coherent module over an affine open form a finite module, as soon as
its associated module is of finite type on the small étale site. -/
theorem module_finite_sections_affineOpen_of_isFiniteTypeOnSite
    (F : S.Modules) (hF : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) F)
    (hft : _root_.SheafOfModules.IsFiniteTypeOnSite ((associatedModule B S hS).obj F))
    (U : S.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(S, U) Γ(F, U) := by
  have hG := isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS F hF
  have haff : SmallEtale.IsAffine B S hS ((opensToSmallEtale B S hS).obj U) := hU
  have hfin := module_finite_sections_affineChartModule_of_isFiniteTypeOnSite B S hS
    ((associatedModule B S hS).obj F) hG hft ⟨(opensToSmallEtale B S hS).obj U, haff⟩
  have hsurj : Function.Surjective ((structureMap B S hS).hom.app (op U)).hom := by
    rw [structureMap_hom_app]
    exact (ConcreteCategory.bijective_of_isIso
      ((forget₂ CommRingCat RingCat.{u}).map (Scheme.Opens.topIso (X := S) U).inv)).2
  have e := (PresheafOfModules.evaluation S.ringCatSheaf.obj (op U)).mapIso
    ((SheafOfModules.forget S.ringCatSheaf).mapIso
      (@asIso _ _ _ _ _ (unitIsoOnQuasicoherent B S hS ⟨F, hF⟩)))
  have key : Module.Finite (S.ringCatSheaf.obj.obj (op U))
      ((PresheafOfModules.evaluation S.ringCatSheaf.obj (op U)).obj
        ((SheafOfModules.forget S.ringCatSheaf).obj
          ((associatedModule B S hS ⋙ restrictModule B S hS).obj F))) :=
    Stacks.module_finite_compHom_of_surjective _
      ((structureMap B S hS).hom.app (op U)).hom hsurj hfin
  exact (Module.Finite.of_surjective (ModuleCat.Hom.hom e.inv)
    (ConcreteCategory.bijective_of_isIso e.inv).2 :
      Module.Finite (S.ringCatSheaf.obj.obj (op U)) (F.val.obj (op U)))

/-- A quasi-coherent `𝒪_S`-module whose associated module on the small étale site is of finite
type is of finite type, in Mathlib's finite-type condition. -/
theorem isFiniteType_of_isFiniteTypeOnSite_associatedModule (F : S.Modules) [F.IsQuasicoherent]
    (hft : _root_.SheafOfModules.IsFiniteTypeOnSite ((associatedModule B S hS).obj F)) :
    _root_.SheafOfModules.IsFiniteType F :=
  Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_of_finite_sections F fun V ↦
    module_finite_sections_affineOpen_of_isFiniteTypeOnSite B S hS F ‹F.IsQuasicoherent› hft
      V.1 V.2

/-- A quasi-coherent `𝒪_S`-module whose associated module on the small étale site is of finite
type is of finite type, in the categorical finite-type condition of [Stacks, Tag 03DL] (5). -/
theorem isFiniteTypeOnSite_of_isFiniteTypeOnSite_associatedModule (F : S.Modules)
    [F.IsQuasicoherent]
    (hft : _root_.SheafOfModules.IsFiniteTypeOnSite ((associatedModule B S hS).obj F)) :
    _root_.SheafOfModules.IsFiniteTypeOnSite F :=
  Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType F
    (isFiniteType_of_isFiniteTypeOnSite_associatedModule B S hS F hft)

end AlgebraicGeometry.SmallEtale

end
