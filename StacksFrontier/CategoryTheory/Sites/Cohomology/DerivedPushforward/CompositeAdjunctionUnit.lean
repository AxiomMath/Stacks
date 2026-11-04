module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOnRingedTopoiUnconditional
public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjunctionUnitTruncations

/-!
# Units of derived adjunctions of ringed topoi: composites and exact direct images

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed topoi. This file records two facts about
the units `K ⟶ Rf_* Lf^* K` of the derived adjunctions of Stacks 07A6.

* The unit for `g ∘ f` is the unit for `g`, followed by `Rg_*` of the unit for `f` at `Lg^* K`
  and of the comparison `Lf^* Lg^* K ⟶ L(g ∘ f)^* K` of Stacks 0D6D, followed by the composition
  isomorphism of Stacks 0D6E. So the unit for `g ∘ f` is invertible at `K` as soon as the unit
  for `g` is and the composite map `Lg^* K ⟶ Rf_* L(g ∘ f)^* K` is.
* If the direct image `f_*` on sheaves of modules is exact, the canonical map from the
  degreewise direct image to the derived direct image is an isomorphism at every complex; if
  moreover the unit `𝓕 ⟶ f_* f^* 𝓕` is an isomorphism for every module, then the derived unit
  `K ⟶ Rf_* Lf^* K` is an isomorphism at every object.

## Main results

* `Stacks.Cohomology.CompositeAdjunctionUnit.derivedAdjunction_comp_unit_app`: the factorization
  of the unit for `g ∘ f`.
* `Stacks.Cohomology.CompositeAdjunctionUnit.isIso_derivedPushforwardUnit_app_of_exact`: an exact
  direct image computes its derived direct image.
* `Stacks.Cohomology.CompositeAdjunctionUnit.isIso_derivedAdjunction_unit_app_of_isIso_unit`: the
  derived unit is invertible when the direct image is exact and the underived unit invertible.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
open Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi

namespace Stacks.Cohomology.CompositeAdjunctionUnit

attribute [local instance] HasDerivedCategory.standard

universe u

section Composite

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
  (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosg : g.u.IsMorphismOfSites Z.J Y.J)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))]

/-- **The unit of the derived adjunction for `g ∘ f`** is the unit for `g`, followed by `Rg_*` of
the composite `Lg^* K ⟶ Rf_* Lf^* Lg^* K ⟶ Rf_* L(g ∘ f)^* K`, followed by the composition
isomorphism `Rg_* Rf_* ≅ R(g ∘ f)_*`. -/
theorem derivedAdjunction_comp_unit_app
    (K : _root_.DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (derivedAdjunction (g.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg)).unit.app K =
      (derivedAdjunction g hmosg).unit.app K ≫
        (derivedPushforward g).map
          ((derivedAdjunction f hmosf).unit.app ((derivedPullback g).obj K) ≫
            (derivedPushforward f).map ((derivedPullbackCompComparison f g).app K)) ≫
        (derivedPushforwardCompIsoOfAdjoints f g hmosf hmosg).hom.app
          ((derivedPullback (g.comp f)).obj K) := by
  rw [← derivedCompAdjunction_ofNatIsoRight f g hmosf hmosg]
  simp [Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft, derivedCompAdjunction,
    Adjunction.comp_unit_app, Functor.map_comp]

/-- **The unit for `g ∘ f` is invertible at `K`** as soon as the unit for `g` is and the composite
`Lg^* K ⟶ Rf_* L(g ∘ f)^* K` is. -/
theorem isIso_derivedAdjunction_comp_unit_app
    (K : _root_.DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    [IsIso ((derivedAdjunction g hmosg).unit.app K)]
    [IsIso ((derivedAdjunction f hmosf).unit.app ((derivedPullback g).obj K) ≫
      (derivedPushforward f).map ((derivedPullbackCompComparison f g).app K))] :
    IsIso ((derivedAdjunction (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg)).unit.app K) := by
  rw [derivedAdjunction_comp_unit_app f g hmosf hmosg K]
  infer_instance

end Composite

section Exact

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)

/-- **An exact direct image computes its derived direct image**: the canonical map from the
degreewise direct image to `Rf_*` is invertible at every complex. A K-injective resolution
`M ⟶ I` is carried by the exact `f_*` to a quasi-isomorphism, and the canonical map is
invertible at `I`. -/
theorem isIso_derivedPushforwardUnit_app_of_exact
    [PreservesFiniteLimits f.pushforwardTopos] [PreservesFiniteColimits f.pushforwardTopos]
    (M : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    IsIso ((derivedPushforwardUnit f).app M) := by
  obtain ⟨I, g, hI, hg⟩ := exists_quasiIso_isKInjective X M.as
  let g' : M ⟶ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I :=
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g
  have := isIso_derivedPushforwardUnit_app_of_isKInjective f I hI
  have hnat := (derivedPushforwardUnit f).naturality g'
  have : IsIso (DerivedCategory.Qh.map g') :=
    (DerivedCategory.isIso_Qh_map_iff _).2 ((HomotopyCategory.quotient_map_mem_quasiIso_iff g).2 hg)
  have : IsIso ((pushforwardOnHomotopy f).map g') :=
    (NatIso.isIso_map_iff f.pushforwardTopos.mapDerivedCategoryFactorsh g').1
      (inferInstanceAs
        (IsIso (f.pushforwardTopos.mapDerivedCategory.map (DerivedCategory.Qh.map g'))))
  have : IsIso ((DerivedCategory.Qh ⋙ derivedPushforward f).map g') :=
    inferInstanceAs (IsIso ((derivedPushforward f).map (DerivedCategory.Qh.map g')))
  have : IsIso ((derivedPushforwardUnit f).app M ≫
      (DerivedCategory.Qh ⋙ derivedPushforward f).map g') := hnat ▸ inferInstance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Qh ⋙ derivedPushforward f).map g')

variable (hmos : f.u.IsMorphismOfSites Y.J X.J)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

include hmos in
/-- **The derived unit is invertible at every object** when the direct image is exact and the
underived unit `𝓕 ⟶ f_* f^* 𝓕` is invertible: at a K-flat resolution the derived unit is the
underived one followed by the canonical maps, which are then invertible. -/
theorem isIso_derivedAdjunction_unit_app_of_isIso_unit
    [PreservesFiniteLimits f.pushforwardTopos] [PreservesFiniteColimits f.pushforwardTopos]
    [IsIso f.pullbackPushforwardAdjunctionTopos.unit]
    (K : _root_.DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    IsIso ((derivedAdjunction f hmos).unit.app K) := by
  obtain ⟨P, hP, s, hs⟩ := hasResolutions_isKFlat (Y := Y) (DerivedCategory.Qh.objPreimage K)
  have : IsIso (DerivedCategory.Qh.map s) :=
    (DerivedCategory.isIso_Qh_map_iff _).2 hs
  let e : DerivedCategory.Qh.obj P ≅ K :=
    asIso (DerivedCategory.Qh.map s) ≪≫ DerivedCategory.Qh.objObjPreimageIso K
  suffices IsIso ((derivedAdjunction f hmos).unit.app (DerivedCategory.Qh.obj P)) from
    Stacks.DerivedCategory.AdjunctionUnitTruncations.isIso_unit_app_of_iso _ e.symm
  have hfac := derivedPullbackPushforwardAdjunctionOfKFlat_unit_fac f hmos
    (fun h ↦ pullbackInvertsQuasiIso_isKFlat f h) P
  have : IsIso ((derivedPullbackComparison f).app P) :=
    LeftDerivedByResolutions.isIso_app_of_resolutions
      (HomotopyCategory.quasiIso _ _) IsKFlat hasResolutions_isKFlat (pullbackOnHomotopy f)
      (pullbackInvertsQuasiIso_isKFlat f hmos) DerivedCategory.Qh (derivedPullback f)
      (derivedPullbackComparison f) P hP
  have : IsIso ((homotopyPullbackPushforwardAdjunction f).unit.app P) := by
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    have : ∀ n : ℤ, IsIso (((Adjunction.mapHomologicalComplexAdjunction
        f.pullbackPushforwardAdjunctionTopos (ComplexShape.up ℤ)).unit.app L).f n) :=
      fun n ↦ inferInstanceAs (IsIso (f.pullbackPushforwardAdjunctionTopos.unit.app (L.X n)))
    have : IsIso ((Adjunction.mapHomologicalComplexAdjunction
        f.pullbackPushforwardAdjunctionTopos (ComplexShape.up ℤ)).unit.app L) :=
      HomologicalComplex.Hom.isIso_of_components _
    exact inferInstanceAs (IsIso ((HomotopyCategory.quotient _ _).map
      ((Adjunction.mapHomologicalComplexAdjunction
        f.pullbackPushforwardAdjunctionTopos (ComplexShape.up ℤ)).unit.app L)))
  have := isIso_derivedPushforwardUnit_app_of_exact f
    ((f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj P)
  have : IsIso ((derivedPullbackPushforwardAdjunctionOfKFlat f hmos
      (fun h ↦ pullbackInvertsQuasiIso_isKFlat f h)).unit.app (DerivedCategory.Qh.obj P) ≫
      (derivedPushforward f).map ((derivedPullbackComparison f).app P)) := by
    rw [hfac]; infer_instance
  show IsIso ((derivedPullbackPushforwardAdjunctionOfKFlat f hmos
      (fun h ↦ pullbackInvertsQuasiIso_isKFlat f h)).unit.app (DerivedCategory.Qh.obj P))
  exact IsIso.of_isIso_comp_right _
    ((derivedPushforward f).map ((derivedPullbackComparison f).app P))

end Exact

end Stacks.Cohomology.CompositeAdjunctionUnit

end
