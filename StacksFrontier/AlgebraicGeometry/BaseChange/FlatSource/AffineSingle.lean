module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.CechBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.CechTermwise
public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Resolution
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite

/-!
# Base change at the direct image of a flat module along an affine morphism

Base change for the derived direct image of a module flat over the base and over the source
along a separated quasi-compact morphism to an affine scheme, computed through the absolute
Čech resolution for a finite affine cover, also at every shift.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Modules (toShHom_comm)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange

universe u

namespace Stacks.AlgebraicGeometry.FlatSourceBaseChange

noncomputable section

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X X' S S' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
  (hsq : IsPullback g' f' f g)

/-- **The derived pullback of a flat module placed in degree zero is its pullback**: a flat
module placed in degree zero is a bounded above complex of flat modules, hence K-flat, and the
comparison `Lg^*F ⟶ g^*F` is invertible on K-flat complexes. -/
theorem isIso_derivedPullbackComparison_single_of_isFlat {Y Y' : RingedSpace.{u, u}}
    (g : Y' ⟶ Y) (F : SheafOfModules.{u} (structureSheafRing Y))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F) :
    IsIso ((derivedPullbackComparison g).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))) := by
  let D : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ :=
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F
  have hD : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) (D.X n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso Y.sheaf
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm hF
    · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero Y.sheaf
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n hn)
  exact Stacks.DerivedPullback.Composition.isIso_derivedPullbackComparison_app_of_isKFlat g
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj D)
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat Y D
      ⟨0, (CochainComplex.isStrictlyLE_iff D 0).2 fun i hi =>
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i (by omega)⟩ hD)

section Cech

variable (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from S))]
  (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)

/-- The `ℤ`-indexed absolute Čech resolution of `ℱ` for the cover `T`. -/
abbrev cechResolution : CochainComplex (SheafOfModules.{u} (structureSheafRing
    X.toRingedSpace)) ℤ :=
  ((Tag01XLDerivedIso.absoluteCechComplexPlus T).obj F).obj

include hsq in
/-- The underived base change map is invertible at every term of the Čech resolution. -/
theorem isIso_moduleBaseChangeSquare_app_cechResolution_X (n : ℤ) :
    IsIso ((moduleBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (toShHom_comm hsq.w)).natTrans.app ((cechResolution T F).X n)) := by
  rw [moduleBaseChangeSquare_eq_baseChangeNatTrans hsq.w]
  by_cases h0 : 0 ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = n := ⟨n.toNat, by omega⟩
    exact (NatTrans.isIso_app_iff_of_iso _
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := p) rfl)).2
      (isIso_baseChangeNatTrans_app_cechComplex_X hsq T F p)
  · have hz : IsZero ((cechResolution T F).X n) :=
      HomologicalComplex.isZero_extend_X _ _ n fun i hi => by
        change (i : ℤ) = n at hi
        omega
    exact isIso_of_source_target_iso_zero _
      (Functor.map_isZero _ (Functor.map_isZero _ hz)).isoZero
      (Functor.map_isZero (modulePushforward f'.toLRSHom.toShHom)
        (Functor.map_isZero (modulePullback g'.toLRSHom.toShHom) hz)).isoZero

include hsq in
/-- The pullback along `g'` of every term of the Čech resolution is acyclic for `f'_*`. -/
theorem rightAcyclic_modulePullback_cechResolution_X (n : ℤ) :
    (modulePushforward f'.toLRSHom.toShHom).rightAcyclic
      ((modulePullback g'.toLRSHom.toShHom).obj ((cechResolution T F).X n)) := by
  by_cases h0 : 0 ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = n := ⟨n.toNat, by omega⟩
    exact RightAcyclicProduct.rightAcyclic_of_iso _
      ((Scheme.Modules.pullback g').mapIso
        (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := p) rfl)).symm
      (rightAcyclic_pullback_cechComplex_X hsq T F p)
  · refine RightAcyclicProduct.rightAcyclic_of_isZero _ (Functor.map_isZero _ ?_)
    exact HomologicalComplex.isZero_extend_X _ _ n fun i hi => by
      change (i : ℤ) = n at hi
      omega

/-- An object at which a natural transformation commuting with the shift is invertible remains
one after shifting. -/
theorem isIso_app_shift_of_isIso {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ]
    [HasShift D ℤ] {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ] (τ : F₁ ⟶ F₂)
    [NatTrans.CommShift τ ℤ] (Y : C) (n : ℤ) (h : IsIso (τ.app Y)) : IsIso (τ.app (Y⟦n⟧)) := by
  rw [NatTrans.app_shift τ n Y]
  infer_instance

include hsq in
/-- **The base change map at a shift of the absolute Čech resolution of a module flat over the
base is invertible**, followed by `Rf'_*` of the comparison of derived and underived pullback:
every derived functor in sight is computed termwise on the shifted Čech resolution. -/
theorem isIso_derivedBaseChangeMap_comp_cechResolution_shift
    (hF : IsFlatOver f.toLRSHom.toShHom F.obj) (n : ℤ) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (toShHom_comm hsq.w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((cechResolution T F)⟦n⟧))) ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        ((derivedPullbackComparison g'.toLRSHom.toShHom).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ((cechResolution T F)⟦n⟧)))) := by
  obtain ⟨n₀, hn₀⟩ := ((Tag01XLDerivedIso.absoluteCechComplexPlus T).obj F).property
  have : (cechResolution T F).IsStrictlyGE n₀ := hn₀
  have hplus : ∀ (M : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
      [M.IsStrictlyGE n₀], (M⟦n⟧).IsStrictlyGE (n₀ - n) :=
    fun M _ => CochainComplex.isStrictlyGE_shift M n₀ n (n₀ - n) (by omega)
  refine isIso_derivedBaseChangeMap_comp_of_termwise _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · exact isIso_derivedPushforwardUnit_app_of_plus_of_rightAcyclic f.toLRSHom.toShHom _
      ⟨n₀ - n, hplus _⟩
      (fun k => Tag01XLDerivedIso.rightAcyclic_absoluteCechComplexPlus_X f T F (k + n))
  · have e := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((Tag01XLDerivedIso.pushforwardAbsoluteCechComplexExtendIso f T).app F)
    have h₀ : IsIso ((derivedPullbackComparison g.toLRSHom.toShHom).app
        (((modulePushforward f.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (cechResolution T F)))) :=
      (NatTrans.isIso_app_iff_of_iso _ e).2
        (isIso_derivedPullbackComparison_relativeCechComplex f T F hF g)
    have h₁ := isIso_app_shift_of_isIso (derivedPullbackComparison g.toLRSHom.toShHom) _ n h₀
    refine (NatTrans.isIso_app_iff_of_iso _ ?_).1 h₁
    exact ((((modulePushforward f.toLRSHom.toShHom).mapHomotopyCategory
        (ComplexShape.up ℤ)).commShiftIso n).app _).symm ≪≫
      ((modulePushforward f.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).mapIso
        (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).commShiftIso n).app _).symm
  · rw [underivedBaseChangeSquare_app_quotient]
    suffices h : IsIso ((NatTrans.mapHomologicalComplex
        (moduleBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
          g.toLRSHom.toShHom (toShHom_comm hsq.w)).natTrans (ComplexShape.up ℤ)).app
        ((cechResolution T F)⟦n⟧)) from Functor.map_isIso _ _
    suffices hc : ∀ k, IsIso (((NatTrans.mapHomologicalComplex
        (moduleBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
          g.toLRSHom.toShHom (toShHom_comm hsq.w)).natTrans (ComplexShape.up ℤ)).app
        ((cechResolution T F)⟦n⟧)).f k) from HomologicalComplex.Hom.isIso_of_components _
    intro k
    show IsIso ((moduleBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom (toShHom_comm hsq.w)).natTrans.app
        ((cechResolution T F).X (k + n)))
    exact isIso_moduleBaseChangeSquare_app_cechResolution_X hsq T F (k + n)
  · exact isIso_derivedPushforwardUnit_app_of_plus_of_rightAcyclic f'.toLRSHom.toShHom _
      ⟨n₀ - n, (CochainComplex.isStrictlyGE_iff _ (n₀ - n)).2 fun i hi =>
        Functor.map_isZero _
          (@CochainComplex.isZero_of_isStrictlyGE _ _ _ ((cechResolution T F)⟦n⟧) (n₀ - n) i hi
            (hplus _))⟩
      fun k => rightAcyclic_modulePullback_cechResolution_X hsq T F (k + n)

include hsq in
/-- **The base change map at the absolute Čech resolution of a module flat over the base is
invertible**, followed by `Rf'_*` of the comparison of derived and underived pullback: every
derived functor in sight is computed termwise on the Čech resolution. -/
theorem isIso_derivedBaseChangeMap_comp_cechResolution
    (hF : IsFlatOver f.toLRSHom.toShHom F.obj) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (toShHom_comm hsq.w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (cechResolution T F))) ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        ((derivedPullbackComparison g'.toLRSHom.toShHom).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (cechResolution T F)))) := by
  refine isIso_derivedBaseChangeMap_comp_of_termwise _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · exact isIso_derivedPushforwardUnit_app_of_plus_of_rightAcyclic f.toLRSHom.toShHom _
      ((Tag01XLDerivedIso.absoluteCechComplexPlus T).obj F).property
      (Tag01XLDerivedIso.rightAcyclic_absoluteCechComplexPlus_X f T F)
  · exact (NatTrans.isIso_app_iff_of_iso _ ((HomotopyCategory.quotient _
      (ComplexShape.up ℤ)).mapIso
        ((Tag01XLDerivedIso.pushforwardAbsoluteCechComplexExtendIso f T).app F))).2
      (isIso_derivedPullbackComparison_relativeCechComplex f T F hF g)
  · rw [underivedBaseChangeSquare_app_quotient]
    suffices h : IsIso ((NatTrans.mapHomologicalComplex
        (moduleBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
          g.toLRSHom.toShHom (toShHom_comm hsq.w)).natTrans (ComplexShape.up ℤ)).app
        (cechResolution T F)) from Functor.map_isIso _ _
    suffices hc : ∀ n, IsIso (((NatTrans.mapHomologicalComplex
        (moduleBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
          g.toLRSHom.toShHom (toShHom_comm hsq.w)).natTrans (ComplexShape.up ℤ)).app
        (cechResolution T F)).f n) from HomologicalComplex.Hom.isIso_of_components _
    exact isIso_moduleBaseChangeSquare_app_cechResolution_X hsq T F
  · obtain ⟨n₀, hn₀⟩ := ((Tag01XLDerivedIso.absoluteCechComplexPlus T).obj F).property
    exact isIso_derivedPushforwardUnit_app_of_plus_of_rightAcyclic f'.toLRSHom.toShHom _
      ⟨n₀, (CochainComplex.isStrictlyGE_iff _ n₀).2 fun i hi =>
        Functor.map_isZero _
          (@CochainComplex.isZero_of_isStrictlyGE _ _ _ (cechResolution T F) n₀ i hi hn₀)⟩
      (rightAcyclic_modulePullback_cechResolution_X hsq T F)

include hsq T in
/-- **Base change for the derived direct image of a module flat over the base and over the
source, through a finite affine open cover.** Let `X` and `S` have affine diagonal and let `T` be
a finite affine open cover of `X`. For a quasi-coherent `𝒪_X`-module `ℱ` which is flat over `S`
and flat as an `𝒪_X`-module, the derived base change map `Lg^*Rf_*ℱ ⟶ Rf'_*L(g')^*ℱ` is an
isomorphism, for every base change `g`. -/
theorem isIso_derivedBaseChangeMap_single_of_cover
    (hF : IsFlatOver f.toLRSHom.toShHom F.obj)
    (hFX : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F.obj) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (toShHom_comm hsq.w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F.obj)))) := by
  let ε : (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ) 0).obj F.obj ⟶ cechResolution T F :=
    (CechSiteChange.absoluteCechAugZ X T).app F
  have : QuasiIso ε := CechSiteChange.quasiIso_absoluteCechAugZ_app X T F
  have hK := isIso_derivedPullbackComparison_single_of_isFlat g'.toLRSHom.toShHom F.obj hFX
  have hcomp := isIso_derivedBaseChangeMap_comp_of_quasiIso _ _ _ _ (toShHom_comm hsq.w) ε
    (quasiIso_map_modulePullback_of_isIso_comparison g'.toLRSHom.toShHom ε hK
      (isIso_derivedPullbackComparison_absoluteCechComplex T F hFX g'))
    (isIso_derivedBaseChangeMap_comp_cechResolution hsq T F hF)
  exact IsIso.of_isIso_comp_right _ ((derivedPushforward f'.toLRSHom.toShHom).map
    ((derivedPullbackComparison g'.toLRSHom.toShHom).app _))

include hsq T in
/-- **Base change for the derived direct image of a shift of a module flat over the base and over
the source, through a finite affine open cover**: `isIso_derivedBaseChangeMap_single_of_cover`
for the module placed in degree `-n`. -/
theorem isIso_derivedBaseChangeMap_single_shift_of_cover
    (hF : IsFlatOver f.toLRSHom.toShHom F.obj)
    (hFX : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F.obj) (n : ℤ) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (toShHom_comm hsq.w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F.obj)⟦n⟧)))) := by
  let ε : (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ) 0).obj F.obj ⟶ cechResolution T F :=
    (CechSiteChange.absoluteCechAugZ X T).app F
  have : QuasiIso ε := CechSiteChange.quasiIso_absoluteCechAugZ_app X T F
  have : QuasiIso (ε⟦n⟧') := (CochainComplex.quasiIso_shift_iff ε n).2 inferInstance
  have hshift : ∀ (M : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ),
      IsIso ((derivedPullbackComparison g'.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) →
      IsIso ((derivedPullbackComparison g'.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (M⟦n⟧))) := fun M h =>
    (NatTrans.isIso_app_iff_of_iso _
      (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).commShiftIso n).app M)).2
      (isIso_app_shift_of_isIso _ _ n h)
  have hK := hshift _ (isIso_derivedPullbackComparison_single_of_isFlat g'.toLRSHom.toShHom
    F.obj hFX)
  have hcomp := isIso_derivedBaseChangeMap_comp_of_quasiIso _ _ _ _ (toShHom_comm hsq.w)
    (ε⟦n⟧') (quasiIso_map_modulePullback_of_isIso_comparison g'.toLRSHom.toShHom (ε⟦n⟧') hK
      (hshift _ (isIso_derivedPullbackComparison_absoluteCechComplex T F hFX g')))
    (isIso_derivedBaseChangeMap_comp_cechResolution_shift hsq T F hF n)
  exact IsIso.of_isIso_comp_right _ ((derivedPushforward f'.toLRSHom.toShHom).map
    ((derivedPullbackComparison g'.toLRSHom.toShHom).app _))

end Cech

end

end Stacks.AlgebraicGeometry.FlatSourceBaseChange
