module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedAlongEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeSchemeCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulesFlat
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# Relative perfectness under the relocalization of an algebraic space

Let `g : T ⟶ S` be a morphism of a big fppf site and `f : X ⟶ Y` a morphism of algebraic spaces
over `T`, flat and locally of finite presentation, with lower-shriek extension
`Λ f : Λ X ⟶ Λ Y` over `S`. If `M ∈ D_QCoh(𝒪_X)` is `Y`-perfect, then its image under the
relocalization `D(𝒪_X) ≌ D(𝒪_{Λ X})` is `Λ Y`-perfect.

The two sides are compared on affine squares of étale scheme charts (Stacks 0DKQ): a chart `U`
of `Λ X` and the chart `U'` of `X` it comes from have the same scheme, and the derived sections
over `U` of the relocalization of `M` are the derived sections of `M` over `U'`, both being right
derived functors of the same sections functor.

## Main results

* `AlgebraicGeometry.Space.nonempty_derivedSections_relocalize_iso`
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_relocalizeDerivedFunctor_obj`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
-- No global `HasDerivedCategory` instance applies to modules on small étale sites, which are not
-- `SmallCategory`; at low priority the standard model chooses nothing where a global one exists.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
attribute [local instance] hasRightDerivedFunctor_chartSections

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) {X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B T hT X)

/-- The relocalized structure sheaf on a chart `U` of `Λ X` and on the chart of `X` it comes
from agree: the counit of the equivalence of small étale sites has identity underlying
morphism of schemes. -/
theorem relocalizeRingSheaf_map_counit_eq_id
    (U : SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)) :
    ((relocalizeRingSheaf B hT hS g X hX).obj.map
      ((SmallEtale.relocalize B hT hS g X hX).counit.app U).op).hom =
      RingHom.id ((relocalizeRingSheaf B hT hS g X hX).obj.obj (op U)) :=
  rfl

/-- **Derived sections over a chart commute with relocalization.** For a chart `U` of `Λ X`
and `M ∈ D(𝒪_X)`, the derived sections over `U` of the relocalization of `M` are the derived
sections of `M` over the chart of `X` that `U` comes from. -/
theorem nonempty_derivedSections_relocalize_iso
    (U : SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor g).obj X))
    (M : DerivedCategory (Modules.{u, u} B T hT X hX)) :
    Nonempty
      ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS _
            (isAlgebraicSpace_relocalize' B hT hS g X hX)).O) U).obj
          ((relocalizeDerivedFunctor B hT hS g X hX).obj M) ≅
        (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT X hX).O)
          ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U)).obj M) := by
  let e := SmallEtale.relocalize B hT hS g X hX
  let RS := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS _
    (isAlgebraicSpace_relocalize' B hT hS g X hX)).O
  let RT := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT X hX).O
  let φ := (RS.obj.map (e.counit.app U).op).hom
  let : HasDerivedCategory (ModuleCat.{u} (RT.obj.obj (op (e.inverse.obj U)))) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{u} RS) := HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{u} RT) := HasDerivedCategory.standard _
  have hφ : φ = RingHom.id _ := relocalizeRingSheaf_map_counit_eq_id B hT hS g hX U
  let F := SheafOfModules.evaluation.{u} RT (op (e.inverse.obj U))
  let G : SheafOfModules.{u} RS ⥤ ModuleCat.{u} (RT.obj.obj (op (e.inverse.obj U))) :=
    SheafOfModules.evaluation.{u} RS (op U)
  have : G.Additive := inferInstanceAs (SheafOfModules.evaluation.{u} RS (op U)).Additive
  let EA : SheafOfModules.{u} RT ⥤ SheafOfModules.{u} RS :=
    (relocalizeModulesEquivalence B hT hS g X hX).functor
  let σ : F ⋙ 𝟭 _ ≅ EA ⋙ G :=
    NatIso.ofComponents (fun N => (ModuleCat.restrictScalarsId'App.{u} φ hφ (F.obj N)).symm)
      (fun _ => rfl)
  let RF :=
    Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections.{u + 1, u, u, u}
      RT (e.inverse.obj U)
  let RG : DerivedCategory (SheafOfModules.{u} RS) ⥤
      DerivedCategory (ModuleCat.{u} (RT.obj.obj (op (e.inverse.obj U)))) :=
    Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections.{u + 1, u, u, u} RS U
  let αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG :=
    Functor.totalRightDerivedUnit
      (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopySections.{u + 1, u, u, u}
        RS U)
      DerivedCategory.Qh (HomotopyCategory.quasiIso (SheafOfModules.{u} RS) (ComplexShape.up ℤ))
  have : RG.IsRightDerivedFunctor αG
      (HomotopyCategory.quasiIso (SheafOfModules.{u} RS) (ComplexShape.up ℤ)) :=
    (inferInstance :
      (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections.{u + 1, u, u, u}
        RS U).IsRightDerivedFunctor (Functor.totalRightDerivedUnit
        (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopySections.{u + 1, u, u, u}
          RS U)
        DerivedCategory.Qh (HomotopyCategory.quasiIso (SheafOfModules.{u} RS) (ComplexShape.up ℤ)))
        (HomotopyCategory.quasiIso (SheafOfModules.{u} RS) (ComplexShape.up ℤ)))
  let iso : RF ⋙ (𝟭 _).mapDerivedCategory ≅ EA.mapDerivedCategory ⋙ RG :=
    Stacks.DerivedFunctor.rightDerivedCompMapDerivedCategoryIso F G EA (𝟭 _) σ RF
      (Functor.totalRightDerivedUnit _ _ _) RG αG
  exact ⟨(iso.app M).symm ≪≫ StacksDraft.DerivedRingIso.mapDerivedCategoryIdIso.app _⟩

include hX in
/-- The relocalization of an object of `D(𝒪_X)` lies in `D_QCoh(𝒪_{Λ X})` exactly when the object
lies in `D_QCoh(𝒪_X)`. -/
theorem qcohDerived_relocalizeDerivedFunctor_obj_iff
    (M : DerivedCategory (Modules.{u, u} B T hT X hX)) :
    QcohDerived B S hS ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩
      ((relocalizeDerivedFunctor B hT hS g X hX).obj M) ↔ QcohDerived B T hT ⟨X, hX⟩ M := by
  let E := relocalizeModulesEquivalence B hT hS g X hX
  refine ⟨fun h n => ?_, fun hM n => ?_⟩
  · refine (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_of_iso
      (E.unitIso.app _).symm
      ((isQuasicoherentOnSite_relocalizeModulesEquivalence_iff B hT hS g X hX _).2
        ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_of_iso
          ((Functor.mapDerivedCategoryHomologyFunctorIso
            E.functor n).app M) (h n)))
  · exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_of_iso
      ((E.functor.mapDerivedCategoryHomologyFunctorIso
        n).app M).symm
      ((isQuasicoherentOnSite_relocalizeModulesEquivalence_iff B hT hS g X hX _).1
        ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_of_iso
          (E.unitIso.app _) (hM n)))

include hX in
/-- The relocalization of an object of `D_QCoh(𝒪_X)` lies in `D_QCoh(𝒪_{Λ X})`. -/
theorem qcohDerived_relocalizeDerivedFunctor_obj (M : DerivedCategory (Modules.{u, u} B T hT X hX))
    (hM : QcohDerived B T hT ⟨X, hX⟩ M) :
    QcohDerived B S hS ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩
      ((relocalizeDerivedFunctor B hT hS g X hX).obj M) :=
  (qcohDerived_relocalizeDerivedFunctor_obj_iff B hT hS g hX M).2 hM

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  sheafTensor_additive_inverseImageRingedSite_over
  sheafTensor_obj_additive_inverseImageRingedSite_over
  hasMapBifunctor_sheafTensor_inverseImageRingedSite_over

omit hX in
/-- **Derived sections over an affine chart commute with relocalization.** For an affine chart `U`
of `Λ X` and `M ∈ D(𝒪_X)`, `RΓ(h_U, u^*ρ(M)) ≅ RΓ(h_{U'}, u'^*M)`, where `U'` is the chart of `X`
that `U` comes from (it has the same scheme). -/
theorem nonempty_representedAffineDerivedSections_relocalize_iso {X : AlgebraicSpaces B T hT}
    (U : SmallEtale B S hS (relocalizeSpace B hT hS g X).1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS _).obj U))]
    (M : DerivedCategory (Modules.{u, u} B T hT X.1 X.2)) :
    haveI : IsAffine ((BigFppfOver.toScheme B T hT).obj ((SmallEtale.toOver B T hT X.1).obj
        ((SmallEtale.relocalize B hT hS g X.1 X.2).inverse.obj U))) :=
      ‹IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS _).obj U))›
    Nonempty ((representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS _).obj U)).obj
        ((smallEtaleDerivedModulePullback B S hS
          (chartToSpace B S hS (relocalizeSpace B hT hS g X) U)).obj
          ((relocalizeDerivedFunctor B hT hS g X.1 X.2).obj M)) ≅
      (representedAffineDerivedSections B T hT ((SmallEtale.toOver B T hT X.1).obj
          ((SmallEtale.relocalize B hT hS g X.1 X.2).inverse.obj U))).obj
        ((smallEtaleDerivedModulePullback B T hT (chartToSpace B T hT X
          ((SmallEtale.relocalize B hT hS g X.1 X.2).inverse.obj U))).obj M)) := by
  have : IsAffine ((BigFppfOver.toScheme B T hT).obj ((SmallEtale.toOver B T hT X.1).obj
      ((SmallEtale.relocalize B hT hS g X.1 X.2).inverse.obj U))) :=
    ‹IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS _).obj U))›
  obtain ⟨e₁⟩ := nonempty_derivedSections_iso_representedAffineDerivedSections
    (relocalizeSpace B hT hS g X) U ((relocalizeDerivedFunctor B hT hS g X.1 X.2).obj M)
  obtain ⟨e₂⟩ := nonempty_derivedSections_relocalize_iso B hT hS g X.2 U M
  obtain ⟨e₃⟩ := nonempty_derivedSections_iso_representedAffineDerivedSections X
    ((SmallEtale.relocalize B hT hS g X.1 X.2).inverse.obj U) M
  exact ⟨(representedAffineDerivedSections B S hS _).mapIso
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS _
        (isEtale_chartToSpace B S hS (relocalizeSpace B hT hS g X) U)).app _) ≪≫
    e₁.symm ≪≫ e₂ ≪≫ e₃ ≪≫ ((representedAffineDerivedSections B T hT _).mapIso
      ((smallEtaleDerivedModulePullbackIsoEtale B T hT _
        (isEtale_chartToSpace B T hT X _)).app M)).symm⟩

omit hX in
/-- The tensor bifunctor on a slice of the inverse-image ringed site of a relocalized morphism is
additive. -/
theorem sheafTensor_additive_relocalizeHom {X Y : AlgebraicSpaces B T hT} (f : X ⟶ Y)
    (U : (inverseImageRingedSite B S hS (relocalizeHom B hT hS g f)).C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((inverseImageRingedSite B S hS (relocalizeHom B hT hS g f)).over U).O).Additive :=
  sheafTensor_additive_inverseImageRingedSite_over _ U

omit hX in
/-- The tensor product with a fixed module on a slice of the inverse-image ringed site of a
relocalized morphism is additive. -/
theorem sheafTensor_obj_additive_relocalizeHom {X Y : AlgebraicSpaces B T hT} (f : X ⟶ Y)
    (U : (inverseImageRingedSite B S hS (relocalizeHom B hT hS g f)).C)
    (M : RingedSite.Modules.{u + 1, u, u}
      ((inverseImageRingedSite B S hS (relocalizeHom B hT hS g f)).over U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((inverseImageRingedSite B S hS (relocalizeHom B hT hS g f)).over U).O).obj M).Additive :=
  sheafTensor_obj_additive_inverseImageRingedSite_over _ U M

omit hX in
/-- The total tensor complexes on a slice of the inverse-image ringed site of a relocalized
morphism exist. -/
theorem hasMapBifunctor_sheafTensor_relocalizeHom {X Y : AlgebraicSpaces B T hT}
    (f : X ⟶ Y) (U : (inverseImageRingedSite B S hS (relocalizeHom B hT hS g f)).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u}
      ((inverseImageRingedSite B S hS (relocalizeHom B hT hS g f)).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS (relocalizeHom B hT hS g f)).over U).O)
      (ComplexShape.up ℤ) :=
  hasMapBifunctor_sheafTensor_inverseImageRingedSite_over _ U K L

attribute [local instance] sheafTensor_additive_relocalizeHom sheafTensor_obj_additive_relocalizeHom
  hasMapBifunctor_sheafTensor_relocalizeHom

omit hX in
/-- **Relative perfectness is preserved by relocalization.** For a morphism `f : X ⟶ Y` of
algebraic spaces over `T` which is flat and locally of finite presentation, and
`M ∈ D_QCoh(𝒪_X)` which is `Y`-perfect, the relocalization of `M` in `D(𝒪_{Λ X})` is
`Λ Y`-perfect. -/
theorem isPerfectRelativeToCanonical_relocalizeDerivedFunctor_obj {X Y : AlgebraicSpaces B T hT}
    (f : X ⟶ Y) (hfl : IsFlat B T hT f.hom) (hlfp : IsLocallyOfFinitePresentation B T hT f.hom)
    (M : DerivedCategory (Modules.{u, u} B T hT X.1 X.2)) (hM : QcohDerived B T hT X M)
    (h : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B T hT f hfl hlfp M) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS (relocalizeHom B hT hS g f)
      ((Space.holdsOnEveryEtaleChart_relocalizeMap_iff B T S hT hS g _ f.hom).2 hfl)
      ((Space.holdsOnEveryEtaleChart_relocalizeMap_iff B T S hT hS g _ f.hom).2 hlfp)
      ((relocalizeDerivedFunctor B hT hS g X.1 X.2).obj M) := by
  refine isPerfectRelativeToCanonical_of_forall_isAffine_chartDiagram (relocalizeHom B hT hS g f)
    _ _ _ (qcohDerived_relocalizeDerivedFunctor_obj B hT hS g X.2 M hM) (fun d hU hV => ?_)
  let dT := ChartDiagram.derelocalize B hT hS g X.2 Y.2 f.hom d
  have : IsAffine ((BigFppfOver.toScheme B T hT).obj ((SmallEtale.toOver B T hT X.1).obj dT.U)) :=
    hU
  have : IsAffine ((BigFppfOver.toScheme B T hT).obj ((SmallEtale.toOver B T hT Y.1).obj dT.V)) :=
    hV
  obtain ⟨hpc, htor⟩ := (isPerfectRelativeTo_chartObject_iff_of_isAffine f hfl hlfp dT M hM).1
    (isPerfectRelativeTo_chartObject_of_isPerfectRelativeToCanonical f hfl hlfp M hM h dT)
  obtain ⟨E⟩ := nonempty_representedAffineDerivedSections_relocalize_iso B hT hS g d.U M
  let : HasDerivedCategory (ModuleCat.{u}
      Γ((BigFppfOver.toScheme B T hT).obj ((SmallEtale.toOver B T hT X.1).obj dT.U), ⊤)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{u}
      Γ((BigFppfOver.toScheme B T hT).obj ((SmallEtale.toOver B T hT Y.1).obj dT.V), ⊤)) :=
    HasDerivedCategory.standard _
  refine ⟨hpc.ofIso E.symm, ?_⟩
  exact (StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
      _ _).2
    (((StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
      _ _).1 htor).imp fun a => Exists.imp fun b hab =>
        AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
          ((ModuleCat.restrictScalars
            ((BigFppfOver.toScheme B T hT).map dT.g).appTop.hom).mapDerivedCategory.mapIso E.symm)
          a b hab)

end AlgebraicGeometry.Space

end
