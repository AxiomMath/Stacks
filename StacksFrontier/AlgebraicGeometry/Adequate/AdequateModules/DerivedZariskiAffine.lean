module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedZariskiUnit
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFlat

/-!
# `Lf^*` and the unit of `Lf^* ⊣ Rf_*` over an affine base

Let `f : ((Sch/Spec A)_τ, 𝒪) ⟶ ((Spec A)_Zar, 𝒪)` be the morphism of [Stacks, Tag 070U] over an
affine base. Every object of `D_QCoh(Spec A)` is represented by a K-flat complex `F` of flat
quasi-coherent modules: it is `M̃^•` for an object `M` of `D(A)` ([Stacks, Tag 06Z0]), `M` has a
K-flat resolution by flat modules ([Stacks, Tag 06Y4]), and sheafification preserves both
properties ([Stacks, Tag 08DV], [Stacks, Tag 05P0]). On such an `F`, `Lf^*F = f^*F` is a complex
of adequate modules, so its cohomology is adequate, and the unit `F ⟶ Rf_*f^*F` is the degreewise
unit, invertible on quasi-coherent modules, followed by the comparison `f_*f^*F ⟶ Rf_*f^*F`,
invertible on complexes of adequate modules. This is the affine case of [Stacks, Tag 070W], which
the source reaches through the equivalence `D_QCoh(S) = D(QCoh(𝒪_S))` for affine `S`.

## Main results

* `Stacks.Adequate.exists_isKFlat_isQuasicoherent_model`: the K-flat model.
* `Stacks.Adequate.BigSite.isAdequate_homology_derivedZariskiPullback_of_affine`: `Lf^*` carries
  `D_QCoh` into `D_Adeq`.
* `Stacks.Adequate.BigSite.isIso_derivedZariskiAdjunction_unit_app_of_affine`: the unit is
  invertible on `D_QCoh`.

## References

* [Stacks Project, Tag 070W](https://stacks.math.columbia.edu/tag/070W)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 08DV](https://stacks.math.columbia.edu/tag/08DV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Adequate

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (A : CommRingCat.{u})

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **A K-flat model with flat quasi-coherent terms, on an affine scheme.** Every object of
`D_QCoh(𝒪_{Spec A})` is the class of a K-flat complex of flat quasi-coherent modules: write it as
`M̃^•` ([Stacks, Tag 06Z0]), resolve `M` by a K-flat complex of flat `A`-modules
([Stacks, Tag 06Y4]) and sheafify degreewise ([Stacks, Tag 08DV], [Stacks, Tag 05P0]). -/
theorem exists_isKFlat_isQuasicoherent_model
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Spec A).zariskiRingedSite.toRingedTopos.O)))
    (hE : ∀ n : ℤ, SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Spec A).zariskiRingedSite.toRingedTopos.O)) n).obj
          E)) :
    ∃ F : CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Spec A).zariskiRingedSite.toRingedTopos.O)) ℤ,
      Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
        (Y := (Spec A).zariskiRingedSite.toRingedTopos) ((HomotopyCategory.quotient _ _).obj F) ∧
      (∀ n, SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf (F.X n)) ∧
      Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj F) ≅ E) := by
  obtain ⟨M, ⟨eM⟩⟩ := StandardModel.exists_iso_mapDerivedCategory A E hE
  obtain ⟨K, q, hK, hflat, hq, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage M)
  refine ⟨((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    ⟨Stacks.TildeStalk.kFlatComplex_tilde A K hK, fun i ↦ (isFlat_tilde_iff_flat _).2 (hflat i)⟩,
    fun n ↦ inferInstanceAs ((tilde.functor A).obj (K.X n)).IsQuasicoherent, ⟨?_⟩⟩
  exact (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    ((tilde.functor A).mapDerivedCategoryFactors.app K).symm ≪≫
    (tilde.functor A).mapDerivedCategory.mapIso
      (asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso M) ≪≫ eM

variable {A} {τ : CoveringTopology} (B : BigSite τ (Spec A))

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 070W] over an affine base: `Lf^*` carries `D_QCoh` into `D_Adeq`.** On a K-flat
model `F` with flat quasi-coherent terms, `Lf^*F` is `f^*F` ([Stacks, Tag 06YY]), a complex of
adequate modules ([Stacks, Tag 06VK]), whose cohomology is adequate since adequate modules form
a weak Serre subcategory. -/
theorem BigSite.isAdequate_homology_derivedZariskiPullback_of_affine
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Spec A).zariskiRingedSite.toRingedTopos.O)))
    (hE : ∀ n : ℤ, SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Spec A).zariskiRingedSite.toRingedTopos.O)) n).obj
          E)) (i : ℤ) :
    IsAdequate.{u, u} B ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)) i).obj
        (B.derivedZariskiPullback.obj E)) := by
  obtain ⟨F, hF, hFq, ⟨e⟩⟩ := exists_isKFlat_isQuasicoherent_model A E hE
  let d := Stacks.Cohomology.DerivedPullbackOfToposHom.kFlatLeftDerivedPullback
    B.zariskiRingedToposHom
  have hc : IsIso (d.comparison.app ((HomotopyCategory.quotient _ _).obj F)) :=
    d.isIso_comparison _ hF
  have hW : (adequate.{u, u} B).IsWeakSerreClass := adequate_isWeakSerreClass B
  have hX : ∀ n, IsAdequate.{u, u} B
      (((B.zariskiRingedToposHom.toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F).X n) :=
    fun n ↦ B.isAdequate_zariskiPullback_obj _ (hFq n)
  have hH := @Stacks.DerivedAcyclic.prop_homology_of_prop_X _ _ _ (adequate.{u, u} B)
    hW.toIsClosedUnderKernels hW.toIsClosedUnderCokernels _ hX i
  let e' : B.derivedZariskiPullback.obj E ≅ DerivedCategory.Q.obj
      ((B.zariskiRingedToposHom.toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F) :=
    B.derivedZariskiPullback.mapIso e.symm ≪≫
      @asIso _ _ _ _ (d.comparison.app ((HomotopyCategory.quotient _ _).obj F)) hc ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  exact (adequate.{u, u} B).prop_of_iso
    (((DerivedCategory.homologyFunctor _ i).mapIso e' ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _).symm) hH

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 070W] over an affine base: the unit of `Lf^* ⊣ Rf_*` is invertible on
`D_QCoh`.** On a K-flat model `F` with flat quasi-coherent terms the unit factors as the
degreewise unit `F ⟶ f_*f^*F`, invertible on quasi-coherent modules ([Stacks, Tag 06VN]), followed
by the comparison `f_*f^*F ⟶ Rf_*f^*F`, invertible because `f^*F` is a complex of adequate
modules. -/
theorem BigSite.isIso_derivedZariskiAdjunction_unit_app_of_affine
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Spec A).zariskiRingedSite.toRingedTopos.O)))
    (hE : ∀ n : ℤ, SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Spec A).zariskiRingedSite.toRingedTopos.O)) n).obj
          E)) :
    IsIso (B.derivedZariskiAdjunction.unit.app E) := by
  obtain ⟨F, hF, hFq, ⟨e⟩⟩ := exists_isKFlat_isQuasicoherent_model A E hE
  rw [← NatTrans.isIso_app_iff_of_iso B.derivedZariskiAdjunction.unit e]
  let f := B.zariskiRingedToposHom
  let d := Stacks.Cohomology.DerivedPullbackOfToposHom.kFlatLeftDerivedPullback f
  let M := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F
  have hfac := Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunction_unit_fac
    f d M
  have hc : IsIso (d.comparison.app M) := d.isIso_comparison M hF
  have h₁ : IsIso ((NatTrans.mapHomologicalComplex
      (RingedToposHom.pullbackAdjPushforwardModules f).unit (ComplexShape.up ℤ)).app F) := by
    have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex
        (RingedToposHom.pullbackAdjPushforwardModules f).unit (ComplexShape.up ℤ)).app F).f n) :=
      fun n ↦ B.isIso_zariskiUnit_app _ (hFq n)
    exact HomologicalComplex.Hom.isIso_of_components _
  have h₂ : IsIso (DerivedCategory.Qh.map
      ((Stacks.Cohomology.DerivedPushforward.pullbackAdjPushforwardMapHomotopy f).unit.app M)) := by
    have : (Stacks.Cohomology.DerivedPushforward.pullbackAdjPushforwardMapHomotopy f).unit.app M =
        (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
          (RingedToposHom.pullbackAdjPushforwardModules f).unit (ComplexShape.up ℤ)).app F) := rfl
    rw [this]
    exact @Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Qh _
      (@Functor.map_isIso _ _ _ _ _ _ (HomotopyCategory.quotient _ _) _ h₁)
  have h₃ := B.isIso_derivedZariskiPushforwardUnit_app_of_isAdequate
    ((f.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    (fun n ↦ B.isAdequate_zariskiPullback_obj _ (hFq n))
  have h₄ : IsIso ((Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunction
        f d).unit.app (DerivedCategory.Qh.obj M) ≫
      (Stacks.Cohomology.DerivedPushforward.derivedPushforward f).map (d.comparison.app M)) := by
    rw [hfac]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h₃
  show IsIso ((Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunction
    f d).unit.app (DerivedCategory.Qh.obj M))
  exact IsIso.of_isIso_comp_right _
    ((Stacks.Cohomology.DerivedPushforward.derivedPushforward f).map (d.comparison.app M))

end Stacks.Adequate

end
