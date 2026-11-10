module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedPushforwardAdequate
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.TermwiseAcyclicBoundedAmplitude
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct

/-!
# The unit of `Lf^* ⊣ Rf_*` for the morphism of 070U

Let `f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of [Stacks, Tag 070U] on a chosen big
site. This file records the following facts about `f` and the unit `K ⟶ Rf_* Lf^* K` of the
derived adjunction of [Stacks, Tag 07A6], over an arbitrary base:

* on quasi-coherent `𝒪_S`-modules the unit of `f^* ⊣ f_*` is invertible and `f^*` lands in the
  adequate modules ([Stacks, Tag 06VN], [Stacks, Tag 06VK]);
* `Rf_*` has cohomological amplitude `0` on complexes with adequate cohomology, and a complex of
  adequate modules computes `Rf_*` ([Stacks, Tag 0G9N], [Stacks, Tag 06VM]);
* at a K-flat complex `P` with flat terms, the derived unit is the degreewise unit
  `P ⟶ f_*f^*P` followed by `f_*` of a K-injective resolution of `f^*P`
  ([Stacks, Tag 06YY], [Stacks, Tag 09T5]).

## Main definitions

* `Stacks.Adequate.BigSite.zariskiUnitComplex`: the degreewise unit `P ⟶ f_*f^*P`.

## Main results

* `Stacks.Adequate.BigSite.isIso_zariskiUnit_app`: the unit of `f^* ⊣ f_*` is invertible at a
  quasi-coherent `𝒪_S`-module.
* `Stacks.Adequate.BigSite.isAdequate_zariskiPullback_obj`: `f^*` of a quasi-coherent
  `𝒪_S`-module is adequate.
* `Stacks.Adequate.BigSite.isIso_derivedZariskiPushforwardUnit_app_of_isAdequate`: complexes of
  adequate modules compute `Rf_*`.
* `Stacks.Adequate.BigSite.isIso_derivedZariskiAdjunction_unit_iff`: the derived unit at a K-flat
  complex is invertible exactly when `P ⟶ f_*f^*P ⟶ f_*I` is a quasi-isomorphism.

## References

* [Stacks Project, Tag 070W](https://stacks.math.columbia.edu/tag/070W)
* [Stacks Project, Tag 06VN](https://stacks.math.columbia.edu/tag/06VN)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Quasi-coherent modules -/

/-- The pullback–pushforward adjunction of the morphism of ringed topoi of [Stacks, Tag 070U], with
its right adjoint read as the direct image along the inclusion of the small Zariski site. -/
def BigSite.zariskiModulesAdjunction :
    B.zariskiRingedToposHom.toModulesHom.pullbackModules ⊣
      B.zariskiRingedSiteHom.toRingedToposSiteHom.pushforwardTopos :=
  (RingedToposHom.pullbackAdjPushforwardModules B.zariskiRingedToposHom).ofNatIsoRight
    B.zariskiRingedSiteHom.pushforwardToposIsoGeneral

/-- The associated-module adjunction of [Stacks, Tag 06VN], read on the categories of modules of
the two ringed topoi. -/
def BigSite.associatedModuleToposAdjunction :
    (B.associatedModuleOfSheaf : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)) ⊣
      B.zariskiRingedSiteHom.toRingedToposSiteHom.pushforwardTopos :=
  B.adjunctionOfSheaf

/-- The pullback of modules along the morphism of [Stacks, Tag 070U] is the associated-module
functor. -/
def BigSite.zariskiPullbackIsoAssociatedModule :
    B.zariskiRingedToposHom.toModulesHom.pullbackModules ≅ B.associatedModuleOfSheaf :=
  B.zariskiModulesAdjunction.leftAdjointUniq B.associatedModuleToposAdjunction

/-- The unit of `f^* ⊣ f_*` is invertible at a quasi-coherent `𝒪_S`-module. -/
theorem BigSite.isIso_zariskiUnit_app (F : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O))
    (hF : SheafOfModules.isQuasicoherent S.ringCatSheaf F) :
    IsIso ((RingedToposHom.pullbackAdjPushforwardModules B.zariskiRingedToposHom).unit.app F) := by
  have : F.IsQuasicoherent := hF
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app B.zariskiModulesAdjunction
    B.associatedModuleToposAdjunction F
  have h₂ : IsIso (B.zariskiModulesAdjunction.unit.app F) := by
    have : IsIso (B.associatedModuleToposAdjunction.unit.app F) :=
      B.isIso_associatedModuleAdjunction_unit_app F
    rw [← h₁] at this
    have hl : IsIso ((B.zariskiModulesAdjunction.leftAdjointUniq
        B.associatedModuleToposAdjunction).hom.app F) :=
      Iso.isIso_hom ((B.zariskiModulesAdjunction.leftAdjointUniq
        B.associatedModuleToposAdjunction).app F)
    have hG := @Functor.map_isIso _ _ _ _ _ _
      B.zariskiRingedSiteHom.toRingedToposSiteHom.pushforwardTopos _ hl
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hG this
  have h₃ : B.zariskiModulesAdjunction.unit.app F =
      (RingedToposHom.pullbackAdjPushforwardModules B.zariskiRingedToposHom).unit.app F ≫
        B.zariskiRingedSiteHom.pushforwardToposIsoGeneral.hom.app _ := by
    have h := Adjunction.homEquiv_ofNatIsoRight_apply
      (RingedToposHom.pullbackAdjPushforwardModules B.zariskiRingedToposHom)
      B.zariskiRingedSiteHom.pushforwardToposIsoGeneral
      (𝟙 (B.zariskiRingedToposHom.toModulesHom.pullbackModules.obj F))
    rwa [Adjunction.homEquiv_id, Adjunction.homEquiv_id] at h
  rw [h₃] at h₂
  exact IsIso.of_isIso_comp_right _
    (B.zariskiRingedSiteHom.pushforwardToposIsoGeneral.hom.app
      (B.zariskiRingedToposHom.toModulesHom.pullbackModules.obj F))

/-- The pullback of a quasi-coherent `𝒪_S`-module along the morphism of [Stacks, Tag 070U] is
adequate. -/
theorem BigSite.isAdequate_zariskiPullback_obj (F : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O))
    (hF : SheafOfModules.isQuasicoherent S.ringCatSheaf F) :
    IsAdequate B (B.zariskiRingedToposHom.toModulesHom.pullbackModules.obj F) := by
  have : F.IsQuasicoherent := hF
  exact (adequate.{u, u} B).prop_of_iso
    (B.zariskiPullbackIsoAssociatedModule.app F).symm
    (B.isAdequate_associatedModuleFunctor_obj F)

/-! ### Complexes of adequate modules compute `Rf_*` -/

attribute [local instance 2000] HasDerivedCategory.standard in
/-- `Rf_*` does not raise the cohomological degree of a complex with adequate cohomology: its
cohomology sheaves are the restrictions of those of the complex. -/
theorem BigSite.isLE_derivedZariskiPushforward_obj
    (L : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)))
    (hL : DerivedCategoryB.derivedCategoryB (adequate.{u, u} B) L) (d : ℤ) (hd : L.IsLE d) :
    (B.derivedZariskiPushforward.obj L).IsLE d := by
  have : B.zariskiRingedSiteHom.toRingedToposSiteHom.pushforwardTopos.Additive :=
    BigSite.additive_restrictModuleOfSheaf B
  rw [DerivedCategory.isLE_iff]
  intro i hi
  obtain ⟨e⟩ := B.nonempty_homology_derivedZariskiPushforward_iso L hL i
  exact IsZero.of_iso (Functor.map_isZero _ (L.isZero_of_isLE d i hi)) e

attribute [local instance 2000] HasDerivedCategory.standard in
/-- A complex of adequate modules computes `Rf_*`: the unit of the total right derived functor of
`f_*` is invertible at it. -/
theorem BigSite.isIso_derivedZariskiPushforwardUnit_app_of_isAdequate
    (X : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)) ℤ)
    (hX : ∀ n, IsAdequate B (X.X n)) :
    IsIso (((Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy
        B.zariskiRingedToposHom).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj X)) := by
  let G := B.zariskiRingedSiteHom.toRingedToposSiteHom.pushforwardTopos
  have : G.Additive := BigSite.additive_restrictModuleOfSheaf B
  have : PreservesFiniteLimits G := BigSite.preservesFiniteLimits_restrictModuleOfSheaf B
  have : B.zariskiRingedToposHom.pushforwardModules.Additive :=
    Functor.additive_of_iso B.zariskiRingedSiteHom.pushforwardToposIsoGeneral.symm
  have : PreservesFiniteLimits B.zariskiRingedToposHom.pushforwardModules :=
    preservesFiniteLimits_of_natIso B.zariskiRingedSiteHom.pushforwardToposIsoGeneral.symm
  refine Stacks.DerivedAcyclic.isIso_app_of_rightAcyclic_of_isLE
    B.zariskiRingedToposHom.pushforwardModules B.derivedZariskiPushforward _
    (adequate.{u, u} B) (adequate_isWeakSerreClass B) 1 (fun E d hE hEd ↦ ?_) X hX fun n ↦ ?_
  · rw [Nat.cast_one, add_sub_cancel_right]
    exact B.isLE_derivedZariskiPushforward_obj E hE d hEd
  · exact Functor.rightAcyclic_of_iso B.zariskiRingedSiteHom.pushforwardToposIsoGeneral.symm _
      (B.rightAcyclic_restrictModuleOfSheaf_of_isAdequate _ (hX n))

/-! ### The unit on a K-flat complex -/

/-- The pushforward `f_*` of modules along the morphism of 070U is additive. -/
instance BigSite.additive_zariskiPushforwardModules :
    B.zariskiRingedToposHom.pushforwardModules.Additive :=
  haveI : B.zariskiRingedSiteHom.toRingedToposSiteHom.pushforwardTopos.Additive :=
    BigSite.additive_restrictModuleOfSheaf B
  Functor.additive_of_iso B.zariskiRingedSiteHom.pushforwardToposIsoGeneral.symm

/-- The pullback `f^*` of modules along the morphism of 070U is additive. -/
instance BigSite.additive_zariskiPullbackModules :
    B.zariskiRingedToposHom.toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive B.zariskiRingedToposHom

/-- The degreewise unit `P ⟶ f_*f^*P` of a complex of `𝒪_S`-modules. -/
def BigSite.zariskiUnitComplex (P : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) ℤ) :
    P ⟶ (B.zariskiRingedToposHom.pushforwardModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((B.zariskiRingedToposHom.toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) where
  f n := (RingedToposHom.pullbackAdjPushforwardModules B.zariskiRingedToposHom).unit.app (P.X n)
  comm' i j _ :=
    ((RingedToposHom.pullbackAdjPushforwardModules
      B.zariskiRingedToposHom).unit.naturality (P.d i j)).symm


attribute [local instance 2000] HasDerivedCategory.standard in
/-- The derived unit at a K-flat complex, read in the homotopy category: see
`Stacks.Adequate.BigSite.isIso_derivedZariskiAdjunction_unit_iff`. -/
theorem BigSite.isIso_derivedZariskiAdjunction_unit_iff_qh
    (P : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) ℤ)
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := S.zariskiRingedSite.toRingedTopos) ((HomotopyCategory.quotient _ _).obj P))
    (I : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)) ℤ) [I.IsKInjective]
    (s : (B.zariskiRingedToposHom.toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ⟶ I) (hs : QuasiIso s) :
    IsIso (B.derivedZariskiAdjunction.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ↔
      IsIso (DerivedCategory.Qh.map
        ((Stacks.Cohomology.DerivedPushforward.pullbackAdjPushforwardMapHomotopy
            B.zariskiRingedToposHom).unit.app ((HomotopyCategory.quotient _ _).obj P) ≫
          (Stacks.Cohomology.DerivedPushforward.pushforwardMapHomotopy B.zariskiRingedToposHom).map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) := by
  let f := B.zariskiRingedToposHom
  let d := Stacks.Cohomology.DerivedPullbackOfToposHom.kFlatLeftDerivedPullback f
  let M := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
  have hfac := Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunction_unit_fac
    f d M
  have hc : IsIso (d.comparison.app M) := d.isIso_comparison M hP
  let α := (Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy f).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  have hαI : IsIso (α.app ((HomotopyCategory.quotient _ _).obj I)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ DerivedCategory.Qh _ α I
      inferInstance
  have hnat := α.naturality ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)
  simp only [Functor.comp_map] at hnat
  have hq : IsIso
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) :=
    (DerivedCategory.isIso_Qh_map_iff _).2 ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hs)
  change IsIso
    ((Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunction f d).unit.app
      (DerivedCategory.Qh.obj M)) ↔ _
  have key : DerivedCategory.Qh.map
        ((Stacks.Cohomology.DerivedPushforward.pullbackAdjPushforwardMapHomotopy f).unit.app M ≫
          (Stacks.Cohomology.DerivedPushforward.pushforwardMapHomotopy f).map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) ≫
        α.app ((HomotopyCategory.quotient _ _).obj I) =
      ((Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunction f d).unit.app
          (DerivedCategory.Qh.obj M) ≫
        (Stacks.Cohomology.DerivedPushforward.derivedPushforward f).map (d.comparison.app M)) ≫
        (Stacks.Cohomology.DerivedPushforward.derivedPushforward f).map
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) := by
    rw [hfac, Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun k ↦ DerivedCategory.Qh.map
      ((Stacks.Cohomology.DerivedPushforward.pullbackAdjPushforwardMapHomotopy f).unit.app M) ≫ k)
      hnat
  refine Iff.trans ?_ (isIso_comp_right_iff _ (α.app ((HomotopyCategory.quotient _ _).obj I)))
  rw [key]
  exact (isIso_comp_right_iff _ ((Stacks.Cohomology.DerivedPushforward.derivedPushforward f).map
      (d.comparison.app M))).symm.trans
    (isIso_comp_right_iff _ ((Stacks.Cohomology.DerivedPushforward.derivedPushforward f).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)))).symm

attribute [local instance 2000] HasDerivedCategory.standard in
/-- Let `P` be a K-flat complex of `𝒪_S`-modules and `s : f^*P ⟶ I` a quasi-isomorphism to a
K-injective complex. Then the unit `P ⟶ Rf_*Lf^*P` of the derived adjunction is invertible exactly
when the composite of the degreewise unit `P ⟶ f_*f^*P` with `f_*s` is a quasi-isomorphism. -/
theorem BigSite.isIso_derivedZariskiAdjunction_unit_iff
    (P : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) ℤ)
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := S.zariskiRingedSite.toRingedTopos) ((HomotopyCategory.quotient _ _).obj P))
    (I : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)) ℤ) [I.IsKInjective]
    (s : (B.zariskiRingedToposHom.toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ⟶ I) (hs : QuasiIso s) :
    IsIso (B.derivedZariskiAdjunction.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ↔
      QuasiIso (B.zariskiUnitComplex P ≫
        (B.zariskiRingedToposHom.pushforwardModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).map s) := by
  refine (B.isIso_derivedZariskiAdjunction_unit_iff_qh P hP I s hs).trans ?_
  have h : (Stacks.Cohomology.DerivedPushforward.pullbackAdjPushforwardMapHomotopy
        B.zariskiRingedToposHom).unit.app ((HomotopyCategory.quotient _ _).obj P) ≫
      (Stacks.Cohomology.DerivedPushforward.pushforwardMapHomotopy B.zariskiRingedToposHom).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (B.zariskiUnitComplex P ≫
        (B.zariskiRingedToposHom.pushforwardModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
          s) := by
    rw [Functor.map_comp]
    rfl
  rw [h]
  exact (DerivedCategory.isIso_Qh_map_iff _).trans
    (HomotopyCategory.quotient_map_mem_quasiIso_iff _)

end Stacks.Adequate

end
