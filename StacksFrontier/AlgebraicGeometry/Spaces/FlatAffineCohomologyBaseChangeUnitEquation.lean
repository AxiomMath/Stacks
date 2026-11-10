module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartProjectionSpellingAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnitTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorByBaseModuleUnitSection

/-!
# `s ↦ s ⊗ 1` is the unit of `(g')^* ⊣ g'_*`

For the cartesian square of **Stacks 073J**

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

with `Y = Spec(A)` and `Y' = Spec(B)` affine, the second part of **Stacks 073K** identifies
`𝓕 ⊗_A B` with `g'_*𝓕'`.  Under that identification the canonical map `s ↦ s ⊗ 1` of
`AlgebraicGeometry.Space.BaseChangeDiagram.tensorOneMap` *is* the unit of the adjunction
`(g')^* ⊣ g'_*`:

```
tensorOneMap ≫ (pushforwardTensorChartIso).hom
  = (modulePullbackAdjunction g').unit.app 𝓕 ≫ (modulePushforwardChartIso.app pulledBack).hom
```

## Main results

* `Stacks.TensorByBaseModule.unitIso_inv_comp_map_spanHom_app`: the inverse of `𝓕 ⊗_R R ≅ 𝓕`
  followed by the functor applied to `Stacks.FlatDevissage.spanHom m` carries a section `s` to
  `s ⊗ₜ (1 ⊗ₜ m)`.
* `Stacks.TensorByBaseModule.tensorOne_presheaf_eq`: an identification of `s ↦ s ⊗ m` followed by
  a presheaf-level comparison with a morphism of sheaves follows from the corresponding statement
  on sections.
* `Stacks.TensorByBaseModule.tensorOne_comp_eqToHom_iso_of_hom_eq`: the same identification after
  gluing, for a comparison transported along an equality of coefficient maps.
* `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorAppLinear_one_tmul_one`: over a
  chart `W` of `X` the comparison of sections carries `s ⊗ (1 ⊗ 1)` to the chart component of the
  unit at `s`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.unitChartIso_val_app`: so does the unit of
  `(g')^* ⊣ g'_*` read across `AlgebraicGeometry.Space.modulePushforwardChartIso`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.tensorOneMap_comp_pushforwardTensorChartIso`: the
  equation displayed above.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TensorProduct
open Stacks.FlatDevissage
open Stacks.TensorByBaseModule

universe u u₂ v₂ w₂

namespace Stacks.TensorByBaseModule

open _root_.PresheafOfModules
open Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type u₂} [CategoryTheory.Category.{v₂} C] (R : Type w₂) [CommRing R]
  (J : CategoryTheory.GrothendieckTopology C)
  [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  (O : CategoryTheory.Sheaf J CommRingCat.{w₂})
  (𝓕 : SheafOfModules.{w₂} (ringSheaf J O)) (θ : constantRingPresheaf (C := C) R ⟶ O.obj)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **`s ↦ s ⊗ m` on sections.**  The inverse of `𝓕 ⊗_R R ≅ 𝓕` followed by the presheaf-level
tensor functor applied to `Stacks.FlatDevissage.spanHom m` carries a section `s` of `𝓕` over `X`
to `s ⊗ₜ (1 ⊗ₜ m)`. -/
theorem unitIso_inv_comp_map_spanHom_app (M : ModuleCat.{w₂} R) (m : M) (X : Cᵒᵖ)
    (s : 𝓕.val.obj X) :
    letI := coefficientAlgebraOfHom R J O θ X
    Hom.app ((tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ).inv ≫
        (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map (spanHom m)) X s =
      TensorProduct.tmul (O.obj.obj X) s
        (TensorProduct.tmul R (1 : O.obj.obj X) m) := by
  let := coefficientAlgebraOfHom R J O θ X
  change TensorProduct.tmul (O.obj.obj X) s
      (Hom.app ((changeOfRings θ).map ((constantModulePresheaf R).map (spanHom m))) X
        (Hom.app ((changeOfRings θ).map (constantModuleUnitIso R).inv) X
          (Hom.app (changeOfRingsUnitIso R J O θ).inv X (1 : O.obj.obj X)))) = _
  refine congrArg (TensorProduct.tmul (O.obj.obj X) s) ?_
  have hunit := changeOfRingsAdjunction_unit_app_apply θ
    (unit (ringPresheaf (constantRingPresheaf (C := C) R))) X
    (1 : (ringPresheaf (constantRingPresheaf (C := C) R)).obj X)
  have h3 := cofHom_app_tmul θ (constantModuleUnitIso (C := C) R).inv X
    (1 : O.obj.obj X) (1 : (ringPresheaf (constantRingPresheaf (C := C) R)).obj X)
  have h4 := cofHom_app_tmul θ ((constantModulePresheaf R).map (spanHom m)) X
    (1 : O.obj.obj X) (1 : (ringPresheaf (constantRingPresheaf (C := C) R)).obj X)
  refine Eq.trans (congrArg
    (fun z => Hom.app ((changeOfRings θ).map ((constantModulePresheaf R).map (spanHom m))) X
      (Hom.app ((changeOfRings θ).map (constantModuleUnitIso (C := C) R).inv) X z))
    ((changeOfRingsUnitIso_inv_app_one R J O θ X).trans hunit)) ?_
  refine Eq.trans (congrArg
    (fun z => Hom.app ((changeOfRings θ).map ((constantModulePresheaf R).map (spanHom m))) X z)
    h3) ?_
  let : Module R (((constantModulePresheaf R).obj M).obj X) := M.isModule
  refine h4.trans ?_
  exact congrArg (TensorProduct.tmul R (1 : O.obj.obj X)) (one_smul R m)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **`s ↦ s ⊗ m` followed by a presheaf-level comparison, from its effect on sections.**  If `Φ`
carries `s ⊗ (1 ⊗ m)` to `ψ s` for every section `s`, then the inverse of `𝓕 ⊗_R R ≅ 𝓕`
followed by the tensor functor applied to `spanHom m` and by `Φ` is `ψ`. -/
theorem tensorOne_presheaf_eq (M : ModuleCat.{w₂} R) (m : M)
    (G : SheafOfModules.{w₂} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj G))
    (ψ : 𝓕 ⟶ G)
    (h : ∀ (X : Cᵒᵖ) (s : 𝓕.val.obj X),
      letI := coefficientAlgebraOfHom R J O θ X
      letI : Module R (((constantModulePresheaf R).obj M).obj X) := M.isModule
      Hom.app Φ X (TensorProduct.tmul (O.obj.obj X) s
          (TensorProduct.tmul R (1 : O.obj.obj X) m)) = Hom.app ψ.val X s) :
    (tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ).inv ≫
        (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map (spanHom m) ≫ Φ =
      (SheafOfModules.forget (ringSheaf J O) ⋙
        PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).map ψ := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  exact (congrArg (Hom.app Φ X)
    (unitIso_inv_comp_map_spanHom_app R J O 𝓕 θ M m X s)).trans (h X s)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  [CategoryTheory.HasWeakSheafify J AddCommGrpCat.{w₂}]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- `Stacks.TensorByBaseModule.tensorOneSheafify` with the glued comparison written as the
adjoint transpose of `Φ` under sheafification. -/
theorem tensorOneSheafifyHomEquiv (M : ModuleCat.{w₂} R) (m : M)
    (G : SheafOfModules.{w₂} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj G))
    (ψ : 𝓕 ⟶ G)
    (h : (tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ).inv ≫
          (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map (spanHom m) ≫ Φ =
        (SheafOfModules.forget (ringSheaf J O) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).map ψ) :
    (tensorByBaseModuleOfHom R J O 𝓕 θ).map (spanHom m) ≫
        (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm Φ =
      (tensorByBaseModuleOfHomUnitIso R J O 𝓕 θ).hom ≫ ψ := by
  change (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).map
          ((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map (spanHom m)) ≫
        (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm Φ =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).map
          (tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ).hom ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).counit.app 𝓕 ≫ ψ
  rw [← sheafificationAdjunction_homEquiv_eq, ← Adjunction.homEquiv_naturality_left_symm]
  exact (congrArg (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O).obj)).homEquiv
        ((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj (unitModule R)) G).symm)
    ((Iso.inv_comp_eq _).mp h)).trans
    (comp_symm_map_of_sheaf J O 𝓕 _ G ψ
      (tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ).hom)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **`s ↦ s ⊗ m` followed by a glued comparison is `ψ`.**  The comparison is taken as an
isomorphism `E` together with the equation identifying it with the adjoint transpose of `Φ`. -/
theorem tensorOne_comp_iso_of_hom_eq (M : ModuleCat.{w₂} R) (m : M)
    (G : SheafOfModules.{w₂} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj G))
    (ψ : 𝓕 ⟶ G) (E : (tensorByBaseModuleOfHom R J O 𝓕 θ).obj M ≅ G)
    (hE : E.hom = (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm Φ)
    (h : (tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ).inv ≫
          (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map (spanHom m) ≫ Φ =
        (SheafOfModules.forget (ringSheaf J O) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).map ψ) :
    (tensorByBaseModuleOfHomUnitIso R J O 𝓕 θ).inv ≫
        (tensorByBaseModuleOfHom R J O 𝓕 θ).map (spanHom m) ≫ E.hom = ψ := by
  rw [hE, tensorOneSheafifyHomEquiv R J O 𝓕 θ M m G Φ ψ h, Iso.inv_hom_id_assoc]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **`s ↦ s ⊗ m` followed by a glued comparison transported along an equality of coefficient
maps.** -/
theorem tensorOne_comp_eqToHom_iso_of_hom_eq
    {θ θ' : constantRingPresheaf (C := C) R ⟶ O.obj} (hθ : θ = θ')
    (M : ModuleCat.{w₂} R) (m : M) (G : SheafOfModules.{w₂} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheafOfHom R J O 𝓕 θ').obj M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj G))
    (ψ : 𝓕 ⟶ G) (E : (tensorByBaseModuleOfHom R J O 𝓕 θ').obj M ≅ G)
    (hE : E.hom = (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm Φ)
    (h : (tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ').inv ≫
          (tensorByBaseModulePresheafOfHom R J O 𝓕 θ').map (spanHom m) ≫ Φ =
        (SheafOfModules.forget (ringSheaf J O) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).map ψ) :
    ((tensorByBaseModuleOfHomUnitIso R J O 𝓕 θ).inv ≫
          (tensorByBaseModuleOfHom R J O 𝓕 θ).map (spanHom m)) ≫
        (eqToHom (congrArg (fun α => (tensorByBaseModuleOfHom R J O 𝓕 α).obj M) hθ) ≫ E.hom) =
      ψ := by
  subst hθ
  refine Eq.trans ?_ (tensorOne_comp_iso_of_hom_eq R J O 𝓕 θ M m G Φ ψ E hE h)
  exact (Category.assoc _ _ _).trans
    (congrArg ((tensorByBaseModuleOfHomUnitIso R J O 𝓕 θ).inv ≫ ·)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ E.hom) (Category.comp_id _))))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **`s ↦ s ⊗ m` followed by a transported glued comparison is `ψ`**, with both factors of the
composite carried as arguments. -/
theorem tensorOne_comp_eqToIso_of_hom_eq
    {θ θ' : constantRingPresheaf (C := C) R ⟶ O.obj} (hθ : θ = θ')
    (M : ModuleCat.{w₂} R) (m : M) (G : SheafOfModules.{w₂} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheafOfHom R J O 𝓕 θ').obj M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj G))
    (ψ : 𝓕 ⟶ G) (E : (tensorByBaseModuleOfHom R J O 𝓕 θ').obj M ≅ G)
    (hE : E.hom = (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm Φ)
    (t : 𝓕 ⟶ (tensorByBaseModuleOfHom R J O 𝓕 θ).obj M)
    (ht : t = (tensorByBaseModuleOfHomUnitIso R J O 𝓕 θ).inv ≫
      (tensorByBaseModuleOfHom R J O 𝓕 θ).map (spanHom m))
    (c : (tensorByBaseModuleOfHom R J O 𝓕 θ).obj M ≅ G)
    (hc : c = eqToIso (congrArg (fun α => (tensorByBaseModuleOfHom R J O 𝓕 α).obj M) hθ) ≪≫ E)
    (h : (tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ').inv ≫
          (tensorByBaseModulePresheafOfHom R J O 𝓕 θ').map (spanHom m) ≫ Φ =
        (SheafOfModules.forget (ringSheaf J O) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).map ψ) :
    t ≫ c.hom = ψ := by
  subst ht
  subst hc
  exact tensorOne_comp_eqToHom_iso_of_hom_eq R J O 𝓕 hθ M m G Φ ψ E hE h

end Stacks.TensorByBaseModule

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace BaseChangeDiagram

variable {B S hS} (D : BaseChangeDiagram B S hS)
  (hg' : yoneda.relativelyRepresentable D.g'.hom)
  (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom]
  (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom]

/-- **The comparison of sections carries `s ⊗ (1 ⊗ 1)` to the chart component of the unit.** -/
theorem pushforwardTensorAppLinear_one_tmul_one (W : SmallEtale B S hS D.X.1)
    (s : D.F.val.obj (op W)) :
    letI := D.chartBaseAlgebra V₀ W
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.pushforwardSectionsModule hg' W
    D.pushforwardTensorAppLinear hg' V₀ V₀' W
        (TensorProduct.tmul (chartRing B S hS D.X.1 D.X.2 W) s
          (TensorProduct.tmul (baseChartRing B S hS D.Y V₀)
            (1 : chartRing B S hS D.X.1 D.X.2 W)
            (1 : baseChartRing B S hS D.Y' V₀'))) =
      modulePullbackChartSection B S hS D.g' D.F (D.baseChangeChartDiagram hg' W) s := by
  let := D.chartBaseAlgebra V₀ W
  let := baseChartAlgebra B S hS D.g V₀ V₀'
  let := D.chartBaseChangeChartAlgebra hg' W
  let := D.pushforwardSectionsModule hg' W
  let := chartDiagramAlgebra B S hS D.g' (D.baseChangeChartDiagram hg' W)
  refine (D.pushforwardTensorAppLinear_tmul hg' V₀ V₀' W s 1 1).trans ?_
  have hc : D.chartRingTensorHom hg' V₀ V₀' W
      (TensorProduct.tmul (baseChartRing B S hS D.Y V₀)
        (1 : chartRing B S hS D.X.1 D.X.2 W) (1 : baseChartRing B S hS D.Y' V₀')) = 1 :=
    (D.chartRingTensorHom_tmul hg' V₀ V₀' W 1 1).trans
      ((congrArg (fun y => (1 : chartRing B S hS D.X.1 D.X.2 W) • y)
        (map_one (D.baseChangeChartBaseHom hg' V₀' W))).trans (one_smul _ _))
  refine Eq.trans (congrArg (fun c => modulePullbackChartBaseChange B S hS D.g' D.F
    (D.baseChangeChartDiagram hg' W) (TensorProduct.tmul _ c s)) hc) ?_
  exact (modulePullbackChartBaseChange_tmul B S hS D.g' D.F
    (D.baseChangeChartDiagram hg' W) 1 s).trans (one_smul _ _)

/-- **The unit of `(g')^* ⊣ g'_*` read across the chart comparison is the chart component of the
unit.** -/
theorem modulePushforwardChartIso_unit_val_app (W : SmallEtale B S hS D.X.1)
    (s : D.F.val.obj (op W)) :
    ((modulePushforwardChartIso B S hS D.g' hg').hom.app D.pulledBack).val.app (op W)
        (((modulePullbackAdjunction B S hS D.g').unit.app D.F).val.app (op W) s) =
      modulePullbackChartSection B S hS D.g' D.F (D.baseChangeChartDiagram hg' W) s := by
  refine (modulePushforwardChartIso_hom_app_chartSetProj B S hS D.g' hg'
    D.pulledBack W _).trans ?_
  refine (chartSetProj_modulePullbackAdjunction_unit B S hS D.g' hg' D.F W s).trans ?_
  refine (chartSetProj_eq_moduleChartProjection B S hS D.g' hg'
    (moduleSetSheaf B S hS D.X' D.pulledBack) W _).trans ?_
  rfl

/-- The unit of `(g')^* ⊣ g'_*` followed by the chart comparison, as one morphism `𝓕 ⟶ g'_*𝓕'`,
is the chart component of the unit on sections. -/
theorem unitChartIso_val_app (W : (SmallEtale B S hS D.X.1)ᵒᵖ) (s : D.F.val.obj W) :
    PresheafOfModules.Hom.app
        ((modulePullbackAdjunction B S hS D.g').unit.app D.F ≫
          ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).hom).val W s =
      modulePullbackChartSection B S hS D.g' D.F (D.baseChangeChartDiagram hg' W.unop) s :=
  (Stacks.Sheaves.RingedToposModules.comp_val_app_apply
      ((modulePullbackAdjunction B S hS D.g').unit.app D.F)
      ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).hom W s).trans
    (D.modulePushforwardChartIso_unit_val_app hg' W.unop s)

/-- **`s ↦ s ⊗ 1` followed by the presheaf-level comparison is the unit of `(g')^* ⊣ g'_*`.** -/
theorem pushforwardTensorComparison_tensorOne :
    (tensorByBaseModulePresheafOfHomUnitIso (baseChartRing B S hS D.Y V₀)
          (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
          (geometricCoefficientMap B S hS D.f V₀)).inv ≫
        (tensorByBaseModulePresheafOfHom (baseChartRing B S hS D.Y V₀)
          (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
          (geometricCoefficientMap B S hS D.f V₀)).map
          (spanHom (M := D.baseModule V₀ V₀') (1 : baseChartRing B S hS D.Y' V₀')) ≫
          D.pushforwardTensorComparison hg' V₀ V₀' =
      (SheafOfModules.forget _ ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
            (structureSheaf B S hS D.X.1 D.X.2)).obj)).map
        ((modulePullbackAdjunction B S hS D.g').unit.app D.F ≫
          ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).hom) := by
  refine tensorOne_presheaf_eq (baseChartRing B S hS D.Y V₀)
    (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
    (geometricCoefficientMap B S hS D.f V₀) (D.baseModule V₀ V₀')
    (1 : baseChartRing B S hS D.Y' V₀') (D.pushforwardPulledBack hg')
    (D.pushforwardTensorComparison hg' V₀ V₀')
    ((modulePullbackAdjunction B S hS D.g').unit.app D.F ≫
      ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).hom) (fun W s => ?_)
  refine Eq.trans ?_ (D.unitChartIso_val_app hg' W s).symm
  exact D.pushforwardTensorAppLinear_one_tmul_one hg' V₀ V₀' W.unop s

/-- **`s ↦ s ⊗ 1` is the unit of `(g')^* ⊣ g'_*`.**  Under the identification
`𝓕 ⊗_A B ≅ g'_*𝓕'` of `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorChartIso`, the
canonical map `AlgebraicGeometry.Space.BaseChangeDiagram.tensorOneMap` is the unit of the
adjunction `(g')^* ⊣ g'_*` followed by the comparison of the two spellings of the direct image. -/
theorem tensorOneMap_comp_pushforwardTensorChartIso (hV₀ : IsTerminal V₀)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] :
    D.tensorOneMap V₀ V₀' hV₀ ≫ (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀).hom =
      (modulePullbackAdjunction B S hS D.g').unit.app D.F ≫
        ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).hom :=
  tensorOne_comp_eqToIso_of_hom_eq (baseChartRing B S hS D.Y V₀)
    (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
    (baseChartCoefficientMap_eq B S hS D.f hV₀) (D.baseModule V₀ V₀')
    (1 : baseChartRing B S hS D.Y' V₀') (D.pushforwardPulledBack hg')
    (D.pushforwardTensorComparison hg' V₀ V₀')
    ((modulePullbackAdjunction B S hS D.g').unit.app D.F ≫
      ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).hom)
    (D.pushforwardTensorIso hg' V₀ V₀') rfl
    (D.tensorOneMap V₀ V₀' hV₀) rfl
    (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀) rfl
    (D.pushforwardTensorComparison_tensorOne hg' V₀ V₀')

end BaseChangeDiagram

end AlgebraicGeometry.Space

end
