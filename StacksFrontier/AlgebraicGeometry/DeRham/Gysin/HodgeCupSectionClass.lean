module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeBridgeShift
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCupRightUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeBridgeSectionClass
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgeNaturality

/-!
# The cup product with the class of a global section placed in degree `c`

For a multiplication `μ : F ⊗ G ⟶ H`, a global section `u` of `G` and a class `x ∈ H^q(X, F)`,
the cup product of Section 0FKU of `x` with the class of `u` placed in degree `c` is
`(-1)^{qc}` times the class of `x` multiplied by `u`, both read in the cohomology modules of the
derived global sections through the bridge `hgroupModuleShiftIso`
(`canonicalPairingModule_sectionClass`). The proof moves the class of `u` to degree `0` through
the shift (`hgroupModuleShiftIso_shift_hom`, `canonicalPairingModule_singleTensorMult_shift`),
where the class of `u` is the image of the class of `1` (`hgroupModuleShiftIso_sectionClass`)
and the cup product with it is right multiplication by `u`
(`canonicalPairingModule_unitComplexSectionMap`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.DeRham.CohomologicalGysin
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

open DerivedCategory

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}}

/-- `moduleDerivedMap` of the map of single complexes in degree `0` is the localization of the
map of extensions. -/
theorem moduleDerivedMap_singleFunctor_map
    {F H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (ψ : F ⟶ H) :
    moduleDerivedMap (a := 0) (b := 0) ((singleFunctor (_root_.SheafOfModules.{u}
        (structureSheafRing X)) ((0 : ℕ) : ℤ)).map ψ) =
      DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map ψ)
          ComplexShape.embeddingUpNat) := by
  have e := extendMap_single_comp_extendSingleIso ψ 0
  have e' : HomologicalComplex.extendMap
        ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map ψ) ComplexShape.embeddingUpNat =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0
          ((0 : ℕ) : ℤ) rfl).hom ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) ((0 : ℕ) : ℤ)).map ψ ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat H 0
          ((0 : ℕ) : ℤ) rfl).inv := by
    rw [← reassoc_of% e, Iso.hom_inv_id, Category.comp_id]
  rw [e', DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp]
  rfl

open Stacks.Cohomology.DerivedGlobalCupProduct (shiftCohomologyIsoR) in
/-- **The bridge and the shift (N-B), on elements**: the bridge in degree `c` is the bridge in
degree `0` followed by the inverse shift identification and `singleNatShiftIso`. -/
theorem hgroupModuleShiftIso_shift_apply
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c q : ℕ) (m : ℤ) (h : (q : ℤ) + (c : ℤ) = m) (h' : -(c : ℤ) + m = q)
    (y : Hgroup (structureSheafRing X) ⊤ q M) :
    (hgroupModuleShiftIso M c q m h).hom y =
      ((DerivedCategory.homologyFunctor _ m).map ((baseSections (baseRingedSpace X.sheaf)).map
          (DerivedCategory.Q.map (singleNatShiftIso M c).inv))).hom
        ((shiftCohomologyIsoR (S := baseRingedSpace X.sheaf)
          ((singleNat M 0).extend ComplexShape.embeddingUpNat)
          (-(c : ℤ)) m q h').inv ((hgroupModuleShiftIso M 0 q q (by simp)).hom y)) := by
  have hB := ConcreteCategory.congr_hom (hgroupModuleShiftIso_shift_hom M c q m h h') y
  have hid : ((DerivedCategory.homologyFunctor _ m).map ((baseSections X).map (DerivedCategory.Q.map
        (singleNatShiftIso M c).hom)) ≫
      (shiftCohomologyIsoR (S := X) ((singleNat M 0).extend ComplexShape.embeddingUpNat)
        (-(c : ℤ)) m q h').hom) ≫
      (shiftCohomologyIsoR (S := X) ((singleNat M 0).extend ComplexShape.embeddingUpNat)
        (-(c : ℤ)) m q h').inv ≫
      (DerivedCategory.homologyFunctor _ m).map ((baseSections X).map (DerivedCategory.Q.map
        (singleNatShiftIso M c).inv)) = 𝟙 _ := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [← hB]
  exact (ConcreteCategory.congr_hom hid _).symm

open Stacks.Cohomology.DerivedGlobalCupProduct (shiftCohomologyIsoR) in
/-- `hgroupModuleShiftIso_shift_apply`, with the bridge in degree `0` already computed. -/
theorem hgroupModuleShiftIso_shift_apply_of_eq
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c q : ℕ) (m : ℤ) (h : (q : ℤ) + (c : ℤ) = m) (h' : -(c : ℤ) + m = q)
    (y : Hgroup (structureSheafRing X) ⊤ q M)
    (z : cohomologyModule (moduleDerived (A := X.sheaf) (singleNat M 0)) (q : ℤ))
    (hz : (hgroupModuleShiftIso M 0 q q (by simp)).hom y = z) :
    (hgroupModuleShiftIso M c q m h).hom y =
      ((DerivedCategory.homologyFunctor _ m).map ((baseSections (baseRingedSpace X.sheaf)).map
          (DerivedCategory.Q.map (singleNatShiftIso M c).inv))).hom
        ((shiftCohomologyIsoR (S := baseRingedSpace X.sheaf)
          ((singleNat M 0).extend ComplexShape.embeddingUpNat)
          (-(c : ℤ)) m q h').inv z) := by
  subst hz
  exact hgroupModuleShiftIso_shift_apply M c q m h h' y

open Stacks.Cohomology.DerivedGlobalCupProduct (shiftCohomologyIsoR cohomologyCast) in
/-- The inverse shift identification read in two equal degrees. -/
theorem shiftCohomologyIsoR_inv_cohomologyCast {S : RingedSpace.{u, u}}
    (N : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) ℤ) (n a b₁ b₂ : ℤ)
    (h₁ : n + a = b₁) (h₂ : n + a = b₂) (e : b₂ = b₁)
    (z : cohomologyModule (DerivedCategory.Q.obj N) b₂) :
    (shiftCohomologyIsoR (S := S) N n a b₁ h₁).inv
        ((cohomologyCast (DerivedCategory.Q.obj N) e).hom z) =
      (shiftCohomologyIsoR (S := S) N n a b₂ h₂).inv z := by
  subst e
  rfl

/-- A pairing out of a tensor product of free modules of rank one, read at `1`, with a morphism
after the second class. At variables. -/
private lemma unitor_tensorHom_comp_apply_one {R : CommRingCat.{u}} {P Q Q' T : ModuleCat.{u} R}
    (x : P) (y : Q) (k : Q ⟶ Q') (g : P ⊗ Q' ⟶ T) :
    ((λ_ (ModuleCat.of R R)).inv ≫
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R P x) ⊗ₘ
          (ModuleCat.ofHom (LinearMap.toSpanSingleton R Q y) ≫ k)) ≫ g).hom (1 : R) =
      g.hom (x ⊗ₜ k.hom y) := by
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply, ModuleCat.MonoidalCategory.tensorHom_tmul]
  exact congrArg (fun t => g.hom t)
    (congrArg₂ (fun a b => a ⊗ₜ[(R : Type u)] b) (one_smul (R : Type u) x)
      (congrArg k.hom (one_smul (R : Type u) y)))

/-- `unitor_tensorHom_comp_apply_one` without the morphism. At variables. -/
private lemma unitor_tensorHom_apply_one {R : CommRingCat.{u}} {P Q T : ModuleCat.{u} R}
    (x : P) (y : Q) (g : P ⊗ Q ⟶ T) :
    ((λ_ (ModuleCat.of R R)).inv ≫
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R P x) ⊗ₘ
          ModuleCat.ofHom (LinearMap.toSpanSingleton R Q y)) ≫ g).hom (1 : R) =
      g.hom (x ⊗ₜ y) := by
  simpa using unitor_tensorHom_comp_apply_one x y (𝟙 _) g

/-- A unit of `ℤ` times a morphism of modules, on an element. At variables. -/
private lemma units_smul_hom_apply {R : Type u} [Ring R] {P Q : ModuleCat.{u} R} (ε : ℤˣ)
    (f : P ⟶ Q) (p : P) : (ε • f).hom p = ε • f.hom p := by
  rw [Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply, Units.smul_def]

/-- A composite of three maps of modules on an element, the first factor computed through a
fourth map and the second through it. At variables. -/
private lemma comp_comp_apply_of_eq {R : Type u} [Ring R] {A B B' C D : ModuleCat.{u} R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : B' ⟶ B) (g' : B' ⟶ C) (a : A) (b : B')
    (hf : f.hom a = k.hom b) (hg : g.hom (k.hom b) = g'.hom b) :
    (f ≫ g ≫ h).hom a = h.hom (g'.hom b) := by
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hf, hg]

/-- **(N) The cup product with the class of a global section placed in degree `c`.** -/
theorem canonicalPairingModule_sectionClass
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) (u : G.val.sections)
    (q c : ℕ) (x : Hgroup (structureSheafRing X) ⊤ q F) :
    (canonicalPairingModule (singleTensorMult μ 0 c c (zero_add c)) (q : ℤ) (c : ℤ)).hom
        ((hgroupModuleShiftIso F 0 q q (by simp)).hom x ⊗ₜ
          (hgroupModuleShiftIso G c 0 c (by simp)).hom (sectionClass u)) =
      ((q : ℤ) * (c : ℤ)).negOnePow •
        (hgroupModuleShiftIso H c q ((q : ℤ) + (c : ℤ)) rfl).hom
          ((Hfunctor (structureSheafRing X) ⊤ q).map (rightMulTensor μ u) x) := by
  let x' := (hgroupModuleShiftIso F 0 q q (by simp)).hom x
  let η₀ := (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap (S := baseRingedSpace X.sheaf)
      (unitComplexSectionMap G u) 0).hom
    ((Stacks.Cohomology.DerivedGlobalCupProduct.globalCycleClass (S := baseRingedSpace X.sheaf)
      (Stacks.Cohomology.DerivedGlobalCupProduct.unitCycleHom (baseRingedSpace X.sheaf))).hom 1)
  have hU : (hgroupModuleShiftIso G 0 0 ((0 : ℕ) : ℤ) (by simp)).hom (sectionClass u) = η₀ :=
    hgroupModuleShiftIso_sectionClass X G u
  have hG := (hgroupModuleShiftIso_shift_apply G c 0 (c : ℤ) (by simp) (by simp)
    (sectionClass u)).trans (congrArg (fun t => ((DerivedCategory.homologyFunctor _ (c : ℤ)).map
      ((baseSections (baseRingedSpace X.sheaf)).map
        (DerivedCategory.Q.map (singleNatShiftIso G c).inv))).hom
        ((Stacks.Cohomology.DerivedGlobalCupProduct.shiftCohomologyIsoR (S := X)
          ((singleNat G 0).extend ComplexShape.embeddingUpNat) (-(c : ℤ)) (c : ℤ) ((0 : ℕ) : ℤ)
            (by simp)).inv t)) hU)
  have hS := ConcreteCategory.congr_hom (canonicalPairingModule_singleTensorMult_shift μ c (q : ℤ) 0
    (c : ℤ) (by simp) (by simp)
    (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x'))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ η₀))) (1 : baseRing (baseRingedSpace X.sheaf))
  rw [unitor_tensorHom_comp_apply_one, units_smul_hom_apply, unitor_tensorHom_apply_one] at hS
  have hRU := canonicalPairingModule_unitComplexSectionMap μ u (q : ℤ) x'
  have hC0 := hgroupModuleShiftIso_naturality (rightMulTensor μ u) 0 q (q : ℤ) (by simp) x
  rw [moduleDerivedMap_singleFunctor_map] at hC0
  have hH := hgroupModuleShiftIso_shift_apply_of_eq H c q ((q : ℤ) + (c : ℤ)) rfl (by omega)
    ((Hfunctor (structureSheafRing X) ⊤ q).map (rightMulTensor μ u) x) _ hC0
  rw [hG]
  refine hS.trans ?_
  rw [hH]
  have e3 := shiftCohomologyIsoR_inv_cohomologyCast (S := baseRingedSpace X.sheaf)
    ((singleNat H 0).extend ComplexShape.embeddingUpNat) (-(c : ℤ)) ((q : ℤ) + (c : ℤ))
    ((q : ℤ) + 0) (q : ℤ) (by omega) (by omega) (add_zero (q : ℤ)).symm
    ((Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap (S := baseRingedSpace X.sheaf)
      (HomologicalComplex.extendMap ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map
        (rightMulTensor μ u)) ComplexShape.embeddingUpNat) (q : ℤ)).hom x')
  refine congrArg (((q : ℤ) * (c : ℤ)).negOnePow • ·) ?_
  exact comp_comp_apply_of_eq _ _ _ _ _ _ _ hRU e3

end StandardModel

end Stacks.DeRham.GysinCupHodge
