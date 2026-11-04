module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCupSectionClass
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupPairingNaturality

/-!
# The cup product with the Gysin class of a global section

Let `w : F ⊗ L ⟶ M` and `μ : F ⊗ G ⟶ GM` be multiplications matched (`EdgeTensorMatching`) by
two edge morphisms `eL : G[-c] ⟶ L[0]` and `eM : GM[-c] ⟶ M[0]`, and let `u` be a global section
of `G`. For `x ∈ H^q(X, F)`, the map on cohomology of right multiplication by `u` followed by `eM`
is `(-1)^{qc}` times the cup product of Cohomology, Section 0FKU, of `x` with the image under
`eL` of the class of `u`, both read through the bridge `hgroupModuleShiftIso`
(`cup_of_edgeTensorMatching`).

The proof moves the cup product across the edge morphisms (`canonicalPairingModule_edge`) and
computes the cup product with the class of `u` placed in degree `c`
(`canonicalPairingModule_sectionClass`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.DeRham.CohomologicalGysin
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

open DerivedCategory
open scoped CategoryTheory.Prod

/-- The algebra behind `moduleDerivedMap_comp`, at variables. -/
private lemma moduleDerivedMap_comp_aux {C : Type*} [Category* C] {P Q R S T U : C} (e : P ⟶ Q)
    (φ : Q ⟶ R) (ψ : R ⟶ S) (f : S ⟶ T) (g : U ≅ R) :
    e ≫ (φ ≫ ψ) ≫ f = (e ≫ φ ≫ g.inv) ≫ g.hom ≫ ψ ≫ f := by
  simp

/-- A functor into modules applied to a composite, on an element. -/
private lemma map_comp_apply' {C : Type*} [Category* C] {R : Type*} [Ring R]
    (G : C ⥤ ModuleCat R) {P Q T : C} (f : P ⟶ Q) (g : Q ⟶ T) (y : G.obj P) :
    (G.map (f ≫ g)).hom y = (G.map g).hom ((G.map f).hom y) := by
  simp

/-- Two functors applied to an identity, on an element. -/
private lemma map_map_id_apply {C D : Type*} [Category* C] [Category* D] {R : Type*} [Ring R]
    (G : C ⥤ D) (H : D ⥤ ModuleCat R) (P : C) (y : H.obj (G.obj P)) :
    (H.map (G.map (𝟙 P))).hom y = y := by
  simp

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}}

/-- **The cup product is natural in its second factor**, on elements. -/
theorem cupPairing_naturality_right_apply {Y : RingedSpace.{u, u}}
    (κ : Stacks.Cohomology.GlobalKunneth.GlobalCupProduct Y)
    {K M M' : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Y))}
    (v : M ⟶ M') (i j : ℤ) (x : cohomologyModule K i) (y : cohomologyModule M j) :
    (Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing κ K M' i j).hom
        (x ⊗ₜ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Y)) j).map
            ((baseSections Y).map v) y) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Y)) (i + j)).map
          ((baseSections Y).map
            ((Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
              Y.sheaf)).map (𝟙 K ×ₘ v)))).hom
        ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing κ K M i j).hom (x ⊗ₜ y)) := by
  have h := Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing_naturality_apply κ (𝟙 K) v i j x y
  simp only [CategoryTheory.Functor.map_id] at h
  exact h

/-- `moduleDerivedMap` takes composites to composites. -/
theorem moduleDerivedMap_comp {A F N : _root_.SheafOfModules.{u} (structureSheafRing X)}
    {a b n : ℕ}
    (φ : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (a : ℤ)).obj A ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (b : ℤ)).obj F)
    (ψ : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (b : ℤ)).obj F ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (n : ℤ)).obj N) :
    moduleDerivedMap (φ ≫ ψ) = moduleDerivedMap φ ≫ moduleDerivedMap ψ :=
  moduleDerivedMap_comp_aux _ _ _ _ _

/-- A linear map, and a unit of `ℤ` applied twice. -/
private lemma map_eq_unit_smul_map_unit_smul {R : Type*} [Ring R] {P Q : ModuleCat.{u} R}
    (f : P ⟶ Q) (ε : ℤˣ) (y : P) : f.hom y = ε • f.hom (ε • y) := by
  rw [Units.smul_def, Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul]

/-- `moduleDerivedMap` takes composites to composites, after a functor into modules, on
elements. -/
theorem moduleDerivedMap_comp_apply {R : Type*} [Ring R]
    (Φ : DerivedCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace X.sheaf))) ⥤ ModuleCat.{u} R)
    {A F N : _root_.SheafOfModules.{u} (structureSheafRing X)} {a b n : ℕ}
    (φ : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (a : ℤ)).obj A ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (b : ℤ)).obj F)
    (ψ : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (b : ℤ)).obj F ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (n : ℤ)).obj N)
    (y : Φ.obj (moduleDerived (A := X.sheaf) (singleNat A a))) :
    (Φ.map (moduleDerivedMap (φ ≫ ψ))).hom y =
      (Φ.map (moduleDerivedMap ψ)).hom ((Φ.map (moduleDerivedMap φ)).hom y) := by
  rw [moduleDerivedMap_comp, Φ.map_comp]
  rfl

/-- The cup product of Section 0FKU along a multiplication of single complexes, written through
the pairing of the global cup product. -/
theorem canonicalPairingModule_apply
    {K L M : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) ℕ}
    (m : ((tensorBifunctorNat (A := X.sheaf)).obj K).obj L ⟶ M) (i j : ℤ)
    (a : cohomologyModule (moduleDerived (A := X.sheaf) K) i)
    (b : cohomologyModule (moduleDerived (A := X.sheaf) L) j) :
    (canonicalPairingModule m i j).hom (a ⊗ₜ b) =
      ((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections (baseRingedSpace X.sheaf)).map
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          (baseRingedSpace X.sheaf).sheaf).toTensor
          (K.extend ComplexShape.embeddingUpNat) (L.extend ComplexShape.embeddingUpNat) ≫
          DerivedCategory.Q.map (multiplicationInt m)))).hom
        ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
          (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (baseRingedSpace X.sheaf))
          (moduleDerived (A := X.sheaf) K) (moduleDerived (A := X.sheaf) L) i j).hom (a ⊗ₜ b)) :=
  rfl

/-- **The edge matching, on cohomology.**  Across the two Gysin edge morphisms, the cup product
along `μ` with a class placed in degree `c` becomes the cup product along `w` with its image. -/
theorem canonicalPairingModule_edge
    {F L M G GM :
      _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (c : ℕ) (w : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj L ⟶ M)
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ GM)
    (eL : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj G ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj L)
    (eM : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj GM ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj M)
    (hM : EdgeTensorMatching c w μ eL eM) (i : ℤ)
    (a : cohomologyModule (moduleDerived (A := X.sheaf) (singleNat F 0)) i)
    (b : cohomologyModule (moduleDerived (A := X.sheaf) (singleNat G c)) (c : ℤ)) :
    ((DerivedCategory.homologyFunctor _ (i + (c : ℤ))).map
        ((baseSections (baseRingedSpace X.sheaf)).map (moduleDerivedMap eM))).hom
      ((canonicalPairingModule (singleTensorMult μ 0 c c (zero_add c)) i (c : ℤ)).hom (a ⊗ₜ b)) =
      (canonicalPairingModule (singleTensorMult w 0 0 0 rfl) i (c : ℤ)).hom
        (a ⊗ₜ ((DerivedCategory.homologyFunctor _ (c : ℤ)).map
          ((baseSections (baseRingedSpace X.sheaf)).map (moduleDerivedMap eL))).hom b) := by
  have hU : (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (baseRingedSpace X.sheaf).sheaf)).map
        (𝟙 (moduleDerived (A := X.sheaf) (singleNat F 0)) ×ₘ moduleDerivedMap eL) =
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (baseRingedSpace X.sheaf).sheaf).obj
        (moduleDerived (A := X.sheaf) (singleNat F 0))).map (moduleDerivedMap eL) :=
    Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left _ _ _
  have heq : ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (baseRingedSpace X.sheaf).sheaf).toTensor
        ((singleNat F 0).extend ComplexShape.embeddingUpNat)
        ((singleNat G c).extend ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (multiplicationInt (singleTensorMult μ 0 c c (zero_add c)))) ≫
        moduleDerivedMap eM =
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (baseRingedSpace X.sheaf).sheaf)).map
          (𝟙 (moduleDerived (A := X.sheaf) (singleNat F 0)) ×ₘ moduleDerivedMap eL) ≫
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (baseRingedSpace X.sheaf).sheaf).toTensor
        ((singleNat F 0).extend ComplexShape.embeddingUpNat)
        ((singleNat L 0).extend ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (multiplicationInt (singleTensorMult w 0 0 0 rfl)) := by
    rw [hU]
    exact (Category.assoc _ _ _).trans hM.symm
  have hnat := cupPairing_naturality_right_apply
    (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (baseRingedSpace X.sheaf))
    (moduleDerivedMap eL) i (c : ℤ) a b
  refine Eq.trans ?_ (congrArg _ hnat).symm
  have key := @map_comp_apply' _ _ _ _
    (baseSections (baseRingedSpace X.sheaf) ⋙ DerivedCategory.homologyFunctor _ (i + (c : ℤ)))
  refine (key _ _ _).symm.trans (Eq.trans ?_ (key _ _ _))
  exact congrArg (fun f => (((baseSections (baseRingedSpace X.sheaf) ⋙
    DerivedCategory.homologyFunctor _ (i + (c : ℤ))).map f).hom _)) heq

/-- **The cup product with the image of the class of a global section under an edge morphism.**
For multiplications `w` and `μ` matched by edge morphisms `eL`, `eM`, a global section `u` of `G`
and `x ∈ H^q(X, F)`, the class of `x` multiplied by `u` and pushed along `eM` is `(-1)^{qc}`
times the cup product along `w` of `x` with the class of `u` pushed along `eL`. The sign comes
from the sign-free identification `H^q(X, A) ≅ H^{q+c}(RΓ(X, A[-c]))` of the bridge, through
`Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_shift₂`. -/
theorem cup_of_edgeTensorMatching
    {F L M G GM :
      _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (c q : ℕ) (w : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj L ⟶ M)
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ GM)
    (eL : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj G ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj L)
    (eM : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj GM ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj M)
    (hM : EdgeTensorMatching c w μ eL eM) (u : G.val.sections)
    (x : Hgroup (structureSheafRing X) ⊤ q F) :
    (hgroupModuleShiftIso M 0 (q + c) ((q : ℤ) + (c : ℤ)) (by push_cast; ring)).hom
        (cohomologyMapOfSingleHom X F M c q
          ((singleFunctor _ (c : ℤ)).map (rightMulTensor μ u) ≫ eM) x) =
      ((q : ℤ) * (c : ℤ)).negOnePow •
        (canonicalPairingModule (singleTensorMult w 0 0 0 rfl) (q : ℤ) (c : ℤ)).hom
          ((hgroupModuleShiftIso F 0 q q (by simp)).hom x ⊗ₜ
            (hgroupModuleShiftIso L 0 (0 + c) c (by push_cast; ring)).hom
              (cohomologyMapOfSingleHom X G L c 0 eL (sectionClass u))) := by
  -- the left-hand side
  have h1 := hgroupModuleShiftIso_cohomologyMapOfSingleHom F M c q ((q : ℤ) + (c : ℤ)) rfl
    (by push_cast; ring) ((singleFunctor _ (c : ℤ)).map (rightMulTensor μ u) ≫ eM) x
  have h2 := moduleDerivedMap_comp_apply
    (baseSections (baseRingedSpace X.sheaf) ⋙
      DerivedCategory.homologyFunctor _ ((q : ℤ) + (c : ℤ)))
    ((singleFunctor _ (c : ℤ)).map (rightMulTensor μ u)) eM
    ((hgroupModuleShiftIso F c q ((q : ℤ) + (c : ℤ)) rfl).hom x)
  have h3 := hgroupModuleShiftIso_naturality (rightMulTensor μ u) c q ((q : ℤ) + (c : ℤ)) rfl x
  -- the right-hand side
  have h4 := canonicalPairingModule_sectionClass μ u q c x
  have h5 := hgroupModuleShiftIso_cohomologyMapOfSingleHom G L c 0 (c : ℤ) (by simp)
    (by push_cast; ring) eL (sectionClass u)
  have h6 := canonicalPairingModule_edge c w μ eL eM hM (q : ℤ)
    ((hgroupModuleShiftIso F 0 q q (by simp)).hom x)
    ((hgroupModuleShiftIso G c 0 c (by simp)).hom (sectionClass u))
  rw [h5, ← h6, h4, h1]
  exact h2.trans ((congrArg _ h3.symm).trans (map_eq_unit_smul_map_unit_smul _ _ _))

end StandardModel
end Stacks.DeRham.GysinCupHodge
