module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorUnitors
public import StacksFrontier.AlgebraicGeometry.Cohomology.FlasqueReductionOfTheCupProductSquare
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift

/-!
# The cup product with the unit class is the identity

Let `(S, 𝒪_S)` be a ringed space and `A = Γ(S, 𝒪_S)`. The structure sheaf placed in degree zero
acts on every complex `ℳ^•` of `𝒪_S`-modules, `μ : Tot(𝒪_S[0] ⊗ ℳ^•) ≅ ℳ^•`, by the left unitor of
the tensor product sheaf in each degree. This file proves that the cup product of Cohomology,
Section 0FKU with the class `1 ∈ H⁰(S, 𝒪_S)` of the unit section, followed by `μ`, is the identity
of `Hʲ(S, ℳ^•)` for every bounded below `ℳ^•`.

The proof is the cocycle description of the cup product, Tag 0FP3: on a flasque resolution
`ℳ^• ⟶ ℳ₁^•` every class is the class of a global cocycle `w`
(`Stacks.Cohomology.DerivedGlobalCupProduct.exists_globalCycleClass_eq_of_isFlasque`), the cup
product of the classes of `1` and `w` is the class of `1 ⊗ w`
(`Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_globalCycleClass`), and `μ` sends
`1 ⊗ w` to `w`; both the cup product and `μ` are natural in `ℳ^•`.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.unitLeftAction`: `μ : Tot(𝒪_S[0] ⊗ ℳ^•) ⟶ ℳ^•`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.unitClass`: the class `1 ∈ H⁰(S, 𝒪_S)` of the unit
  section.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.cycles_naiveCupProductEval_unitLeftAction`: on global
  cocycles, the naive cup product followed by `μ` is the module action of sections.
* `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_unitClass_globalCycleClass`: the unit
  law on the class of a global cocycle.
* `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_unitClass`: **the unit law**
  `1 ∪ η = η`, after `μ`, for every bounded below `ℳ^•`.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

-- `TopCat.Sheaf` and the ring-sheaf spellings are crossed by the tensor product sheaf and its
-- additivity instances.
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable (S : RingedSpace.{u, u})

/-- The left unitor `𝒪_S ⊗ ℱ ⟶ ℱ` of the tensor product sheaf, as a natural transformation. -/
def sheafTensorUnitLeft :
    (sheafTensor.{u, u, u, u, u} S.sheaf).obj (SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf)) ⟶
      𝟭 _ where
  app A := (Stacks.RingedSpace.tensorSheafUnitLeftIso S A).hom
  naturality {A B} f := by
    have h := @MonoidalCategory.leftUnitor_naturality _ _
      (SheafOfModules.monoidalCategorySheafTensor ⟨S.presheaf, S.IsSheaf⟩) A B f
    exact (congrArg (fun g => ((sheafTensor.{u, u, u, u, u} S.sheaf).obj
        (SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf))).map f ≫ g)
      (Stacks.RingedSpace.leftUnitor_sheafTensor_eq S B).symm).trans
      (h.trans (congrArg (· ≫ f) (Stacks.RingedSpace.leftUnitor_sheafTensor_eq S A)))

/-- `⊗_{𝒪_S}` preserves zero morphisms in its first variable, being additive. -/
local instance preservesZeroMorphisms_sheafTensor :
    (sheafTensor.{u, u, u, u, u} S.sheaf).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- `ℱ ⊗_{𝒪_S} -` preserves zero morphisms, being additive. -/
local instance preservesZeroMorphisms_sheafTensor_obj
    (M : SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) :
    ((sheafTensor.{u, u, u, u, u} S.sheaf).obj M).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The structure sheaf placed in degree zero. -/
abbrev unitSingleComplex : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj (SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf))

/-- **The action `μ : Tot(𝒪_S[0] ⊗ ℳ^•) ⟶ ℳ^•` of the structure sheaf in degree zero**: the
identification of the total complex with `𝒪_S ⊗ -` applied degreewise, followed by the left
unitor in each degree. -/
def unitLeftAction (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) :
    HomologicalComplex.mapBifunctor (unitSingleComplex S) M (sheafTensor.{u, u, u, u, u} S.sheaf)
        (ComplexShape.up ℤ) ⟶
      M :=
  (HomologicalComplex.mapBifunctorSingleLeftIso (sheafTensor.{u, u, u, u, u} S.sheaf) _ M).hom ≫
    (NatTrans.mapHomologicalComplex (sheafTensorUnitLeft S) (ComplexShape.up ℤ)).app M ≫
      ((Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app M)

/-- In degree `i`, the action `μ` is the identification `Tot(𝒪_S[0] ⊗ ℳ^•)ⁱ ≅ 𝒪_S ⊗ ℳⁱ` followed
by the left unitor `𝒪_S ⊗ ℳⁱ ⟶ ℳⁱ`. -/
theorem unitLeftAction_f (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (i : ℤ) :
    (unitLeftAction S M).f i =
      (HomologicalComplex.singleLeftXIso (sheafTensor.{u, u, u, u, u} S.sheaf)
          (SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf)) M i).hom ≫
        (sheafTensorUnitLeft S).app (M.X i) := by
  simp only [unitLeftAction, HomologicalComplex.mapBifunctorSingleLeftIso,
    HomologicalComplex.singleLeftIsoMapBifunctor, HomologicalComplex.Hom.isoOfComponents,
    Functor.mapHomologicalComplex_obj_X, SheafOfModules.Tensor.sheafTensor_obj_obj, Iso.symm_mk,
    HomologicalComplex.comp_f, Functor.id_obj, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f]
  exact congrArg (fun t => _ ≫ t) (Category.comp_id _)

/-- **The action of `𝒪_S[0]` is natural** in the complex acted on. -/
theorem unitLeftAction_naturality
    {M M' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} (g : M ⟶ M') :
    HomologicalComplex.mapBifunctorMap (𝟙 (unitSingleComplex S)) g
        (sheafTensor.{u, u, u, u, u} S.sheaf) (ComplexShape.up ℤ) ≫ unitLeftAction S M' =
      unitLeftAction S M ≫ g := by
  apply HomologicalComplex.hom_ext
  intro i
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, unitLeftAction_f, unitLeftAction_f,
    ← cancel_epi (HomologicalComplex.singleLeftXIso (sheafTensor.{u, u, u, u, u} S.sheaf)
      (SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf)) M i).inv,
    Category.assoc, Iso.inv_hom_id_assoc, HomologicalComplex.singleLeftXIso_inv, Category.assoc,
    HomologicalComplex.singleLeftι, HomologicalComplex.ι_mapBifunctorMap_assoc]
  rw [← HomologicalComplex.singleLeftι, HomologicalComplex.singleLeftι_singleLeftXIso_hom_assoc,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf))
  refine (NatTrans.naturality_assoc ((sheafTensor.{u, u, u, u, u} S.sheaf).map e.inv) (g.f i)
    (((sheafTensor.{u, u, u, u, u} S.sheaf).map e.hom).app (M'.X i) ≫
      (sheafTensorUnitLeft S).app (M'.X i))).symm.trans ?_
  rw [← NatTrans.comp_app_assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  exact (sheafTensorUnitLeft S).naturality (g.f i)

/-! ### The unit class and the action of `𝒪_S[0]` on a summand -/

section UnitClass

open Stacks.Cech.SheafTensorPairing (evalComplex pairEval naiveCupProductEval)
open Stacks.Cohomology.GlobalKunneth

variable {S}

/-- The identification `𝒪_S[0]⁰ ≅ 𝒪_S` of the degree-zero term of the structure sheaf placed in
degree zero. -/
abbrev unitSingleComplexXIso :
    (unitSingleComplex S).X 0 ≅ SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf) :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf))

/-- The global sections of the structure sheaf are the base ring, as a module over itself. -/
abbrev unitSections :
    ModuleCat.of (baseRing S) (baseRing S) ⟶
      (SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).obj
        (SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf)) :=
  𝟙 (ModuleCat.of (baseRing S) (baseRing S))

/-- The unit section `1 ∈ Γ(S, 𝒪_S)`, as a degree-zero cochain of `Γ(S, 𝒪_S[0])`: a morphism out
of the base ring, with value `1` at `1`. -/
def unitCochain :
    ModuleCat.of (baseRing S) (baseRing S) ⟶
      (evalComplex S.sheaf ⊤ (unitSingleComplex S)).X 0 :=
  unitSections ≫ (SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
    (unitSingleComplexXIso (S := S)).inv

/-- The unit section is a cocycle of `Γ(S, 𝒪_S[0])`. -/
def unitSingleCycle :
    ModuleCat.of (baseRing S) (baseRing S) ⟶
      (evalComplex S.sheaf ⊤ (unitSingleComplex S)).cycles 0 :=
  (evalComplex S.sheaf ⊤ (unitSingleComplex S)).liftCycles unitCochain 1 (by simp)
    ((Functor.map_isZero (SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ 1 (by omega))).eq_of_tgt _ _)

/-- The unit cocycle, viewed as a cochain, is the unit cochain. -/
@[reassoc (attr := simp)]
theorem unitSingleCycle_iCycles :
    unitSingleCycle (S := S) ≫ (evalComplex S.sheaf ⊤ (unitSingleComplex S)).iCycles 0 =
      unitCochain :=
  HomologicalComplex.liftCycles_i (evalComplex S.sheaf ⊤ (unitSingleComplex S)) unitCochain 1 _ _

/-- **The unit class** `1 ∈ H⁰(S, 𝒪_S)`, the class of the global cocycle `1` of `𝒪_S[0]`. -/
def unitClass :
    ModuleCat.of (baseRing S) (baseRing S) ⟶
      cohomologyModule (DerivedCategory.Q.obj (unitSingleComplex S)) 0 :=
  globalCycleClass unitSingleCycle

/-- **The action of `𝒪_S[0]` on a summand**: on the summand of bidegree `(0, j)` of
`Tot(𝒪_S[0] ⊗ ℳ^•)` it is the left unitor `𝒪_S ⊗ ℳʲ ⟶ ℳʲ`, read in the degree `n = 0 + j`. -/
theorem ιMapBifunctor_unitLeftAction_f
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (j n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (0, j) = n) :
    HomologicalComplex.ιMapBifunctor (unitSingleComplex S) M (sheafTensor.{u, u, u, u, u} S.sheaf)
        (ComplexShape.up ℤ) 0 j n h ≫ (unitLeftAction S M).f n =
      ((sheafTensor.{u, u, u, u, u} S.sheaf).map (unitSingleComplexXIso (S := S)).hom).app (M.X j) ≫
        (sheafTensorUnitLeft S).app (M.X j) ≫
          eqToHom (congrArg M.X (show j = n by simpa using h)) := by
  obtain rfl : n = j := by simpa using h.symm
  rw [unitLeftAction_f, eqToHom_refl, Category.comp_id]
  exact HomologicalComplex.singleLeftι_singleLeftXIso_hom_assoc _ _ _ _ _

/-- **The map of global sections `Γ(S, 𝒪_S) ⊗ Γ(S, ℱ) ⟶ Γ(S, 𝒪_S ⊗ ℱ)`, followed by the left
unitor, is the module action** `r ⊗ x ↦ r • x`. -/
theorem pairEval_unit_sheafTensorUnitLeft_apply
    (F : SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))
    (r : (ringSheaf.{u, u, u} S.sheaf).obj.obj (op ⊤)) (x : F.val.obj (op ⊤)) :
    ((SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
        ((sheafTensorUnitLeft S).app F)).hom
      ((pairEval S.sheaf ⊤ (SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf)) F).hom
        (r ⊗ₜ x)) = r • x :=
  Stacks.RingedSpace.tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul S F (op ⊤) r x

/-- Moving a family of cocycles to an equal degree commutes with the inclusion of cocycles. -/
@[reassoc]
theorem eqToHom_iCycles {R : Type u} [Ring R] (Y : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ}
    (h : a = b) :
    eqToHom (congrArg (fun n => Y.cycles n) h) ≫ Y.iCycles b =
      Y.iCycles a ≫ eqToHom (congrArg Y.X h) := by
  subst h
  simp

/-- **The naive cup product with a cocycle of `𝒪_S[0]`, followed by the action of `𝒪_S[0]`**:
on cocycles `z` of `Γ(S, 𝒪_S[0])` in degree `0` and `w` of `Γ(S, ℳ^•)` in degree `j` it is the
module action of the section `z` on the section `w`, read in the degree `0 + j`. -/
theorem cycles_naiveCupProductEval_unitLeftAction
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (j : ℤ)
    {A B : ModuleCat.{u} (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤)}
    (z : A ⟶ (evalComplex S.sheaf ⊤ (unitSingleComplex S)).cycles 0)
    (w : B ⟶ (evalComplex S.sheaf ⊤ M).cycles j)
    (z₀ : ((Stacks.Cech.CupProduct.tensorModules
          (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤)).obj
            ((evalComplex S.sheaf ⊤ (unitSingleComplex S)).cycles 0)).obj
          ((evalComplex S.sheaf ⊤ M).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (evalComplex S.sheaf ⊤ (unitSingleComplex S))
            (evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
              (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (0 + j))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor (evalComplex S.sheaf ⊤ (unitSingleComplex S))
            (evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
              (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (0 + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((evalComplex S.sheaf ⊤ (unitSingleComplex S)).iCycles 0)
            ((evalComplex S.sheaf ⊤ M).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (evalComplex S.sheaf ⊤ (unitSingleComplex S))
            (evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
              (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
            (ComplexShape.up ℤ) 0 j (0 + j) rfl) :
    Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ z w ≫ z₀ ≫
        HomologicalComplex.cyclesMap (naiveCupProductEval S.sheaf ⊤ (unitSingleComplex S) M)
          (0 + j) ≫
        HomologicalComplex.cyclesMap (((SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf)
          (op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).map (unitLeftAction S M)) (0 + j) ≫
        (evalComplex S.sheaf ⊤ M).iCycles (0 + j) =
      Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
          (z ≫ (evalComplex S.sheaf ⊤ (unitSingleComplex S)).iCycles 0 ≫
            (SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
              (unitSingleComplexXIso (S := S)).hom)
          (w ≫ (evalComplex S.sheaf ⊤ M).iCycles j) ≫
        pairEval S.sheaf ⊤ (SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf)) (M.X j) ≫
        (SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
          ((sheafTensorUnitLeft S).app (M.X j) ≫ eqToHom (congrArg M.X (zero_add j).symm)) := by
  rw [HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i_assoc, reassoc_of% hz₀,
    reassoc_of% (Stacks.Cech.SheafTensorPairing.ι_naiveCupProductEval_f S.sheaf ⊤
      (unitSingleComplex S) M 0 j (0 + j) rfl), Functor.mapHomologicalComplex_map_f,
    ← Functor.map_comp, ιMapBifunctor_unitLeftAction_f, Functor.map_comp, Functor.map_comp]
  have hn := Stacks.Cech.SheafTensorPairing.pairEval_naturality S.sheaf ⊤
    (unitSingleComplexXIso (S := S)).hom (𝟙 (M.X j))
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hn
  rw [← reassoc_of% hn]
  simp only [Stacks.Cech.SheafTensorPairing.tensorMap, Functor.map_comp, NatTrans.comp_app,
    Category.assoc]
  simp only [← NatTrans.naturality_assoc]
  rfl

/-- Two morphisms out of the free module of rank one agree as soon as they agree at `1`. -/
theorem hom_ext_of_apply_one {R : Type u} [Ring R] {N : ModuleCat.{u} R}
    {f g : ModuleCat.of R R ⟶ N} (h : f.hom 1 = g.hom 1) : f = g :=
  ModuleCat.hom_ext (LinearMap.ext_ring h)

/-- The class of a family of global cocycles moved to an equal degree is its class moved to that
degree. -/
theorem globalCycleClass_eqToHom {T : ModuleCat.{u} (baseRing S)}
    {N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} {a b : ℤ}
    (z : T ⟶ (evalComplex S.sheaf ⊤ N).cycles a) (h : a = b) :
    globalCycleClass (z ≫ eqToHom (congrArg (fun n => (evalComplex S.sheaf ⊤ N).cycles n) h)) =
      globalCycleClass z ≫
        eqToHom (congrArg (fun n => cohomologyModule (DerivedCategory.Q.obj N) n) h) := by
  subst h
  exact (congrArg globalCycleClass (Category.comp_id z)).trans (Category.comp_id _).symm

/-- The unit cochain followed by `𝒪_S[0]⁰ ≅ 𝒪_S` is the identification of the global sections of
`𝒪_S` with the base ring. -/
theorem unitCochain_comp_unitComplexXIso :
    unitCochain (S := S) ≫ (SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
      (unitSingleComplexXIso (S := S)).hom = unitSections :=
  (Category.assoc _ _ _).trans ((congrArg (unitSections ≫ ·)
    ((Functor.map_comp _ _ _).symm.trans ((congrArg
      (SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
      (unitSingleComplexXIso (S := S)).inv_hom_id).trans
        (CategoryTheory.Functor.map_id _ _)))).trans
    (Category.comp_id _))

/-- **The naive cup product of the unit cocycle with a global cocycle, followed by the action of
`𝒪_S[0]`, is that cocycle**, read in the degree `0 + j`. -/
theorem unitSingleCycle_naiveCupProductEval_unitLeftAction
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (j : ℤ)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (evalComplex S.sheaf ⊤ M).cycles j)
    (z₀ : ((Stacks.Cech.CupProduct.tensorModules
          (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤)).obj
            ((evalComplex S.sheaf ⊤ (unitSingleComplex S)).cycles 0)).obj
          ((evalComplex S.sheaf ⊤ M).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (evalComplex S.sheaf ⊤ (unitSingleComplex S))
            (evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
              (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (0 + j))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor (evalComplex S.sheaf ⊤ (unitSingleComplex S))
            (evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
              (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (0 + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((evalComplex S.sheaf ⊤ (unitSingleComplex S)).iCycles 0)
            ((evalComplex S.sheaf ⊤ M).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (evalComplex S.sheaf ⊤ (unitSingleComplex S))
            (evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
              (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
            (ComplexShape.up ℤ) 0 j (0 + j) rfl) :
    ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ unitSingleCycle w ≫ z₀ ≫
        HomologicalComplex.cyclesMap (naiveCupProductEval S.sheaf ⊤ (unitSingleComplex S) M)
          (0 + j)) ≫
        HomologicalComplex.cyclesMap (((SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf)
          (op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).map (unitLeftAction S M)) (0 + j) =
      w ≫ eqToHom (congrArg (fun n => (evalComplex S.sheaf ⊤ M).cycles n) (zero_add j).symm) := by
  have key := cycles_naiveCupProductEval_unitLeftAction M j
    (A := ModuleCat.of (baseRing S) (baseRing S)) (B := ModuleCat.of (baseRing S) (baseRing S))
    unitSingleCycle w z₀ hz₀
  refine (cancel_mono ((evalComplex S.sheaf ⊤ M).iCycles (0 + j))).1 ?_
  refine hom_ext_of_apply_one ?_
  have k1 := ConcreteCategory.congr_hom key
    ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv.hom 1)
  have k2 := ConcreteCategory.congr_hom
    (eqToHom_iCycles (evalComplex S.sheaf ⊤ M) (zero_add j).symm) (w.hom 1)
  have h1 : (unitSingleCycle ≫ (evalComplex S.sheaf ⊤ (unitSingleComplex S)).iCycles 0 ≫
      (SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
        (unitSingleComplexXIso (S := S)).hom).hom 1 =
      (1 : (ringSheaf.{u, u, u} S.sheaf).obj.obj (op ⊤)) :=
    (ConcreteCategory.congr_hom (unitSingleCycle_iCycles_assoc (S := S) _) 1).trans
      (ConcreteCategory.congr_hom unitCochain_comp_unitComplexXIso 1)
  have k3 : ((SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
        ((sheafTensorUnitLeft S).app (M.X j))).hom
      ((pairEval S.sheaf ⊤ (SheafOfModules.unit (ringSheaf.{u, u, u} S.sheaf)) (M.X j)).hom
        ((unitSingleCycle ≫ (evalComplex S.sheaf ⊤ (unitSingleComplex S)).iCycles 0 ≫
          (SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
            (unitSingleComplexXIso (S := S)).hom).hom 1 ⊗ₜ
          (w ≫ (evalComplex S.sheaf ⊤ M).iCycles j).hom 1)) =
      ((evalComplex S.sheaf ⊤ M).iCycles j).hom (w.hom 1) := by
    rw [h1]
    exact (pairEval_unit_sheafTensorUnitLeft_apply (M.X j) 1 _).trans (one_smul _ _)
  refine k1.trans (Eq.trans ?_ k2.symm)
  refine (congrArg (fun x => ((SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
    (eqToHom (congrArg M.X (zero_add j).symm))).hom x) k3).trans ?_
  rw [eqToHom_map]
  rfl

/-- **The unit law on the class of a global cocycle**: the cup product of `1 ∈ H⁰(S, 𝒪_S)` with
the class of a global cocycle `w` of `Γ(S, ℳ^•)`, followed by the action of `𝒪_S[0]`, is the
class of `w`. -/
theorem totalCupPairing_unitClass_globalCycleClass
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (j : ℤ)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (evalComplex S.sheaf ⊤ M).cycles j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (unitClass ⊗ₘ globalCycleClass w) ≫ totalCupPairing (unitSingleComplex S) M 0 j ≫
        (DerivedCategory.homologyFunctor _ (0 + j)).map ((baseSections S).map
          (DerivedCategory.Q.map (unitLeftAction S M))) =
      globalCycleClass w ≫
        eqToHom (congrArg (fun n => cohomologyModule (DerivedCategory.Q.obj M) n)
          (zero_add j).symm) := by
  obtain ⟨z₀, hz₀⟩ := exists_tensorCycles_naive (unitSingleComplex S) M 0 j
  refine (totalCupPairing_globalCycleClass_naive_assoc (unitSingleComplex S) M unitSingleCycle w
    z₀ hz₀ _).trans ?_
  refine (globalCycleClass_mapR _ (unitLeftAction S M)).trans ?_
  refine (congrArg globalCycleClass
    (unitSingleCycle_naiveCupProductEval_unitLeftAction M j w z₀ hz₀)).trans ?_
  exact globalCycleClass_eqToHom w (zero_add j).symm

/-- `Hⁿ(RΓ(S, f))` commutes with moving the degree. -/
theorem homology_map_eqToHom
    {K L : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} (f : K ⟶ L)
    {a b : ℤ} (h : a = b) :
    (DerivedCategory.homologyFunctor _ a).map ((baseSections S).map (DerivedCategory.Q.map f)) ≫
        eqToHom (congrArg (fun n => cohomologyModule (DerivedCategory.Q.obj L) n) h) =
      eqToHom (congrArg (fun n => cohomologyModule (DerivedCategory.Q.obj K) n) h) ≫
        (DerivedCategory.homologyFunctor _ b).map
          ((baseSections S).map (DerivedCategory.Q.map f)) := by
  subst h
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Given `hμ ≫ ha = hT ≫ hμ₁`, `L ≫ X ≫ c ≫ hT = L ≫ Y ≫ c₁`,
`L ≫ Y ≫ c₁ ≫ hμ₁ = (η ≫ haj) ≫ e₁` and `haj ≫ e₁ = e₂ ≫ ha`, the composites
`L ≫ X ≫ c ≫ hμ ≫ ha` and `η ≫ e₂ ≫ ha` agree. -/
theorem unitClass_paste {C : Type*} [Category* C] {P Q R T U W T' R' A B : C} (L : P ⟶ Q)
    (X : Q ⟶ R) (c : R ⟶ T) (hμ : T ⟶ U) (ha : U ⟶ W) (hT : T ⟶ T') (hμ₁ : T' ⟶ W)
    (Y : Q ⟶ R') (c₁ : R' ⟶ T') (η : P ⟶ A) (haj : A ⟶ B) (e₁ : B ⟶ W) (e₂ : A ⟶ U)
    (h₁ : hμ ≫ ha = hT ≫ hμ₁) (h₂ : L ≫ X ≫ c ≫ hT = L ≫ Y ≫ c₁)
    (h₃ : L ≫ Y ≫ c₁ ≫ hμ₁ = (η ≫ haj) ≫ e₁) (h₄ : haj ≫ e₁ = e₂ ≫ ha) :
    (L ≫ X ≫ c ≫ hμ) ≫ ha = (η ≫ e₂) ≫ ha := by
  simp only [Category.assoc] at h₃ ⊢
  rw [h₁, reassoc_of% h₂, h₃, h₄]

/-- **The cup product with the unit class is the identity.** For a bounded below complex `ℳ^•`
of `𝒪_S`-modules and a class `η ∈ Hʲ(S, ℳ^•)`, the cup product of Cohomology, Section 0FKU of
`1 ∈ H⁰(S, 𝒪_S)` with `η`, followed by the action `Tot(𝒪_S[0] ⊗ ℳ^•) ⟶ ℳ^•` of `𝒪_S[0]`, is `η`
(read in the degree `0 + j`). -/
theorem totalCupPairing_unitClass
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (hM : ∃ n : ℤ, M.IsStrictlyGE n) (j : ℤ)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj M) j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (unitClass ⊗ₘ η) ≫ totalCupPairing (unitSingleComplex S) M 0 j ≫
        (DerivedCategory.homologyFunctor _ (0 + j)).map ((baseSections S).map
          (DerivedCategory.Q.map (unitLeftAction S M))) =
      η ≫ eqToHom (congrArg (fun n => cohomologyModule (DerivedCategory.Q.obj M) n)
        (zero_add j).symm) := by
  obtain ⟨M₁, -, a, -, ha, -, hM₁, -, hfl, -, -⟩ :=
    Stacks.Cohomology.FlasqueReduction.exists_flasqueResolution_quasiIso_tensor S M M hM hM
  have h1 : IsIso (DerivedCategory.Q.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := a)).2 ha
  have h2 : IsIso ((baseSections S).map (DerivedCategory.Q.map a)) :=
    ((baseSections S).mapIso (@asIso _ _ _ _ (DerivedCategory.Q.map a) h1)).isIso_hom
  have h3 : IsIso ((DerivedCategory.homologyFunctor _ (0 + j)).map
      ((baseSections S).map (DerivedCategory.Q.map a))) :=
    ((DerivedCategory.homologyFunctor _ (0 + j)).mapIso (@asIso _ _ _ _
      ((baseSections S).map (DerivedCategory.Q.map a)) h2)).isIso_hom
  refine (cancel_mono ((DerivedCategory.homologyFunctor _ (0 + j)).map
    ((baseSections S).map (DerivedCategory.Q.map a)))).1 ?_
  obtain ⟨w, hw⟩ := exists_globalCycleClass_eq_of_isFlasque M₁ hM₁ hfl j
    (η ≫ (DerivedCategory.homologyFunctor _ j).map ((baseSections S).map (DerivedCategory.Q.map a)))
  have e1 := unitLeftAction_naturality S a
  have e2 := totalCupPairing_naturality' (𝟙 (unitSingleComplex S)) a 0 j unitClass η
  have e3 := totalCupPairing_unitClass_globalCycleClass M₁ j w
  rw [hw] at e3
  have e5 : unitClass (S := S) ≫ (DerivedCategory.homologyFunctor _ 0).map
      ((baseSections S).map (DerivedCategory.Q.map (𝟙 (unitSingleComplex S)))) = unitClass :=
    (congrArg (unitClass ≫ ·) ((congrArg (fun t => (DerivedCategory.homologyFunctor _ 0).map
      ((baseSections S).map t)) (DerivedCategory.Q.map_id _)).trans
        ((congrArg (DerivedCategory.homologyFunctor _ 0).map ((baseSections S).map_id _)).trans
          ((DerivedCategory.homologyFunctor _ 0).map_id _)))).trans (Category.comp_id _)
  rw [e5] at e2
  have e4 : (DerivedCategory.homologyFunctor _ (0 + j)).map ((baseSections S).map
        (DerivedCategory.Q.map (unitLeftAction S M))) ≫
      (DerivedCategory.homologyFunctor _ (0 + j)).map ((baseSections S).map
        (DerivedCategory.Q.map a)) =
      (DerivedCategory.homologyFunctor _ (0 + j)).map ((baseSections S).map
        (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 (unitSingleComplex S)) a
          (sheafTensor.{u, u, u, u, u} S.sheaf) (ComplexShape.up ℤ)))) ≫
      (DerivedCategory.homologyFunctor _ (0 + j)).map ((baseSections S).map
        (DerivedCategory.Q.map (unitLeftAction S M₁))) := by
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + j)
    exact (H.map_comp _ _).symm.trans ((congrArg H.map ((baseSections S).map_comp _ _).symm).trans
      ((congrArg (fun g => H.map ((baseSections S).map g))
        ((DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map e1.symm).trans
          (DerivedCategory.Q.map_comp _ _)))).trans
        ((congrArg H.map ((baseSections S).map_comp _ _)).trans (H.map_comp _ _))))
  exact unitClass_paste _ _ _ _ _ _ _ _ _ _ _ _ _ e4 e2 e3
    (homology_map_eqToHom a (zero_add j).symm)

end UnitClass

end Stacks.Cohomology.DerivedGlobalCupProduct
