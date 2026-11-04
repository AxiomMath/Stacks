module

public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalRightMul
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyShiftedSingleCochains

/-!
# The Čech cup product of hypercohomology, elementwise

The cup product `Stacks.Cech.Hypercohomology.cup` of the classes of two Čech cocycles `α`, `β` of
the total Čech complexes of bounded below complexes of `𝒪_X`-modules is the class of their Čech
cup product, and on elements that Čech cup product is the generic one
(`Stacks.Cech.LinearCupProduct.cechCupProduct`) of the tensor `α ⊗ β`.

## Main results

* `Stacks.Cech.Hypercohomology.unitTensor_cupPair_cechCup`: the Čech cup product of two
  cochains is the generic Čech cup product of their tensor.
* `Stacks.Cech.Hypercohomology.cup_cechClass_cocycleClass`: the cup product in hypercohomology of
  the classes of two Čech cocycles is the class of their Čech cup product.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing coverObject)
open scoped TensorProduct

universe u

namespace Stacks.Cech.Hypercohomology


open Stacks.Cech.LinearCupProduct (cechCupProduct)

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

/-- A morphism `f : R ⟶ M` from the unit module is the morphism sending `1` to `f 1`. -/
theorem toMor_apply_one_eq {R : Type u} [Ring R] {M : ModuleCat.{u} R} (f : unitModule R ⟶ M) :
    toMor (f.hom 1) = f := by
  ext : 1
  exact LinearMap.ext_ring (by simp [toMor])

/-- The class of a cocycle `x : P ⟶ Kⁿ` evaluated at `e : P` is the class of the cocycle
`R ⟶ Kⁿ` sending `1` to `x e`, evaluated at `1`. -/
theorem cocycleClass_apply_eq {R : Type u} [Ring R] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    {P : ModuleCat.{u} R} (n : ℤ) (x : P ⟶ K.X n) (hx : x ≫ K.d n (n + 1) = 0) (e : P) :
    (cocycleClass n x hx).hom e =
      (cocycleClass n (toMor (x.hom e))
        (by rw [← toMor_comp, Category.assoc, hx, comp_zero])).hom 1 := by
  generalize_proofs _ _ hy
  have h : toMor e ≫ cocycleClass n x hx = cocycleClass n (toMor (x.hom e)) hy := by
    simp only [cocycleClass, ← Category.assoc,
      HomologicalComplex.comp_liftCycles, toMor_comp]
  rw [← h]
  simp [toMor]

variable {T : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  {ι : Type u} (U : ι → Opens T) (hU : ⊤ = ⨆ i, U i)

/-- **The Čech cup product of two cochains, elementwise**: the cup product of the library's
hypercohomology, on a pair of cochains, is the generic Čech cup product of their tensor. -/
theorem unitTensor_cupPair_cechCup {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) (m b N : ℤ) (h : m + b = N)
    (α : unitModule _ ⟶ ((cech O U hU).obj F.obj).X m)
    (β : unitModule _ ⟶ ((cech O U hU).obj G.obj).X b) :
    (unitTensor O ≫
        Stacks.CupProduct.cupPair (Stacks.Cech.CupProduct.tensorModules _) _ _ m b N h α β ≫
          (cechCup O U hU γ).f N).hom 1 =
      (ιTot (coverObject U hU) ((Stacks.Cech.Refinement.sectionsComplex O).obj F.obj)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj G.obj) m b N h ≫
        (cechCupProduct (coverObject U hU) _ γ).f N).hom (tmulHom (α.hom 1) (β.hom 1)) := by
  simp only [Stacks.CupProduct.cupPair, cechCup, HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  have e3 : eqToHom (cech_obj_eq O U hU H).symm = 𝟙 _ := rfl
  have hu : (unitTensor O).hom 1 =
      (1 : SectionRing (ringSheaf O) ⊤) ⊗ₜ (1 : SectionRing (ringSheaf O) ⊤) := by
    simp [unitTensor, toMor]
  simp only [eqToHom_cech_obj_eq, e3, HomologicalComplex.id_f,
    ModuleCat.hom_comp, LinearMap.comp_apply, hu]
  rfl

/-- `unitTensor_cupPair_cechCup` for the cochains attached to two elements. -/
theorem unitTensor_cupPair_toMor_cechCup
    {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) (m b N : ℤ) (h : m + b = N)
    (a : ((cech O U hU).obj F.obj).X m) (w : ((cech O U hU).obj G.obj).X b) :
    (unitTensor O ≫ CupProduct.cupPair (CupProduct.tensorModules _) _ _ m b N h (toMor a)
          (toMor w) ≫ (cechCup O U hU γ).f N).hom 1 =
      (ιTot (coverObject U hU) ((Refinement.sectionsComplex O).obj F.obj)
          ((Refinement.sectionsComplex O).obj G.obj) m b N h ≫
        (cechCupProduct (coverObject U hU) _ γ).f N).hom
          (tmulHom (show ((LinearCupProduct.totalCechComplexFunctor (coverObject U hU) _).obj
              ((Refinement.sectionsComplex O).obj F.obj)).X m from a)
            (show ((LinearCupProduct.totalCechComplexFunctor (coverObject U hU) _).obj
              ((Refinement.sectionsComplex O).obj G.obj)).X b from w)) := by
  refine (unitTensor_cupPair_cechCup O U hU γ m b N h (toMor a) (toMor w)).trans ?_
  congr 2
  all_goals simp only [toMor, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
  all_goals rfl

/-- **The cup product in hypercohomology of the classes of two Čech cocycles** is the class of
their Čech cup product. -/
theorem cup_cechClass_cocycleClass
    {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G)
    (γ : Pairing O F G H) (m b N : ℤ) (h : m + b = N)
    (α : unitModule _ ⟶ ((cech O U hU).obj F.obj).X m)
    (hα : α ≫ ((cech O U hU).obj F.obj).d m (m + 1) = 0)
    (β : unitModule _ ⟶ ((cech O U hU).obj G.obj).X b)
    (hβ : β ≫ ((cech O U hU).obj G.obj).d b (b + 1) = 0) :
    cup O hF hG γ m b N h
        (cechClass O U hU F m (cocycleClass m α hα (1 : SectionRing (ringSheaf O) ⊤)))
        (cechClass O U hU G b (cocycleClass b β hβ (1 : SectionRing (ringSheaf O) ⊤))) =
      cechClass O U hU H N (cocycleClass N (unitTensor O ≫
          CupProduct.cupPair (CupProduct.tensorModules _) _ _ m b N h α β ≫ (cechCup O U hU γ).f N)
        (by rw [Category.assoc,
            CupProduct.cupPair_comp_gamma_comp_d_eq_zero _ _ _ _ m b N h α β hα hβ, comp_zero])
        (1 : SectionRing (ringSheaf O) ⊤)) := by
  rw [cup_eq, toMor_apply_one_eq, toMor_apply_one_eq, cechCupClass_eq, comp_cocycleClass]
  rfl

end Stacks.Cech.Hypercohomology

end
