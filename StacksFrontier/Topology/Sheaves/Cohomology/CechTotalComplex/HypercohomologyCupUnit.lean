module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AugmentationModelBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologySinglePairing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.LinearCupProductUnit

/-!
# The unit of the cup product on cohomology

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings. The scalar action
`ℱ × 𝒪_X ⟶ ℱ` of `𝒪_X` on a sheaf of modules is a pairing, and the unit section `1` of `𝒪_X`
has a class `1 ∈ H⁰(X, 𝒪_X)`. For the cup product of Cohomology, Section 01FP,

`a ∪ 1 = a`  for every `a ∈ Hⁿ(X, ℱ)`.

## Main definitions

* `Stacks.Cech.Hypercohomology.scalarBilinear`, `Stacks.Cech.Hypercohomology.scalarPairing`: the
  scalar action of `𝒪_X` on a sheaf of modules, as a bilinear map and as a pairing.
* `Stacks.Cech.Hypercohomology.sectionClass`: the class in `H⁰(X, ℱ)` of a global section.

## Main results

* `Stacks.Cech.Hypercohomology.sectionClass_eq_cechClass`: the class of a global section is
  represented, on every open covering, by the Čech cocycle of its restrictions.
* `Stacks.Cech.Hypercohomology.cup_scalarPairing_sectionClass_one`: `a ∪ 1 = a`.

## References

* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor coverObject)
open Stacks.Cech.LinearCupProduct (ComplexPairing tensorPresheafModules)
open Stacks.Cech.CupProduct (tensorModules tensorModulesMap)
open scoped TensorProduct

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- The structure sheaf `𝒪_X`, as a sheaf of modules over itself. -/
abbrev unitSheaf : SheafOfModules.{u} (ringSheaf O) := SheafOfModules.unit (ringSheaf O)

/-- **The scalar action `ℱ × 𝒪_X ⟶ ℱ`, `(x, r) ↦ r • x`**, as a bilinear map on sections. -/
def scalarBilinear (F : SheafOfModules.{u} (ringSheaf O)) :
    Stacks.BilinearMap F.val (unitSheaf O).val F.val where
  app V :=
    { toFun := fun x =>
        { toFun := fun r => (show (ringSheaf O).obj.obj V from r) • x
          map_zero' := zero_smul _ x
          map_add' := fun r r' => add_smul (show (ringSheaf O).obj.obj V from r) r' x }
      map_zero' := AddMonoidHom.ext fun r => smul_zero (show (ringSheaf O).obj.obj V from r)
      map_add' := fun x x' => AddMonoidHom.ext fun r =>
        smul_add (show (ringSheaf O).obj.obj V from r) x x' }
  map_smul_left V s x r := smul_comm (show SectionRing (ringSheaf O) (unop V) from r) s x
  map_smul_right _ s x r := mul_smul s r x
  naturality f x r := PresheafOfModules.map_smul _ f r x

/-- **The scalar action of `𝒪_X` on a sheaf of modules**, as a pairing of the sheaves placed in
degree zero. -/
def scalarPairing (F : SheafOfModules.{u} (ringSheaf O)) :
    Pairing O (singlePlus O F 0) (singlePlus O (unitSheaf O) 0) (singlePlus O F 0) :=
  singlePairing (bilinearPairing (scalarBilinear O F))

/-- The sections over the opens of `X` of a sheaf placed in degree zero. -/
abbrev sectionsK (F : SheafOfModules.{u} (ringSheaf O)) :=
  (Stacks.Cech.Refinement.sectionsComplex O).obj (singlePlus O F 0).obj

/-- The open `X`, as the terminal object of the slice over `X`. -/
abbrev topOver : Over (⊤ : Opens X) := Over.mk (𝟙 ⊤)

/-- The open `X` is terminal in the slice over `X`. -/
abbrev isTerminalTopOver : IsTerminal (topOver (X := X)) := Over.mkIdTerminal

/-- The global unit section of `𝒪_X`, as a section of the sheaf placed in degree zero. -/
def unitSection : ModuleCat.of (SectionRing (ringSheaf O) ⊤) (SectionRing (ringSheaf O) ⊤) ⟶
    ((sectionsK O (unitSheaf O)).X 0).obj (op (topOver (X := X))) :=
  toMor (show (sectionsP O (unitSheaf O)).obj (op (topOver (X := X))) from
      (1 : (ringSheaf O).obj.obj (op ⊤))) ≫
    (singleXIso O (unitSheaf O) 0 rfl).inv.app (op topOver)

/-- The unit section restricted to an open, paired with a section by the scalar action. -/
theorem bilinearPairing_scalar_unit (F : SheafOfModules.{u} (ringSheaf O))
    (V : Over (⊤ : Opens X)) :
    tensorModulesMap (SectionRing (ringSheaf O) ⊤) (𝟙 ((sectionsP O F).obj (op V)))
        (toMor (show (sectionsP O (unitSheaf O)).obj (op (topOver (X := X))) from
            (1 : (ringSheaf O).obj.obj (op ⊤))) ≫
          (sectionsP O (unitSheaf O)).map ((isTerminalTopOver (X := X)).from V).op) ≫
      (bilinearPairing (scalarBilinear O F)).app (op V) =
      Stacks.Cech.LinearCupProduct.rightUnitMap ((sectionsP O F).obj (op V)) := by
  rw [toMor_comp]
  have h1 : ((sectionsP O (unitSheaf O)).map ((isTerminalTopOver (X := X)).from V).op)
      (show (sectionsP O (unitSheaf O)).obj (op (topOver (X := X))) from
        (1 : (ringSheaf O).obj.obj (op ⊤))) =
      (show (sectionsP O (unitSheaf O)).obj (op V) from (1 : (ringSheaf O).obj.obj (op V.left))) :=
    ((ringSheaf O).obj.map ((isTerminalTopOver (X := X)).from V).left.op).hom.map_one
  rw [h1]
  refine ModuleCat.hom_ext (TensorProduct.ext' fun x r => ?_)
  change (show (ringSheaf O).obj.obj (op V.left) from
      (LinearMap.toSpanSingleton _ _ (show (sectionsP O (unitSheaf O)).obj (op V) from
        (1 : (ringSheaf O).obj.obj (op V.left)))) r) •
      (show F.val.obj (op V.left) from x) = r • x
  rw [LinearMap.toSpanSingleton_apply, sectionsP_smul, sectionsP_smul]
  change ((ringSheaf O).obj.map _ r * 1) • (show F.val.obj (op V.left) from x) = _
  rw [mul_one]

/-- **The global unit section acts as the identity under the scalar pairing.** -/
theorem scalarPairing_unitSection (F : SheafOfModules.{u} (ringSheaf O)) (V : Over (⊤ : Opens X)) :
    tensorModulesMap (SectionRing (ringSheaf O) ⊤) (𝟙 (((sectionsK O F).X 0).obj (op V)))
        (unitSection O ≫ ((sectionsK O (unitSheaf O)).X 0).map
          ((isTerminalTopOver (X := X)).from V).op) ≫
      ((scalarPairing O F).μ 0 0 0 rfl).app (op V) =
      Stacks.Cech.LinearCupProduct.rightUnitMap (((sectionsK O F).X 0).obj (op V)) := by
  rw [scalarPairing, singlePairing_μ_zero]
  refine ModuleCat.hom_ext (TensorProduct.ext' fun x r => ?_)
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (bilinearPairing_scalar_unit O F V))
    (x ⊗ₜ r)

variable {O}

/-- A global section of a sheaf of modules, as a section of the sheaf placed in degree zero over
the terminal object of the slice over `X`. -/
def globalSection (F : SheafOfModules.{u} (ringSheaf O)) (s : F.val.obj (op ⊤)) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      ((sectionsK O F).X 0).obj (op (topOver (X := X))) :=
  toMor (show (sectionsP O F).obj (op (topOver (X := X))) from s) ≫
    (singleXIso O F 0 rfl).inv.app (op topOver)

/-- The global unit section is the global section `1`. -/
theorem unitSection_eq : unitSection O = globalSection (unitSheaf O)
    (1 : (ringSheaf O).obj.obj (op ⊤)) :=
  rfl

/-- **The augmentation of a global section** into the total Čech complex of the sections presheaf
of the sheaf placed in degree zero: its restrictions to the members of a covering, in Čech
degree zero ([Stacks, Tag 07M9]). -/
def sectionCochainGen {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (F : SheafOfModules.{u} (ringSheaf O)) (s : F.val.obj (op ⊤)) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤)).obj (sectionsK O F)).X (((0 : ℕ) : ℤ) + 0) :=
  globalSection F s ≫ Stacks.Cech.LinearCupProduct.cechAugmentationCochains (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (isTerminalTopOver (X := X)) ((sectionsK O F).X 0) ≫
    Stacks.Cech.LinearCupProduct.ιTotalCech (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      (sectionsK O F) 0 0

/-- The augmentation cocycle of a global section commutes with refinement. -/
theorem sectionCochainGen_refinement {I J : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (c : J → I) (hc : ∀ j, V j ≤ U (c j))
    (F : SheafOfModules.{u} (ringSheaf O)) (s : F.val.obj (op ⊤)) :
    sectionCochainGen U hU F s ≫
      ((Stacks.Cech.LinearCupProduct.totalCechRefinement (coverObject U hU) (coverObject V hV)
        (SectionRing (ringSheaf O) ⊤) c
            (Stacks.Cech.Refinement.coverRefinementHom U hU V hV c hc)).app
          (sectionsK O F)).f (((0 : ℕ) : ℤ) + 0) = sectionCochainGen V hV F s := by
  have hT := Stacks.Cech.LinearCupProduct.ιTotalCech_totalCechRefinement (coverObject U hU)
    (coverObject V hV) (SectionRing (ringSheaf O) ⊤) c
    (Stacks.Cech.Refinement.coverRefinementHom U hU V hV c hc) (sectionsK O F) 0 0
  have hA := Stacks.Cech.LinearCupProduct.cechAugmentationCochains_comp_cechRefinement
    (coverObject U hU) (SectionRing (ringSheaf O) ⊤) (isTerminalTopOver (X := X))
    (coverObject V hV) c (Stacks.Cech.Refinement.coverRefinementHom U hU V hV c hc)
    ((sectionsK O F).X 0)
  unfold sectionCochainGen
  rw [Category.assoc, Category.assoc, hT, reassoc_of% hA]

/-- The augmentation cochain of a global section is a cocycle. -/
theorem sectionCochainGen_d {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (F : SheafOfModules.{u} (ringSheaf O)) (s : F.val.obj (op ⊤)) :
    sectionCochainGen U hU F s ≫ ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor
      (coverObject U hU) (SectionRing (ringSheaf O) ⊤)).obj (sectionsK O F)).d
        (((0 : ℕ) : ℤ) + 0) ((((0 : ℕ) : ℤ) + 0) + 1) = 0 := by
  have h := (Stacks.Cech.LinearCupProduct.cechAugmentationTotal (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤) (isTerminalTopOver (X := X)) (sectionsK O F)).comm 0 (0 + 1)
  have h0 : ((Stacks.Cech.LinearCupProduct.sectionsAtFunctor (SectionRing (ringSheaf O) ⊤)
      (op (topOver (X := X)))).obj (sectionsK O F)).d 0 (0 + 1) = 0 := by
    change ((sectionsK O F).d 0 (0 + 1)).app _ = 0
    rw [sectionsComplex_singlePlus_d]
    rfl
  have h1 : (Stacks.Cech.LinearCupProduct.cechAugmentationTotal (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (isTerminalTopOver (X := X)) (sectionsK O F)).f 0 ≫
      ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤)).obj (sectionsK O F)).d 0 (0 + 1) = 0 :=
    h.trans (by rw [h0, Limits.zero_comp])
  unfold sectionCochainGen
  rw [Category.assoc, Category.assoc]
  exact (congrArg (fun f => globalSection F s ≫ f) h1).trans Limits.comp_zero

/-- **The Čech cocycle of the restrictions of a global section** to the members of a covering,
in the total Čech complex of the sheaf placed in degree zero. -/
def sectionCochain {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (F : SheafOfModules.{u} (ringSheaf O)) (s : F.val.obj (op ⊤)) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶ ((cech O U hU).obj (singlePlus O F 0).obj).X 0 :=
  sectionCochainGen U hU F s

/-- The cochain of the restrictions of a global section is a cocycle. -/
theorem sectionCochain_d {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (F : SheafOfModules.{u} (ringSheaf O)) (s : F.val.obj (op ⊤)) :
    sectionCochain U hU F s ≫ ((cech O U hU).obj (singlePlus O F 0).obj).d 0 (0 + 1) = 0 :=
  sectionCochainGen_d U hU F s

/-- **The augmentation cocycle commutes with refinement.** -/
theorem sectionCochain_refinement {I J : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (c : J → I) (hc : ∀ j, V j ≤ U (c j))
    (F : SheafOfModules.{u} (ringSheaf O)) (s : F.val.obj (op ⊤)) :
    sectionCochain U hU F s ≫
        ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app (singlePlus O F 0).obj).f 0 =
      sectionCochain V hV F s :=
  sectionCochainGen_refinement U hU V hV c hc F s

/-- The trivial covering of `X` by itself. -/
theorem top_eq_iSup_top : (⊤ : Opens X) = ⨆ _ : PUnit.{u + 1}, (⊤ : Opens X) := by
  rw [iSup_const]

/-- **The class in `H⁰(X, ℱ)` of a global section `s`**: the class of `s` on the trivial
covering. By `sectionClass_eq_cechClass` it is the class of the Čech cocycle of its
restrictions on every open covering. -/
def sectionClass (F : SheafOfModules.{u} (ringSheaf O)) (s : F.val.obj (op ⊤)) :
    hypercohomology O (singlePlus O F 0) 0 :=
  cechClass O (fun _ : PUnit.{u + 1} => ⊤) top_eq_iSup_top (singlePlus O F 0) 0
    (cocycleClass 0 (sectionCochain _ top_eq_iSup_top F s) (sectionCochain_d _ _ F s)
      (1 : SectionRing (ringSheaf O) ⊤))

/-- **The class of a global section is represented on every covering** by the Čech cocycle of
its restrictions. -/
theorem sectionClass_eq_cechClass {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (F : SheafOfModules.{u} (ringSheaf O)) (s : F.val.obj (op ⊤)) :
    sectionClass F s = cechClass O U hU (singlePlus O F 0) 0
      (cocycleClass 0 (sectionCochain U hU F s) (sectionCochain_d U hU F s)
        (1 : SectionRing (ringSheaf O) ⊤)) := by
  have href := cechClass_refinement O (fun _ : PUnit.{u + 1} => ⊤) top_eq_iSup_top U hU
    (fun _ => PUnit.unit) (fun _ => le_top) (singlePlus O F 0) 0
  rw [sectionClass, ← href, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply
    (cocycleClass 0 _ _), cocycleClass_comp_homologyMap]
  congr 2
  exact congrArg ConcreteCategory.hom (cocycleClass_congr 0
    (sectionCochain_refinement _ top_eq_iSup_top U hU _ (fun _ => le_top) F s) _ _)

/-- The identification of the two spellings of the total Čech complex is the identity. -/
theorem eqToHom_cech_obj_eq {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) :
    eqToHom (cech_obj_eq O U hU K) = 𝟙 _ :=
  rfl

/-- The unit `1 ⊗ 1` is the inclusion `r ↦ r ⊗ 1`. -/
theorem unitTensor_eq :
    unitTensor O = Stacks.Cech.LinearCupProduct.rightUnitInv (unitModule _) := by
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  change (1 : SectionRing (ringSheaf O) ⊤) • ((1 : SectionRing (ringSheaf O) ⊤) ⊗ₜ[SectionRing
    (ringSheaf O) ⊤] (1 : SectionRing (ringSheaf O) ⊤)) = (TensorProduct.rid _ _).symm 1
  rw [one_smul, TensorProduct.rid_symm_apply]

variable (O) in
/-- The global unit section of `𝒪_X`. -/
abbrev oneSection : (unitSheaf O).val.obj (op ⊤) := (1 : (ringSheaf O).obj.obj (op ⊤))

/-- **The cup product of a cochain with the restrictions of the unit section is the cochain**,
for the scalar pairing. -/
theorem cupPair_scalarPairing_sectionCochain_one {I : Type u} (U : I → Opens X)
    (hU : ⊤ = ⨆ i, U i) (F : SheafOfModules.{u} (ringSheaf O)) (n : ℤ)
    (z : unitModule (SectionRing (ringSheaf O) ⊤) ⟶ ((cech O U hU).obj (singlePlus O F 0).obj).X n)
        :
    unitTensor O ≫ Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
        ((cech O U hU).obj (singlePlus O F 0).obj)
        ((cech O U hU).obj (singlePlus O (unitSheaf O) 0).obj) n 0 n (add_zero n) z
        (sectionCochain U hU (unitSheaf O) (oneSection O)) ≫
      (cechCup O U hU (scalarPairing O F)).f n = z := by
  have hT := Stacks.Cech.LinearCupProduct.cechCupProduct_augmentation_right (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤) (isTerminalTopOver (X := X)) (scalarPairing O F)
    (fun a ha => (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map_isZero
      (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 F a ha))
    (unitSection O) (scalarPairing_unitSection O F) n
  have hw : sectionCochain U hU (unitSheaf O) (oneSection O) ≫
      (eqToHom (cech_obj_eq O U hU (singlePlus O (unitSheaf O) 0))).f 0 =
      sectionCochainGen U hU (unitSheaf O) (oneSection O) := by
    rw [HomologicalComplex.eqToHom_f]
    exact Category.comp_id _
  rw [unitTensor_eq, Stacks.CupProduct.cupPair, cechCup, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f]
  simp only [Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [Stacks.Cech.LinearCupProduct.tensorModules_map_app,
    Stacks.Cech.LinearCupProduct.tensorModules_obj_map]
  rw [Stacks.Cech.LinearCupProduct.tensorModulesMap_comp_assoc,
    Stacks.Cech.LinearCupProduct.tensorModulesMap_comp_assoc,
    Stacks.Cech.LinearCupProduct.tensorModulesMap_comp_assoc]
  simp only [Category.comp_id, Category.id_comp]
  rw [hw, show tensorModulesMap (SectionRing (ringSheaf O) ⊤)
      (z ≫ (eqToHom (cech_obj_eq O U hU (singlePlus O F 0))).f n)
      (sectionCochainGen U hU (unitSheaf O) (oneSection O)) =
      tensorModulesMap (SectionRing (ringSheaf O) ⊤)
        (z ≫ (eqToHom (cech_obj_eq O U hU (singlePlus O F 0))).f n) (𝟙 _) ≫
      tensorModulesMap (SectionRing (ringSheaf O) ⊤) (𝟙 _)
        (sectionCochainGen U hU (unitSheaf O) (oneSection O)) by
    rw [Stacks.Cech.CupProduct.tensorModulesMap_comp, Category.comp_id, Category.id_comp]]
  rw [Category.assoc, Stacks.Cech.LinearCupProduct.rightUnitInv_tensorModulesMap_assoc]
  have hT' := congrArg (fun f => (z ≫ (eqToHom (cech_obj_eq O U hU (singlePlus O F 0))).f n) ≫ f ≫
    (eqToHom (cech_obj_eq O U hU (singlePlus O F 0)).symm).f n) hT
  refine (Eq.trans ?_ hT').trans ?_
  · simp only [Category.assoc]
    rfl
  · have e1 : (eqToHom (cech_obj_eq O U hU (singlePlus O F 0))).f n = 𝟙 _ := by
      rw [eqToHom_cech_obj_eq]
      rfl
    have e2 : (eqToHom (cech_obj_eq O U hU (singlePlus O F 0)).symm).f n = 𝟙 _ := by
      rw [HomologicalComplex.eqToHom_f]
      rfl
    rw [e1, e2]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => rfl)

/-- A morphism from a projective object to the homology is the class of a cocycle. -/
private theorem exists_cocycleClass_eq_of_projective {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) {P : C} [Projective P] (n : ℤ) (γ : P ⟶ K.homology n) :
    ∃ (z : P ⟶ K.X n) (hz : z ≫ K.d n (n + 1) = 0), cocycleClass n z hz = γ :=
  Stacks.CupProduct.exists_liftCycles_homologyπ_eq K n (n + 1) (CochainComplex.next ℤ n) γ

/-- **The unit section is a right unit for the cup product**: for the scalar pairing
`ℱ × 𝒪_X ⟶ ℱ` and the class `1 ∈ H⁰(X, 𝒪_X)` of the unit section, `a ∪ 1 = a` for every
`a ∈ Hⁿ(X, ℱ)` ([Stacks, Section 01FP]). -/
theorem cup_scalarPairing_sectionClass_one (F : SheafOfModules.{u} (ringSheaf O))
    (hF : CechComputes O (singlePlus O F 0))
    (hO : CechComputes O (singlePlus O (unitSheaf O) 0)) (n : ℤ)
    (y : hypercohomology O (singlePlus O F 0) n) :
    cup O hF hO (scalarPairing O F) n 0 n (add_zero n) y
      (sectionClass (unitSheaf O) (oneSection O)) = y := by
  obtain ⟨I, U, hU, z, rfl⟩ := (hF n).1 y
  rw [sectionClass_eq_cechClass U hU, cup_eq O U hU hF hO]
  obtain ⟨zz, hzz, hz⟩ :=
    exists_cocycleClass_eq_of_projective ((cech O U hU).obj (singlePlus O F 0).obj) n (toMor z)
  rw [← hz, toMor_apply, cechCupClass_eq]
  have hc : unitTensor O ≫ cocycleClass n
      (Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
        ((cech O U hU).obj (singlePlus O F 0).obj)
        ((cech O U hU).obj (singlePlus O (unitSheaf O) 0).obj) n 0 n (add_zero n) zz
        (sectionCochain U hU (unitSheaf O) (oneSection O)) ≫
        (cechCup O U hU (scalarPairing O F)).f n)
      (Stacks.CupProduct.cupPair_comp_gamma_comp_d_eq_zero _ _ _ _ n 0 n (add_zero n) _ _ hzz
        (sectionCochain_d U hU (unitSheaf O) (oneSection O))) = cocycleClass n zz hzz := by
    dsimp only [cocycleClass]
    rw [← Category.assoc, HomologicalComplex.comp_liftCycles]
    congr 2
    exact cupPair_scalarPairing_sectionCochain_one U hU F n zz
  rw [hc, hz, ConcreteCategory.comp_apply, toMor_apply_one]

/-! ### Linearity of the cup product in the second factor -/

section Linearity

variable {R : Type u} [CommRing R]

/-- `toMor` is linear. -/
theorem toMor_smul {M : ModuleCat.{u} R} (r : R) (x : M) : toMor (r • x) = r • toMor x := by
  ext : 1
  exact LinearMap.ext_ring (by simp [toMor])

/-- Lifting a multiple of a cocycle to the cycles is the multiple of the lift. -/
theorem liftCycles_smul {K : CochainComplex (ModuleCat.{u} R) ℤ} {P : ModuleCat.{u} R} (r : R)
    (i j : ℤ) (hj : (ComplexShape.up ℤ).next i = j) (z : P ⟶ K.X i) (hz : z ≫ K.d i j = 0)
    (hrz : (r • z) ≫ K.d i j = 0) :
    K.liftCycles (r • z) j hj hrz = r • K.liftCycles z j hj hz := by
  rw [← cancel_mono (K.iCycles i), HomologicalComplex.liftCycles_i, Linear.smul_comp,
    HomologicalComplex.liftCycles_i]

/-- The class of a multiple of a cocycle is the multiple of its class. -/
theorem cocycleClass_smul {K : CochainComplex (ModuleCat.{u} R) ℤ} {P : ModuleCat.{u} R} (r : R)
    (n : ℤ) (z : P ⟶ K.X n) (hz : z ≫ K.d n (n + 1) = 0) (hrz : (r • z) ≫ K.d n (n + 1) = 0) :
    cocycleClass n (r • z) hrz = r • cocycleClass n z hz := by
  dsimp only [cocycleClass]
  rw [liftCycles_smul r n (n + 1) _ z hz hrz, Linear.smul_comp]

/-- The cup product of cochains is linear in its second factor. -/
theorem cupPair_smul_right (K L : CochainComplex (ModuleCat.{u} R) ℤ) {P Q : ModuleCat.{u} R}
    (p q t : ℤ) (ht : p + q = t) (α : P ⟶ K.X p) (β : Q ⟶ L.X q) (r : R) :
    Stacks.CupProduct.cupPair (tensorModules R) K L p q t ht α (r • β) =
      r • Stacks.CupProduct.cupPair (tensorModules R) K L p q t ht α β := by
  have h : ((tensorModules R).obj (K.X p)).map (r • β) =
      r • ((tensorModules R).obj (K.X p)).map β :=
    ModuleCat.hom_ext (TensorProduct.map_smul_right _ _ _)
  dsimp only [Stacks.CupProduct.cupPair]
  rw [h, Linear.smul_comp, Linear.comp_smul]

variable (O)

/-- **The cup product of Čech classes is linear in the second factor** over the global sections
of `𝒪_X`. -/
theorem cechCupClass_smul_right {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) (p q t : ℤ) (ht : p + q = t)
    (x : unitModule _ ⟶ ((cech O U hU).obj F.obj).homology p)
    (y : ((cech O U hU).obj G.obj).homology q) (r : SectionRing (ringSheaf O) ⊤) :
    cechCupClass O U hU γ p q t ht x (toMor (r • y)) =
      r • cechCupClass O U hU γ p q t ht x (toMor y) := by
  obtain ⟨zx, hzx, rfl⟩ := exists_cocycleClass_eq_of_projective ((cech O U hU).obj F.obj) p x
  obtain ⟨zy, hzy, hy⟩ :=
    exists_cocycleClass_eq_of_projective ((cech O U hU).obj G.obj) q (toMor y)
  have hrzy : (r • zy) ≫ ((cech O U hU).obj G.obj).d q (q + 1) = 0 := by
    rw [Linear.smul_comp, hzy, smul_zero]
  have hry : toMor (r • y) = cocycleClass q (r • zy) hrzy := by
    rw [toMor_smul, ← hy, cocycleClass_smul r q zy hzy hrzy]
  rw [← hy, hry, cechCupClass_eq, cechCupClass_eq, ← Linear.comp_smul]
  congr 1
  have hX := Stacks.CupProduct.cupPair_comp_gamma_comp_d_eq_zero
    (tensorModules (SectionRing (ringSheaf O) ⊤)) ((cech O U hU).obj F.obj)
    ((cech O U hU).obj G.obj) (cechCup O U hU γ) p q t ht zx zy hzx hzy
  have hrX : (r • (Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
      ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht zx zy ≫
        (cechCup O U hU γ).f t)) ≫ ((cech O U hU).obj H.obj).d t (t + 1) = 0 := by
    rw [Linear.smul_comp, hX, smul_zero]
  have e : Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
      ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht zx (r • zy) ≫
        (cechCup O U hU γ).f t =
      r • (Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
      ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht zx zy ≫
        (cechCup O U hU γ).f t) := by
    rw [cupPair_smul_right, Linear.smul_comp]
  exact (cocycleClass_congr t e _ hrX).trans (cocycleClass_smul r t _ hX hrX)

/-- **The cup product is linear in the second factor** over the global sections of `𝒪_X`. -/
theorem cup_smul_right {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) (a : hypercohomology O F p) (b : hypercohomology O G q)
    (r : SectionRing (ringSheaf O) ⊤) :
    cup O hF hG γ p q t ht a (r • b) = r • cup O hF hG γ p q t ht a b := by
  obtain ⟨I, U, hU, x, rfl⟩ := (hF p).1 a
  obtain ⟨J, V, hV, y, rfl⟩ := (hG q).1 b
  have hW := iSup_inf_eq_top U hU V hV
  have ha := cechClass_refinement O U hU _ hW Prod.fst (fun _ => inf_le_left) F p
  have hb := cechClass_refinement O V hV _ hW Prod.snd (fun _ => inf_le_right) G q
  rw [← ha, ← hb, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← map_smul,
    cup_eq O _ hW hF hG, cup_eq O _ hW hF hG, cechCupClass_smul_right, Linear.smul_comp]
  rfl

end Linearity

end Stacks.Cech.Hypercohomology
