module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquareClasses
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupSheafTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalDuality
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The global cup product and the Čech cup product on hypercohomology

Let `(S, 𝒪_S)` be a ringed space and `K`, `M` bounded below complexes of `𝒪_S`-modules for which
Čech cohomology computes hypercohomology. Hypercohomology in the model of Cohomology,
Section 01FP (`Stacks.Cech.Hypercohomology.hypercohomology`) is identified with the cohomology of
derived global sections in the model of Section 0FKU (`θ`, the identification of the two models
of `RΓ(S, -)`). Under this identification the cup product of Section 0FKU followed by the
canonical map `𝒦^• ⊗^𝐋 ℳ^• ⟶ Tot(𝒦^• ⊗ ℳ^•)` is the Čech cup product of Section 01FP at the
sheaf-tensor coefficient pairing. This is [Stacks, Tag 0FKV]
(`Stacks.Cech.CupProductSquare.cupProductSquareCommutes`) read on cohomology classes.

## Main definitions

* `Stacks.Cech.CupProductSquare.hypercohomologyToCohomologyModule`: `θ`.

## Main results

* `Stacks.Cech.CupProductSquare.cupPairing_hypercohomologyToCohomologyModule_cycles`: the two
  cup products agree on classes of cycles of a common covering.

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.DerivedGlobalCupProduct (cupProductOnSpace cupPairing cohomologyModule)
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections tensorBase)
open Stacks.Cohomology.DerivedSectionsModels (derivedSectionsFunctorIsoBaseSections)
open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans)
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cech.ModuleCupProduct (CoeffRing totalCechComplexFunctorA)
open Stacks.Cohomology.CechSheaf (coverObject)
open RingTheory.TorProducts (cycleClass)
open Stacks.Cech.Hypercohomology

universe u

namespace Stacks.Cech.CupProductSquare

open scoped Stacks.StandardDerivedModel
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable (S : RingedSpace.{u, u}) {I : Type u} (Ui : I → Opens S.carrier)
  (hU : (⊤ : Opens S.carrier) = ⨆ i, Ui i)
  (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))

/-- **The identification of the two models of hypercohomology**: the class of `Hⁿ(S, K)` in the
Čech-comparison model of Section 01FP, read in the model of derived global sections of Section
0FKU (`Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections`). -/
def hypercohomologyToCohomologyModule (n : ℤ) (a : hypercohomology S.sheaf K n) :
    cohomologyModule (DerivedCategory.Q.obj K.1) n :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
    ((derivedSectionsFunctorIsoBaseSections S).hom.app K)).hom a

/-- `θ` sends the Čech class of a cycle `z` of `Tot(Č(𝒰, K))` to the image under
`cechToBaseSections` of the cycle class of `z`. -/
theorem hypercohomologyToCohomologyModule_cechClass (n : ℤ)
    (z : (totalCechBase S Ui hU K).cycles n) :
    hypercohomologyToCohomologyModule S K n
        (cechClass S.sheaf Ui hU K n ((totalCechBase S Ui hU K).homologyπ n z)) =
      (cycleClass (Stacks.Cech.Hypercohomology.toMor z) ≫
        (DerivedCategory.homologyFunctor _ n).map ((cechToBaseSections S Ui hU).app K)).hom 1 := by
  have e : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
      ((cechToBaseSections S Ui hU).app K) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
        ((Stacks.Cech.Linear.totalCechToDerivedSections S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤
          Ui hU).app K) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
        ((derivedSectionsFunctorIsoBaseSections S).hom.app K) :=
    Functor.map_comp _ _ _
  refine Eq.trans ?_ (congrArg (fun φ => (cycleClass (toMor z) ≫ φ).hom (1 : baseRing S)) e).symm
  calc _ = ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
        ((derivedSectionsFunctorIsoBaseSections S).hom.app K)).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
          ((Stacks.Cech.Linear.totalCechToDerivedSections S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤
            Ui hU).app K)).hom
          (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing S)) n).inv.app
            (totalCechBase S Ui hU K)).hom (((totalCechBase S Ui hU K).homologyπ n).hom z))) := rfl
    _ = ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
        ((derivedSectionsFunctorIsoBaseSections S).hom.app K)).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
          ((Stacks.Cech.Linear.totalCechToDerivedSections S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤
            Ui hU).app K)).hom
          (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing S)) n).inv.app
            (totalCechBase S Ui hU K)).hom (((totalCechBase S Ui hU K).homologyπ n).hom
              ((toMor z).hom (1 : baseRing S))))) := by rw [toMor_apply_one z]
    _ = _ := rfl

/-- `θ` sends the Čech class of a cohomology class `x` of `Tot(Č(𝒰, K))` to the image of `x`
under the map on cohomology induced by `cechToBaseSections`. -/
theorem hypercohomologyToCohomologyModule_cechClass' (n : ℤ)
    (x : (totalCechBase S Ui hU K).homology n) :
    hypercohomologyToCohomologyModule S K n (cechClass S.sheaf Ui hU K n x) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
        ((cechToBaseSections S Ui hU).app K)).hom
        (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing S)) n).inv.app
          (totalCechBase S Ui hU K)).hom x) := by
  have e : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
      ((cechToBaseSections S Ui hU).app K) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
        ((Stacks.Cech.Linear.totalCechToDerivedSections S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤
          Ui hU).app K) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
        ((derivedSectionsFunctorIsoBaseSections S).hom.app K) :=
    Functor.map_comp _ _ _
  refine Eq.trans ?_ (congrArg (fun φ => φ.hom (((DerivedCategory.homologyFunctorFactors
    (ModuleCat.{u} (baseRing S)) n).inv.app (totalCechBase S Ui hU K)).hom x)) e).symm
  rfl

/-- For linear maps `f : R ⟶ M`, `g : R ⟶ N` and `φ : M ⊗ N ⟶ P`, the composite
`R ≅ R ⊗ R ⟶ M ⊗ N ⟶ P` sends `1` to `φ (f 1 ⊗ₜ g 1)`. -/
theorem lunit_tensorHom_apply {R : Type u} [CommRing R] {M N P : ModuleCat.{u} R}
    (f : ModuleCat.of R R ⟶ M) (g : ModuleCat.of R R ⟶ N) (φ : M ⊗ N ⟶ P) :
    ((λ_ (ModuleCat.of R R)).inv ≫ (f ⊗ₘ g) ≫ φ).hom (1 : R) = φ.hom (f.hom 1 ⊗ₜ g.hom 1) := by
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

variable (M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))

/-- The cup product of Section 0FKU, followed by the map to the total tensor complex, of the
images of the cycle classes of `zc` and `wc` is the image under the Čech cup product at the
sheaf-tensor coefficients of the class of `zc ⊗ₜ wc`. -/
theorem cupPairing_toMor_cechCycleClass {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    (cupPairing (cupProductOnSpace S) (DerivedCategory.Q.obj K.1) (DerivedCategory.Q.obj M.1) i j ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((baseSections S).map ((derivedToTensorNatTrans S).app (K.1, M.1)))).hom
      ((cycleClass (toMor zc) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
            ((cechToBaseSections S Ui hU).app K)).hom 1 ⊗ₜ
        (cycleClass (toMor wc) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) j).map
            ((cechToBaseSections S Ui hU).app M)).hom 1) =
    (cycleClass z₀ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
      ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
        (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj (tensorPlus S K M).1)
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((cechToBaseSections S Ui hU).app (tensorPlus S K M))).hom
      ((toMor zc).hom (1 : baseRing S) ⊗ₜ (toMor wc).hom (1 : baseRing S)) :=
  (lunit_tensorHom_apply _ _ _).symm.trans ((congrArg (fun φ => φ.hom (1 : baseRing S))
    (cupPairing_cechCycleClass S Ui hU K M (toMor zc) (toMor wc) z₀ hz₀)).trans
      (lunit_tensorHom_apply _ _ _))

/-- The cup product of Section 0FKU, followed by the map to the total tensor complex, of the
`θ`-images of the Čech classes of cycles `zc` and `wc`, written through the cycle classes of
`zc` and `wc`. -/
theorem cupPairing_theta_aux₁ {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j) :
    (cupPairing (cupProductOnSpace S) (DerivedCategory.Q.obj K.1) (DerivedCategory.Q.obj M.1) i j ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((baseSections S).map ((derivedToTensorNatTrans S).app (K.1, M.1)))).hom
      (hypercohomologyToCohomologyModule S K i (cechClass S.sheaf Ui hU K i
          ((totalCechBase S Ui hU K).homologyπ i zc)) ⊗ₜ
        hypercohomologyToCohomologyModule S M j (cechClass S.sheaf Ui hU M j
          ((totalCechBase S Ui hU M).homologyπ j wc))) =
    (cupPairing (cupProductOnSpace S) (DerivedCategory.Q.obj K.1) (DerivedCategory.Q.obj M.1) i j ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((baseSections S).map ((derivedToTensorNatTrans S).app (K.1, M.1)))).hom
      ((cycleClass (toMor zc) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
            ((cechToBaseSections S Ui hU).app K)).hom 1 ⊗ₜ
        (cycleClass (toMor wc) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) j).map
            ((cechToBaseSections S Ui hU).app M)).hom 1) :=
  congrArg₂ (fun x y => (cupPairing (cupProductOnSpace S) (DerivedCategory.Q.obj K.1)
      (DerivedCategory.Q.obj M.1) i j ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((baseSections S).map ((derivedToTensorNatTrans S).app (K.1, M.1)))).hom (x ⊗ₜ y))
    (hypercohomologyToCohomologyModule_cechClass S Ui hU K i zc)
    (hypercohomologyToCohomologyModule_cechClass S Ui hU M j wc)

/-- The image of `toMor zc 1 ⊗ₜ toMor wc 1` under the Čech cup product at the sheaf-tensor
coefficients equals that of `zc ⊗ₜ wc`. -/
theorem cupPairing_theta_aux₂ {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (_hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    (cycleClass z₀ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
      ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
        (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj (tensorPlus S K M).1)
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((cechToBaseSections S Ui hU).app (tensorPlus S K M))).hom
      ((toMor zc).hom (1 : baseRing S) ⊗ₜ (toMor wc).hom (1 : baseRing S)) =
    (cycleClass z₀ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
      ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
        (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj (tensorPlus S K M).1)
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((cechToBaseSections S Ui hU).app (tensorPlus S K M))).hom (zc ⊗ₜ wc) :=
  congrArg₂ (fun x y => (cycleClass z₀ ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
      ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
        (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj (tensorPlus S K M).1)
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((cechToBaseSections S Ui hU).app (tensorPlus S K M))).hom (x ⊗ₜ y))
    (toMor_apply_one zc) (toMor_apply_one wc)

/-- The cup product of Section 0FKU, followed by the map to the total tensor complex, of the
`θ`-images of the Čech classes of cycles `zc` and `wc` is the image of `zc ⊗ₜ wc` under the
Čech cup product at the sheaf-tensor coefficients followed by `cechToBaseSections`. -/
theorem cupPairing_hypercohomologyToCohomologyModule_cechClass {i j : ℤ}
    (zc : (totalCechBase S Ui hU K).cycles i) (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    (cupPairing (cupProductOnSpace S) (DerivedCategory.Q.obj K.1) (DerivedCategory.Q.obj M.1) i j ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((baseSections S).map ((derivedToTensorNatTrans S).app (K.1, M.1)))).hom
      (hypercohomologyToCohomologyModule S K i (cechClass S.sheaf Ui hU K i
          ((totalCechBase S Ui hU K).homologyπ i zc)) ⊗ₜ
        hypercohomologyToCohomologyModule S M j (cechClass S.sheaf Ui hU M j
          ((totalCechBase S Ui hU M).homologyπ j wc))) =
    (cycleClass z₀ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
      ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
        (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj (tensorPlus S K M).1)
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((cechToBaseSections S Ui hU).app (tensorPlus S K M))).hom (zc ⊗ₜ wc) :=
  (cupPairing_theta_aux₁ S Ui hU K M zc wc).trans
    ((cupPairing_toMor_cechCycleClass S Ui hU K M zc wc z₀ hz₀).trans
      (cupPairing_theta_aux₂ S Ui hU K M zc wc z₀ hz₀))

/-- The Čech cup product at the sheaf-tensor coefficients sends the cycle class of `z₀ x` in
the derived category to the class of the cycle `cyclesMap (cechCupProductSheafTensor) (z₀ x)`. -/
theorem cycleClass_Q_cechCup {i j : ℤ}
    (x : ((totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j : ModuleCat _))
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j)) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
      ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
        (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj (tensorPlus S K M).1)
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU))).hom
      ((cycleClass z₀).hom x) =
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing S)) (i + j)).inv.app
      (totalCechBase S Ui hU (tensorPlus S K M))).hom
      ((totalCechBase S Ui hU (tensorPlus S K M)).homologyπ (i + j)
        (HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
          (i + j) (z₀ x))) := by
  have h := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (CoeffRing S.sheaf ⊤))
    (i + j)).inv.naturality
    (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
  have h1 := ConcreteCategory.congr_hom h
    (((totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).homologyπ (i + j)).hom (z₀.hom x))
  have h2 : ((HomologicalComplex.homologyFunctor (ModuleCat.{u} (CoeffRing S.sheaf ⊤)) (up ℤ)
      (i + j)).map (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui
        hU)).hom (((totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).homologyπ (i + j)).hom
          (z₀.hom x)) =
      ((totalCechBase S Ui hU (tensorPlus S K M)).homologyπ (i + j)).hom
        ((HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
          (i + j)).hom (z₀.hom x)) :=
    (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
      (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU) (i + j))
      (z₀.hom x))
  exact h1.symm.trans (congrArg ((DerivedCategory.homologyFunctorFactors
    (ModuleCat.{u} (CoeffRing S.sheaf ⊤)) (i + j)).inv.app _).hom h2)



/-- The cochain of the Čech cup product of two cycles, in the spelling of the total tensor
complex. -/
theorem iCycles_cyclesMap_cechCupProductSheafTensor {i j : ℤ}
    (zc : (totalCechBase S Ui hU K).cycles i) (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    ((totalCechBase S Ui hU (tensorPlus S K M)).iCycles (i + j)).hom
        ((HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
          (i + j)).hom (z₀.hom (zc ⊗ₜ wc))) =
      ((HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl ≫
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU).f
          (i + j)).hom
        ((totalCechBase S Ui hU K).iCycles i zc ⊗ₜ (totalCechBase S Ui hU M).iCycles j wc)) := by
  have h2 := ConcreteCategory.congr_hom hz₀ (zc ⊗ₜ wc)
  have h3 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU) (i + j))
    (z₀.hom (zc ⊗ₜ wc))
  exact h3.trans (congrArg
    ((Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU).f
      (i + j)).hom h2)

/-- The cochain of the Čech cup product of two cycles, in the spelling of the module-valued
total Čech complexes. -/
theorem cechCupProduct_tmulHom_iCycles {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j) :
    (Stacks.CategoryTheory.CechComplex.ιTot (coverObject Ui hU)
          ((Stacks.Cech.Refinement.sectionsComplex S.sheaf).obj K.obj)
          ((Stacks.Cech.Refinement.sectionsComplex S.sheaf).obj M.obj) i j (i + j) rfl ≫
        (Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject Ui hU) _
          (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2)).f (i + j)).hom
        (Stacks.CategoryTheory.CechComplex.tmulHom
          (((cechSections S.sheaf Ui hU).obj K.obj).iCycles i zc)
          (((cechSections S.sheaf Ui hU).obj M.obj).iCycles j wc)) =
      ((HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl ≫
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU).f
          (i + j)).hom
        ((totalCechBase S Ui hU K).iCycles i zc ⊗ₜ (totalCechBase S Ui hU M).iCycles j wc)) :=
  rfl

/-- The class in hypercohomology of a cycle of the module-valued total Čech complex, in the two
spellings of that complex. -/
theorem cechClass_homologyπ_totalCechBase (L : CochainComplex.Plus (SheafOfModules.{u}
    (ringSheaf.{u, u, u} S.sheaf))) (n : ℤ) (z : (totalCechBase S Ui hU L).cycles n) :
    cechClass S.sheaf Ui hU L n ((totalCechBase S Ui hU L).homologyπ n z) =
      cechClass S.sheaf Ui hU L n (((cechSections S.sheaf Ui hU).obj L.obj).homologyπ n z) :=
  rfl

/-- The total cup pairing of the `θ`-images of the Čech classes of cycles `zc` and `wc` is the
image of `zc ⊗ₜ wc` under the Čech cup product at the sheaf-tensor coefficients followed by
`cechToBaseSections`, with the tensor complex written as `tensorPlusOf`. -/
theorem cupPairing_hypercohomologyToCohomologyModule_cechClass_of
    {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    (Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing K.1 M.1 i j).hom
      (hypercohomologyToCohomologyModule S K i (cechClass S.sheaf Ui hU K i
          ((totalCechBase S Ui hU K).homologyπ i zc)) ⊗ₜ
        hypercohomologyToCohomologyModule S M j (cechClass S.sheaf Ui hU M j
          ((totalCechBase S Ui hU M).homologyπ j wc))) =
    (cycleClass z₀ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
      ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
        (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj
          (tensorPlusOf S.sheaf K M (tensorPlus S K M).2).1)
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((cechToBaseSections S Ui hU).app (tensorPlusOf S.sheaf K M (tensorPlus S K M).2))).hom
          (zc ⊗ₜ wc) :=
  cupPairing_hypercohomologyToCohomologyModule_cechClass S Ui hU K M zc wc z₀ hz₀

/-- `cycleClass_Q_cechCup` with the tensor complex written as `tensorPlusOf`. -/
theorem cycleClass_Q_cechCup_of {i j : ℤ}
    (x : ((totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j : ModuleCat _))
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j)) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
      ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
        (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj
          (tensorPlusOf S.sheaf K M (tensorPlus S K M).2).1)
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU))).hom
      ((cycleClass z₀).hom x) =
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing S)) (i + j)).inv.app
      (totalCechBase S Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2))).hom
      ((totalCechBase S Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2)).homologyπ (i + j)
        (HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
          (i + j) (z₀ x))) :=
  cycleClass_Q_cechCup S Ui hU K M x z₀

/-- The cochain of the Čech cup product of two cycles, in the spelling of the total tensor
complex. -/
theorem iCycles_cyclesMap_cechCupProductSheafTensor_of {i j : ℤ}
    (zc : (totalCechBase S Ui hU K).cycles i) (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    ((totalCechBase S Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2)).iCycles (i + j)).hom
        ((HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
          (i + j)).hom (z₀.hom (zc ⊗ₜ wc))) =
      ((HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl ≫
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU).f
          (i + j)).hom
        ((totalCechBase S Ui hU K).iCycles i zc ⊗ₜ (totalCechBase S Ui hU M).iCycles j wc)) :=
  iCycles_cyclesMap_cechCupProductSheafTensor S Ui hU K M zc wc z₀ hz₀

/-- The cochain of a cycle of `Tot(Č(𝒰, Tot(K ⊗ M)))`, in the two spellings of that complex. -/
theorem iCycles_cechSections_totalCechBase (L : CochainComplex.Plus (SheafOfModules.{u}
    (ringSheaf.{u, u, u} S.sheaf))) (n : ℤ) (y : (totalCechBase S Ui hU L).cycles n) :
    ((cechSections S.sheaf Ui hU).obj L.obj).iCycles n y =
      ((totalCechBase S Ui hU L).iCycles n y : ((cechSections S.sheaf Ui hU).obj L.obj).X n) :=
  rfl

/-- The image of `zc ⊗ₜ wc` under the Čech cup product followed by `cechToBaseSections` is the
image under `cechToBaseSections` of the class of the cup product cycle. -/
theorem cupPairing_chain₂ {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j)) :
    (cycleClass z₀ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
      ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
        (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj
          (tensorPlusOf S.sheaf K M (tensorPlus S K M).2).1)
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((cechToBaseSections S Ui hU).app (tensorPlusOf S.sheaf K M (tensorPlus S K M).2))).hom
          (zc ⊗ₜ wc) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
          ((cechToBaseSections S Ui hU).app (tensorPlusOf S.sheaf K M (tensorPlus S K M).2))).hom
        (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing S)) (i + j)).inv.app
          (totalCechBase S Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2))).hom
          ((totalCechBase S Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2)).homologyπ (i + j)
            ((HomologicalComplex.cyclesMap
              (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
              (i + j)).hom (z₀.hom (zc ⊗ₜ wc))))) :=
  congrArg ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
      ((cechToBaseSections S Ui hU).app (tensorPlusOf S.sheaf K M (tensorPlus S K M).2))).hom
    (cycleClass_Q_cechCup_of S Ui hU K M (zc ⊗ₜ wc) z₀)

/-- The image under `cechToBaseSections` of the class of the cup product cycle is the `θ`-image
of its Čech class. -/
theorem cupPairing_chain₃ {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j)) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
          ((cechToBaseSections S Ui hU).app (tensorPlusOf S.sheaf K M (tensorPlus S K M).2))).hom
        (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing S)) (i + j)).inv.app
          (totalCechBase S Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2))).hom
          ((totalCechBase S Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2)).homologyπ (i + j)
            ((HomologicalComplex.cyclesMap
              (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
              (i + j)).hom (z₀.hom (zc ⊗ₜ wc))))) =
      hypercohomologyToCohomologyModule S (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j)
        (cechClass S.sheaf Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j)
          (((cechSections S.sheaf Ui hU).obj
              (tensorPlusOf S.sheaf K M (tensorPlus S K M).2).obj).homologyπ
            (i + j)
            ((HomologicalComplex.cyclesMap
              (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
              (i + j)).hom (z₀.hom (zc ⊗ₜ wc))))) :=
  (hypercohomologyToCohomologyModule_cechClass' S Ui hU
      (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j) _).symm.trans
    (congrArg
      (hypercohomologyToCohomologyModule S (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j))
      (cechClass_homologyπ_totalCechBase S Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2)
        (i + j)
        ((HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
          (i + j)).hom (z₀.hom (zc ⊗ₜ wc)))))

/-- The cochain of the cup product cycle is the Čech cup product, at the coefficient pairing
`sheafTensorPairingOf`, of the cochains of `zc` and `wc`. -/
theorem cupPairing_chain₄a {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    ((cechSections S.sheaf Ui hU).obj (tensorPlusOf S.sheaf K M (tensorPlus S K M).2).obj).iCycles
        (i + j)
        ((HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
          (i + j)).hom (z₀.hom (zc ⊗ₜ wc))) =
      (Stacks.CategoryTheory.CechComplex.ιTot (coverObject Ui hU)
          ((Stacks.Cech.Refinement.sectionsComplex S.sheaf).obj K.obj)
          ((Stacks.Cech.Refinement.sectionsComplex S.sheaf).obj M.obj) i j (i + j) rfl ≫
        (Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject Ui hU) _
          (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2)).f (i + j)).hom
        (Stacks.CategoryTheory.CechComplex.tmulHom
          (((cechSections S.sheaf Ui hU).obj K.obj).iCycles i zc)
          (((cechSections S.sheaf Ui hU).obj M.obj).iCycles j wc)) :=
  (iCycles_cechSections_totalCechBase S Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2)
      (i + j)
      ((HomologicalComplex.cyclesMap
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
        (i + j)).hom (z₀.hom (zc ⊗ₜ wc)))).trans
    ((iCycles_cyclesMap_cechCupProductSheafTensor_of S Ui hU K M zc wc z₀ hz₀).trans
      (cechCupProduct_tmulHom_iCycles S Ui hU K M zc wc).symm)

/-- The Čech cup product on hypercohomology of the classes of `zc` and `wc` is the Čech class of
the cup product cycle, with the classes taken in `cechSections`. -/
theorem cupPairing_chain₄b (hK : CechComputes S.sheaf K) (hM : CechComputes S.sheaf M)
    {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    cup S.sheaf hK hM (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2) i j (i + j) rfl
        (cechClass S.sheaf Ui hU K i (((cechSections S.sheaf Ui hU).obj K.obj).homologyπ i zc))
        (cechClass S.sheaf Ui hU M j (((cechSections S.sheaf Ui hU).obj M.obj).homologyπ j wc)) =
      cechClass S.sheaf Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j)
        (((cechSections S.sheaf Ui hU).obj
            (tensorPlusOf S.sheaf K M (tensorPlus S K M).2).obj).homologyπ
          (i + j)
          ((HomologicalComplex.cyclesMap
            (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
            (i + j)).hom (z₀.hom (zc ⊗ₜ wc)))) :=
  cup_sheafTensorPairingOf_cechClass_ofSections S.sheaf K M (tensorPlus S K M).2 Ui hU hK hM
    zc wc
    ((HomologicalComplex.cyclesMap
      (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
      (i + j)).hom (z₀.hom (zc ⊗ₜ wc)))
    (cupPairing_chain₄a S Ui hU K M zc wc z₀ hz₀)

/-- The Čech cup product on hypercohomology of the classes of `zc` and `wc`, in the two
spellings of the total Čech complex. -/
theorem cupPairing_chain₄c (hK : CechComputes S.sheaf K) (hM : CechComputes S.sheaf M)
    {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j) :
    cup S.sheaf hK hM (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2) i j (i + j) rfl
        (cechClass S.sheaf Ui hU K i ((totalCechBase S Ui hU K).homologyπ i zc))
        (cechClass S.sheaf Ui hU M j ((totalCechBase S Ui hU M).homologyπ j wc)) =
      cup S.sheaf hK hM (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2) i j (i + j) rfl
        (cechClass S.sheaf Ui hU K i (((cechSections S.sheaf Ui hU).obj K.obj).homologyπ i zc))
        (cechClass S.sheaf Ui hU M j (((cechSections S.sheaf Ui hU).obj M.obj).homologyπ j wc)) :=
  congrArg₂
    (cup S.sheaf hK hM (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2) i j (i + j) rfl)
    (cechClass_homologyπ_totalCechBase S Ui hU K i zc)
    (cechClass_homologyπ_totalCechBase S Ui hU M j wc)

/-- The Čech cup product on hypercohomology of the classes of `zc` and `wc` is the Čech class of
the cup product cycle. -/
theorem cupPairing_chain₄ (hK : CechComputes S.sheaf K) (hM : CechComputes S.sheaf M)
    {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    cup S.sheaf hK hM (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2) i j (i + j) rfl
        (cechClass S.sheaf Ui hU K i ((totalCechBase S Ui hU K).homologyπ i zc))
        (cechClass S.sheaf Ui hU M j ((totalCechBase S Ui hU M).homologyπ j wc)) =
      cechClass S.sheaf Ui hU (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j)
        (((cechSections S.sheaf Ui hU).obj
            (tensorPlusOf S.sheaf K M (tensorPlus S K M).2).obj).homologyπ
          (i + j)
          ((HomologicalComplex.cyclesMap
            (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)
            (i + j)).hom (z₀.hom (zc ⊗ₜ wc)))) :=
  (cupPairing_chain₄c S Ui hU K M hK hM zc wc).trans
    (cupPairing_chain₄b S Ui hU K M hK hM zc wc z₀ hz₀)

/-- The image of `zc ⊗ₜ wc` under the Čech cup product followed by `cechToBaseSections` is the
`θ`-image of the Čech cup product on hypercohomology of the classes of `zc` and `wc`. -/
theorem cupPairing_chain₅ (hK : CechComputes S.sheaf K) (hM : CechComputes S.sheaf M)
    {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    (cycleClass z₀ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
      ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
        (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj
          (tensorPlusOf S.sheaf K M (tensorPlus S K M).2).1)
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((cechToBaseSections S Ui hU).app (tensorPlusOf S.sheaf K M (tensorPlus S K M).2))).hom
          (zc ⊗ₜ wc) =
      hypercohomologyToCohomologyModule S (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j)
        (cup S.sheaf hK hM (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2) i j (i + j) rfl
          (cechClass S.sheaf Ui hU K i ((totalCechBase S Ui hU K).homologyπ i zc))
          (cechClass S.sheaf Ui hU M j ((totalCechBase S Ui hU M).homologyπ j wc))) :=
  (cupPairing_chain₂ S Ui hU K M zc wc z₀).trans ((cupPairing_chain₃ S Ui hU K M zc wc z₀).trans
    (congrArg
      (hypercohomologyToCohomologyModule S (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j))
      (cupPairing_chain₄ S Ui hU K M hK hM zc wc z₀ hz₀).symm))

/-- **The cup product of Section 0FKU of the classes of two Čech cocycles, followed by the
canonical map to the total tensor complex, is the Čech cup product of Section 01FP at the
sheaf-tensor coefficients**, on classes of cycles of a common covering. -/
theorem cupPairing_hypercohomologyToCohomologyModule_cycles (hK : CechComputes S.sheaf K)
    (hM : CechComputes S.sheaf M) {i j : ℤ} (zc : (totalCechBase S Ui hU K).cycles i)
    (wc : (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    (Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing K.1 M.1 i j).hom
      (hypercohomologyToCohomologyModule S K i (cechClass S.sheaf Ui hU K i
          ((totalCechBase S Ui hU K).homologyπ i zc)) ⊗ₜ
        hypercohomologyToCohomologyModule S M j (cechClass S.sheaf Ui hU M j
          ((totalCechBase S Ui hU M).homologyπ j wc))) =
      hypercohomologyToCohomologyModule S (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j)
        (cup S.sheaf hK hM (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2) i j (i + j) rfl
          (cechClass S.sheaf Ui hU K i ((totalCechBase S Ui hU K).homologyπ i zc))
          (cechClass S.sheaf Ui hU M j ((totalCechBase S Ui hU M).homologyπ j wc))) :=
  (cupPairing_hypercohomologyToCohomologyModule_cechClass_of S Ui hU K M zc wc z₀ hz₀).trans
    (cupPairing_chain₅ S Ui hU K M hK hM zc wc z₀ hz₀)

end Stacks.Cech.CupProductSquare

end
