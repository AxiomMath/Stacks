module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AugmentationDerivedTopVertical
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductSummand
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductOnSections

/-!
# The global cup product on global sections

Let `(S, 𝒪_S)` be a ringed space and `A = Γ(S, 𝒪_S)`.  For complexes `𝒦^•`, `ℳ^•` of
`𝒪_S`-modules the diagram

```
Γ(S, 𝒦^•) ⊗^𝐋_A Γ(S, ℳ^•) ───→ RΓ(S, 𝒦^•) ⊗^𝐋_A RΓ(S, ℳ^•)
          │                                    │ μ
          ↓                                    ↓
Tot(Γ(S, 𝒦^•) ⊗_A Γ(S, ℳ^•))           RΓ(S, 𝒦^• ⊗^𝐋 ℳ^•)
          │                                    │
          ↓                                    ↓
Γ(S, Tot(𝒦^• ⊗ ℳ^•)) ─────────────→ RΓ(S, Tot(𝒦^• ⊗ ℳ^•))
```

commutes in `D(A)`, `μ` being the global cup product of Cohomology, Section 0FKU and the left
column the naive cup product.  This is [Stacks, Tag 0FP3] for the morphism `(S, 𝒪_S) ⟶ (pt, A)`,
as in the discussion preceding [Stacks, Tag 0FKV].

## Main results

* `Stacks.Cech.SheafTensorPairing.naiveCupProductEval`: the naive cup product on sections, with
  sections read by evaluation.
* `Stacks.Cech.CupProductSquare.globalCupProduct_naiveCupProduct`: **the diagram.**
* `Stacks.Cech.CupProductSquare.augmentation_comp_cechRightLeg`: the right-hand leg of
  [Stacks, Tag 0FKV], precomposed with the Čech augmentation in both tensor factors, is the
  canonical map at the two complexes of sections, the naive cup product and the unit.

## Implementation notes

The `Stacks.Cech.SheafTensorPairing` section takes
`(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat` as an instance argument:
`Stacks.SheafOfModules.Tensor.sheafTensor` takes it as an instance argument, and synthesizing
`∀ F, ((sheafTensor 𝒪_X).obj F).Additive` puts `sheafTensor 𝒪_X` under a binder, where the
∀-abstracted search for it exceeds the `synthInstance` budget.  It is discharged by synthesis at
every instantiation, so the `Stacks.Cech.CupProductSquare` results below, read at `S.sheaf` for a
ringed space `S`, do not carry it.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.CechSheaf (sectionsTerminalFunctorIso)
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cech.ModuleCupProduct (CoeffRing sectionsComplexFunctor)
open Stacks.Cech.CupProduct (tensorModules)
open scoped CategoryTheory.Prod TensorProduct

universe u

namespace Stacks.Cech.SheafTensorPairing

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (V : Opens X) (K L : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} O)) ℤ)

/-- Sections at the terminal object of the slice over `V` are sections over `V`, on complexes. -/
abbrev sectionsAtTerminalIso (T : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} O)) ℤ) :
    sectionsAtTerminal O V T ≅
      ((SheafOfModules.evaluation (ringSheaf.{u, u, u} O) (op V)).mapHomologicalComplex
        (up ℤ)).obj T :=
  (NatIso.mapHomologicalComplex
    (sectionsTerminalFunctorIso.{u, u, u} (R := ringSheaf.{u, u, u} O) V) (up ℤ)).app T

/-- **The naive cup product** `Tot(Γ(V, 𝒦^•) ⊗_A Γ(V, ℒ^•)) ⟶ Γ(V, Tot(𝒦^• ⊗_{𝒪_X} ℒ^•))` of the
sheaf-tensor pairing, `A = 𝒪_X(V)`, with sections read by evaluation at `V`. -/
def naiveCupProductEval :
    HomologicalComplex.mapBifunctor
        (((SheafOfModules.evaluation (ringSheaf.{u, u, u} O) (op V)).mapHomologicalComplex
          (up ℤ)).obj K)
        (((SheafOfModules.evaluation (ringSheaf.{u, u, u} O) (op V)).mapHomologicalComplex
          (up ℤ)).obj L)
        (tensorModules (CoeffRing O V)) (up ℤ) ⟶
      ((SheafOfModules.evaluation (ringSheaf.{u, u, u} O) (op V)).mapHomologicalComplex
        (up ℤ)).obj (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)) :=
  HomologicalComplex.mapBifunctorMap (sectionsAtTerminalIso O V K).inv
      (sectionsAtTerminalIso O V L).inv (tensorModules (CoeffRing O V)) (up ℤ) ≫
    naiveCupProductA O V K L ≫
      (sectionsAtTerminalIso O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))).hom

/-- The complex `Γ(V, T^•)` of sections over `V`, read by evaluation at `V`. -/
abbrev evalComplex (T : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} O)) ℤ) :=
  ((SheafOfModules.evaluation (ringSheaf.{u, u, u} O) (op V)).mapHomologicalComplex (up ℤ)).obj T

/-- The naive cup product on a summand is the coefficient pairing, conjugated by the
identification of sections at the terminal object with sections over `V`. -/
theorem naiveCupProductEval_ι (p q n : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ) p q n h ≫ (naiveCupProductEval O V K L).f n =
      ((tensorModules (CoeffRing O V)).map ((sectionsAtTerminalIso O V K).inv.f p)).app _ ≫
        ((tensorModules (CoeffRing O V)).obj _).map ((sectionsAtTerminalIso O V L).inv.f q) ≫
        ((sheafTensorComplexPairing O V K L).μ p q n h).app (op (Over.mk (𝟙 V))) ≫
        (sectionsAtTerminalIso O V
          (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))).hom.f n := by
  dsimp only [naiveCupProductEval]
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  exact congrArg (fun z => _ ≫ _ ≫ z) (Stacks.Cech.LinearCupProduct.ι_naiveCupProductDegree_assoc
    (CoeffRing O V) (sheafTensorComplexPairing O V K L) (op (Over.mk (𝟙 V))) p q n h _)

/-- The naive cup product at the terminal object of the slice is the naive cup product on
evaluation, conjugated by the identification of the two presentations of sections. -/
theorem naiveCupProductA_comp_iso :
    HomologicalComplex.mapBifunctorMap (sectionsAtTerminalIso O V K).hom
        (sectionsAtTerminalIso O V L).hom (tensorModules (CoeffRing O V)) (up ℤ) ≫
      naiveCupProductEval O V K L =
    naiveCupProductA O V K L ≫
      (sectionsAtTerminalIso O V
        (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))).hom := by
  rw [naiveCupProductEval, ← Category.assoc, HomologicalComplex.mapBifunctorMap_comp,
    Iso.hom_inv_id, Iso.hom_inv_id, HomologicalComplex.mapBifunctorMap_id, Category.id_comp]

end Stacks.Cech.SheafTensorPairing

namespace Stacks.Cech.CupProductSquare

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

open Stacks.Cohomology.GlobalKunneth (baseRing baseSections tensorBase)
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedGlobalCupProduct (globalSections)
open CochainComplex.DerivedTensor.ToTotal (canonicalDerivedToTensorNatTrans)

variable (S : RingedSpace.{u, u})
  (K M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)

open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans totalComplexPair)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex naiveCupProduct)
open Stacks.Cohomology.DerivedSectionsOnAPoint

/-- The naive cup product on the point for `π_*K`, `π_*M`, followed by `Γ` of the naive cup
product of `π`. -/
abbrev pointNaive : HomologicalComplex.mapBifunctor
    (((onePointSections ↥(baseRing S)).mapHomologicalComplex (up ℤ)).obj
      ((pushforwardComplex (toCoeffPoint S)).obj K))
    (((onePointSections ↥(baseRing S)).mapHomologicalComplex (up ℤ)).obj
      ((pushforwardComplex (toCoeffPoint S)).obj M))
    (MonoidalCategory.curriedTensor (onePointModuleCat ↥(baseRing S))) (up ℤ) ⟶
    ((sectionsOverOpen (coeffPt S) ⊤).mapHomologicalComplex (up ℤ)).obj
      ((pushforwardComplex (toCoeffPoint S)).obj
        ((totalComplexPair (sheafTensor S.sheaf)).obj (K, M))) :=
  (onePointSectionsTotalIso ↥(baseRing S) ((pushforwardComplex (toCoeffPoint S)).obj K)
      ((pushforwardComplex (toCoeffPoint S)).obj M)).inv ≫
    ((sectionsOverOpen (coeffPt S) ⊤).mapHomologicalComplex (up ℤ)).map
      (naiveCupProduct (toCoeffPoint S) K M)

private theorem hP_paste {C : Type*} [Category* C] {a0 a1 a2 a3 a4 c1 c2 c3 : C}
    (a : a0 ⟶ a1) (B : a1 ⟶ a3) (B1 : a1 ⟶ a2) (B2 : a2 ⟶ a3) (g : a3 ⟶ a4)
    (c : a0 ⟶ c1) (qnv : c1 ⟶ c3) (qt : c1 ⟶ c2) (qΓ : c2 ⟶ c3) (u : c3 ⟶ a4)
    (h1 : B = B1 ≫ B2) (h2 : qnv = qt ≫ qΓ) (hP : a ≫ B1 ≫ B2 ≫ g = c ≫ qt ≫ qΓ ≫ u) :
    a ≫ B ≫ g = c ≫ qnv ≫ u := by
  subst h1 h2
  simpa only [Category.assoc] using hP

/-- The naive cup product square over the point's ring, for the canonical presentation. -/
theorem canonicalPresentation_naive :
    (Functor.uncurry.obj (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
          ↥(baseRing (coeffPt S)))).map (pointSectionsUnit S K ×ₘ pointSectionsUnit S M) ≫
        Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap
          (canonicalPointPresentation S).adjunction (Functor.uncurry.obj
            (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
              ↥(baseRing (coeffPt S))))
          (spaceTensor S) (canonicalPointPresentation S).tensorIso.hom (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj M) ≫
        (derivedPushforward (toCoeffPoint S) ⋙ baseSections (coeffPt S)).map
          ((derivedToTensorNatTrans S).app (K, M)) =
      (canonicalDerivedToTensorNatTrans ↥(baseRing (coeffPt S))).app
          (((onePointSections ↥(baseRing S)).mapHomologicalComplex (up ℤ)).obj
              ((pushforwardComplex (toCoeffPoint S)).obj K),
            ((onePointSections ↥(baseRing S)).mapHomologicalComplex (up ℤ)).obj
              ((pushforwardComplex (toCoeffPoint S)).obj M)) ≫
        DerivedCategory.Q.map (pointNaive S K M) ≫
        pointSectionsUnit S ((totalComplexPair (sheafTensor S.sheaf)).obj (K, M)) :=
  hP_paste _ _ _ _ _ _ _ _ _ _
    (canonicalPointPresentation_adjunctionBitensorMap S _ _) (DerivedCategory.Q.map_comp _ _)
    (pointNaiveCupProduct_relativeCupProduct S K M)

/-- The naive cup product on the point, on a summand. -/
theorem pointNaive_ι (p q n : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor _ _
        (MonoidalCategory.curriedTensor (onePointModuleCat ↥(baseRing S))) (up ℤ) p q n h ≫
        (pointNaive S K M).f n =
      (onePointTensorSectionsMap ↥(baseRing S)).app
          (((pushforwardComplex (toCoeffPoint S)).obj K).X p,
            ((pushforwardComplex (toCoeffPoint S)).obj M).X q) ≫
        (onePointSections ↥(baseRing S)).map (HomologicalComplex.ιMapBifunctor
          ((pushforwardComplex (toCoeffPoint S)).obj K)
          ((pushforwardComplex (toCoeffPoint S)).obj M)
          (sheafTensor (onePointRingedSpace ↥(baseRing S)).sheaf) (up ℤ) p q n h) ≫
        (sectionsOverOpen (coeffPt S) ⊤).map ((naiveCupProduct (toCoeffPoint S) K M).f n) :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (onePointSectionsTotalIso_inv_ι ↥(baseRing S) ((pushforwardComplex (toCoeffPoint S)).obj K)
      ((pushforwardComplex (toCoeffPoint S)).obj M) p q n h) |>.trans (Category.assoc _ _ _))

/-- **The naive cup product on the point agrees with the naive cup product on `S` on pure
tensors**: both send `x ⊗ y` to the sheafification-unit image of `x ⊗ y`. -/
theorem pointNaive_tmul (p q n : ℤ) (hpq : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = n)
    (x : (((globalSections S).mapHomologicalComplex (up ℤ)).obj K).X p)
    (y : (((globalSections S).mapHomologicalComplex (up ℤ)).obj M).X q) :
    ((pointNaive S K M).f n).hom ((HomologicalComplex.ιMapBifunctor
        (((ModuleCat.restrictScalars.{u} (coeffStructMapComm S)).mapHomologicalComplex (up ℤ)).obj
          (((globalSections S).mapHomologicalComplex (up ℤ)).obj K))
        (((ModuleCat.restrictScalars.{u} (coeffStructMapComm S)).mapHomologicalComplex (up ℤ)).obj
          (((globalSections S).mapHomologicalComplex (up ℤ)).obj M))
        (MonoidalCategory.curriedTensor (ModuleCat.{u} ↥(baseRing (coeffPt S)))) (up ℤ)
          p q n hpq).hom (x ⊗ₜ y)) =
      ((Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ K M).f n).hom
        ((HomologicalComplex.ιMapBifunctor (((globalSections S).mapHomologicalComplex (up ℤ)).obj K)
          (((globalSections S).mapHomologicalComplex (up ℤ)).obj M)
          (MonoidalCategory.curriedTensor (ModuleCat.{u} ↥(baseRing S))) (up ℤ)
            p q n hpq).hom (x ⊗ₜ y)) := by
  let x₁ : (((onePointSections ↥(baseRing S)).mapHomologicalComplex (up ℤ)).obj
      ((pushforwardComplex (toCoeffPoint S)).obj K)).X p := x
  let y₁ : (((onePointSections ↥(baseRing S)).mapHomologicalComplex (up ℤ)).obj
      ((pushforwardComplex (toCoeffPoint S)).obj M)).X q := y
  let x₂ : (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).X p := x
  let y₂ : (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).X q := y
  have e1 := congrArg (fun f => ModuleCat.Hom.hom f (x₁ ⊗ₜ y₁)) (pointNaive_ι S K M p q n hpq)
  have e2 := Stacks.Cohomology.NaiveCupProductSummand.naiveCupProduct_sheafTensorComplexPairing
    S K M p q n hpq x y
  have e3 := congrArg (fun f => ModuleCat.Hom.hom f (x₂ ⊗ₜ y₂))
    (Stacks.Cech.SheafTensorPairing.naiveCupProductEval_ι S.sheaf ⊤ K M p q n hpq)
  exact e1.trans (e2.trans e3.symm)

/-- The naive cup product square over the point's ring for the canonical presentation, with the
complexes of sections over the point written as restrictions of scalars of global sections. -/
theorem canonicalPresentation_naive_res :
    (Functor.uncurry.obj (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
          ↥(baseRing (coeffPt S)))).map (pointSectionsUnit S K ×ₘ pointSectionsUnit S M) ≫
        Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap
          (canonicalPointPresentation S).adjunction (Functor.uncurry.obj
            (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
              ↥(baseRing (coeffPt S))))
          (spaceTensor S) (canonicalPointPresentation S).tensorIso.hom (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj M) ≫
        (derivedPushforward (toCoeffPoint S) ⋙ baseSections (coeffPt S)).map
          ((derivedToTensorNatTrans S).app (K, M)) =
      (canonicalDerivedToTensorNatTrans ↥(baseRing (coeffPt S))).app
          (((ModuleCat.restrictScalars.{u} (coeffStructMapComm S)).mapHomologicalComplex (up ℤ)).obj
              (((globalSections S).mapHomologicalComplex (up ℤ)).obj K),
            ((ModuleCat.restrictScalars.{u} (coeffStructMapComm S)).mapHomologicalComplex
                (up ℤ)).obj
              (((globalSections S).mapHomologicalComplex (up ℤ)).obj M)) ≫
        DerivedCategory.Q.map (pointNaive S K M) ≫
        pointSectionsUnit S ((totalComplexPair (sheafTensor S.sheaf)).obj (K, M)) :=
  canonicalPresentation_naive S K M

/-- **The global cup product against the naive cup product on global sections.**  For
complexes `𝒦^•`, `ℳ^•` of `𝒪_S`-modules, `A = Γ(S, 𝒪_S)`, the unit `Γ ⟶ RΓ` in each factor
followed by the global cup product `μ` of Cohomology, Section 0FKU and `RΓ` of the canonical map
`𝒦^• ⊗^𝐋 ℳ^• ⟶ Tot(𝒦^• ⊗ ℳ^•)` is the canonical map
`Γ(S, 𝒦^•) ⊗^𝐋_A Γ(S, ℳ^•) ⟶ Tot(Γ(S, 𝒦^•) ⊗_A Γ(S, ℳ^•))`, the naive cup product and the unit at
`Tot(𝒦^• ⊗ ℳ^•)`.  This is [Stacks, Tag 0FP3] for the morphism `(S, 𝒪_S) ⟶ (pt, A)`, the
diagram displayed before [Stacks, Tag 0FKV]. -/
theorem globalCupProduct_naiveCupProduct :
    (Functor.uncurry.obj (tensorBase S)).map (sectionsUnitQ S ⊤ K ×ₘ sectionsUnitQ S ⊤ M) ≫
        (globalCupProduct (canonicalOnePointComparison S)).app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj M) ≫
        (baseSections S).map ((derivedToTensorNatTrans S).app (K, M)) =
      (canonicalDerivedToTensorNatTrans ↥(baseRing S)).app
          (((globalSections S).mapHomologicalComplex (up ℤ)).obj K,
            ((globalSections S).mapHomologicalComplex (up ℤ)).obj M) ≫
        DerivedCategory.Q.map (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ K M) ≫
        sectionsUnitQ S ⊤ ((totalComplexPair (sheafTensor S.sheaf)).obj (K, M)) :=
  globalCupProduct_naive_of_presentation (baseRing_coeffPoint S) (coeffStructMapComm S)
    (heq_coeffStructMap S) (canonicalPointPresentation S)
    (Stacks.Cohomology.GlobalKunneth.lerayIso (toCoeffPoint S) ≪≫
      (derivedPreimageSectionsIso S).symm) K M
    ((totalComplexPair (sheafTensor S.sheaf)).obj (K, M)) ((derivedToTensorNatTrans S).app (K, M))
    (pointSectionsUnit S) (pointSectionsUnit_comp_lerayIso S) (pointNaive S K M)
    (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ K M) (pointNaive_tmul S K M)
    (canonicalPresentation_naive_res S K M)

private theorem id_id_comp {C : Type*} [Category* C] {x y : C} (a b : x ⟶ x) (c : x ⟶ y)
    (ha : a = 𝟙 x) (hb : b = 𝟙 x) : a ≫ b ≫ c = c := by
  simp [ha, hb]

private theorem sectionsUnit_paste {C : Type*} [Category* C] {x0 x1 x2 x3 x4 x5 y4 y5 : C}
    (a1 : x0 ⟶ x1) (a2 : x1 ⟶ x2) (a3 : x2 ⟶ x3) (a4 : x3 ⟶ x4) (a5 : x4 ⟶ x5) (b : x5 ⟶ y5)
    (bh : x4 ⟶ y4) (uB : x3 ⟶ y4) (uB' : x1 ⟶ y4) (rq : y4 ⟶ y5) (rq' : y4 ⟶ y5)
    (h23 : a2 ≫ a3 ≫ uB = uB') (h : a4 ≫ bh = uB) (hn : a5 ≫ b = bh ≫ rq) (hr : rq = rq') :
    (a1 ≫ a2 ≫ a3 ≫ a4 ≫ a5) ≫ b = a1 ≫ uB' ≫ rq' := by
  subst hr h23 h
  simp [hn]

/-- **The unit of the bounded below model is the unit of the unbounded model**: the unit
`Γ(S, 𝒯^•) ⟶ RΓ(S, 𝒯^•)` of `sectionsToBaseSections`, built from the bounded below derived
functor of sections and the comparison of the two models, is `sectionsUnitQ`. -/
theorem sectionsToBaseSections_app_eq
    (T : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))) :
    (sectionsToBaseSections S).app T = sectionsUnitQ S ⊤ T.1 := by
  have h := Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso_hom_app S ⊤
    ((HomotopyCategory.Plus.quotient _).obj T)
  have hn := (Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso S ⊤).hom.naturality
    ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ
      (SheafOfModules.{u} (structureSheafRing S))).hom.app T)
  have hι : DerivedCategory.Plus.ι.map ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ
      (SheafOfModules.{u} (structureSheafRing S))).hom.app T) =
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing S))).hom.app T.1 :=
    StacksDraft.DerivedSectionsComparison.liftNatIso_hom_app _ _ _ _ T
  rw [sectionsToBaseSections_app]
  dsimp only [Stacks.Cech.Linear.sectionsToDerived, Stacks.Cech.Linear.sectionsToDerivedNat,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  refine sectionsUnit_paste _ _ _ _ _ _ _ _ _ _ _ ?_ h hn ?_
  · have hb : DerivedCategory.Qh.map ((Stacks.Cech.Linear.sectionsHomotopyBridgeIso S.carrier
        (ringSheaf.{u, u, u} S.sheaf) ⊤).inv.app T) = 𝟙 _ := DerivedCategory.Qh.map_id _
    exact id_id_comp _ _ _ hb rfl
  · exact congrArg (derivedSectionsOverOpen S ⊤).map hι

open Stacks.Cech.SheafTensorPairing (sectionsAtTerminal sectionsAtTerminalIso naiveCupProductA
  naiveCupProductEval evalComplex)
open CochainComplex.DerivedTensor.ToTotal (canonicalDerivedToTensorComp
  canonicalDerivedToTensorNatTrans_naturality)

/-- A pasting of commutative squares, with every object and morphism a variable. -/
private theorem right_paste {C : Type*} [Category* C] (A : C × C ⥤ C)
    {xK xM cK cM gK gM RK RM Rb Rt sΓ gT sA xT : C}
    (aK : xK ⟶ cK) (aM : xM ⟶ cM) (cbK : cK ⟶ RK) (cbM : cM ⟶ RM) (iK : xK ⟶ gK) (iM : xM ⟶ gM)
    (uK : gK ⟶ RK) (uM : gM ⟶ RM) (hK : aK ≫ cbK = iK ≫ uK) (hM : aM ≫ cbM = iM ≫ uM)
    (μ : A.obj (RK, RM) ⟶ Rb) (rτ : Rb ⟶ Rt) (τΓ : A.obj (gK, gM) ⟶ sΓ) (qnv : sΓ ⟶ gT)
    (uT : gT ⟶ Rt) (hG : A.map (uK ×ₘ uM) ≫ μ ≫ rτ = τΓ ≫ qnv ≫ uT)
    (τA : A.obj (xK, xM) ⟶ sA) (qiso : sA ⟶ sΓ) (hnat : A.map (iK ×ₘ iM) ≫ τΓ = τA ≫ qiso)
    (qnA : sA ⟶ xT) (iT : xT ⟶ gT) (hnv : qiso ≫ qnv = qnA ≫ iT) :
    A.map (aK ×ₘ aM) ≫ A.map (cbK ×ₘ cbM) ≫ μ ≫ rτ = τA ≫ qnA ≫ iT ≫ uT := by
  rw [← A.map_comp_assoc, show (aK ×ₘ aM) ≫ (cbK ×ₘ cbM) = (iK ×ₘ iM) ≫ (uK ×ₘ uM) by
    rw [prod_comp, prod_comp, hK, hM], A.map_comp_assoc, hG, reassoc_of% hnat, reassoc_of% hnv]

/-- **The right-hand leg of [Stacks, Tag 0FKV]'s square after the augmentation of
[Stacks, Tag 07M9] in both tensor factors is the left-hand column of the diagram preceding the
tag**: the canonical map at the complexes of sections, the naive cup product, and the unit
`Γ(S, -) ⟶ RΓ(S, -)` at `Tot(𝒦^• ⊗ ℳ^•)`. -/
theorem augmentation_comp_cechRightLeg {I : Type u} (Ui : I → Opens S.carrier)
    (hU : (⊤ : Opens S.carrier) = ⨆ i, Ui i)
    (K M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))) :
    (Functor.uncurry.obj (tensorBase S)).map
          (DerivedCategory.Q.map
              (Stacks.Cech.SheafTensorPairing.augmentationA S.sheaf ⊤ Ui hU K.1) ×ₘ
            DerivedCategory.Q.map
              (Stacks.Cech.SheafTensorPairing.augmentationA S.sheaf ⊤ Ui hU M.1)) ≫
        cechRightLeg S Ui hU K M =
      canonicalDerivedToTensorComp (CoeffRing.{u} S.sheaf ⊤) _ _ _
          (naiveCupProductA S.sheaf ⊤ K.1 M.1) ≫
        sectionsAtTerminalToBaseSections S (tensorPlus S K M) := by
  have hB : ∀ T : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)),
      sectionsAtTerminalToBaseSections S T =
        DerivedCategory.Q.map (sectionsAtTerminalIso S.sheaf ⊤ T.1).hom ≫
          sectionsUnitQ S ⊤ T.1 :=
    fun T => congrArg (fun z => DerivedCategory.Q.map (sectionsAtTerminalIso S.sheaf ⊤ T.1).hom ≫ z)
      (sectionsToBaseSections_app_eq S T)
  have hK := (augmentationA_comp_cechToBaseSectionsA S Ui hU K).trans (hB K)
  have hM := (augmentationA_comp_cechToBaseSectionsA S Ui hU M).trans (hB M)
  have hnv := (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map
      (Stacks.Cech.SheafTensorPairing.naiveCupProductA_comp_iso S.sheaf ⊤ K.1 M.1)).trans
      (DerivedCategory.Q.map_comp _ _))
  have hnat := canonicalDerivedToTensorNatTrans_naturality (CoeffRing.{u} S.sheaf ⊤)
    (sectionsAtTerminalIso S.sheaf ⊤ K.1).hom (sectionsAtTerminalIso S.sheaf ⊤ M.1).hom
  have hG := globalCupProduct_naiveCupProduct S K.1 M.1
  rw [hB (tensorPlus S K M)]
  exact (right_paste (Functor.uncurry.obj (tensorBase S)) _ _ _ _ _ _ _ _ hK hM _ _ _ _ _ hG
    _ _ hnat _ _ hnv).trans (Category.assoc _ _ _).symm

end Stacks.Cech.CupProductSquare
