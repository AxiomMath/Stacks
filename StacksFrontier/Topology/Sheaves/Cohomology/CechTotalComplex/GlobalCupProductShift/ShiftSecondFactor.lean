module

public import StacksFrontier.AlgebraicGeometry.Cohomology.FlasqueReductionOfTheCupProductSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductCocycles
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupPairingNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductShift
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift.ShiftCohomologyIsoR

/-!
# The global cup product and the shift of the second factor

Let `(S, 𝒪_S)` be a ringed space. For bounded below complexes `𝒦^•`, `ℳ^•` of `𝒪_S`-modules and
classes `ξ ∈ Hⁱ(S, 𝒦^•)`, `η ∈ Hʲ(S, ℳ^•[t])`, the cup product of `ξ` and `η`, carried to
`Hⁱ⁺ʲ⁺ᵗ(S, Tot(𝒦^• ⊗ ℳ^•))` by `mapBifunctorShift₂Iso` and the shift identification, is
`(-1)^{it}` times the cup product of `ξ` with `η` moved to `Hʲ⁺ᵗ(S, ℳ^•)`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_shift₂_globalCycleClass`: the cup
  product and the shift of the second factor, on classes of global cocycles.
* `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_shift₂`: **the cup product and the
  shift of the second factor.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.GlobalKunneth
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cohomology.DerivedSectionsLeray (sectionsUnitQ derivedSectionsOverOpen
  derivedSectionsOverOpenUnit sectionsOverOpen)
open RingTheory.TorProducts (cycleClass)
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

variable {S : RingedSpace.{u, u}}

/-! ### The cup product and the shift of the second factor, on flasque complexes -/

section ShiftTwo

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose

open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans totalComplexPair)

variable (K M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)

/-- The left hand side of `totalCupPairing_shift₂_globalCycleClass`, as one global cocycle
class. -/
theorem totalCupPairing_shift₂_lhs (t i j : ℤ) (z : ModuleCat.of (baseRing S) (baseRing S) ⟶
    (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ (shiftR M t)).cycles j)
    (z₀' : (((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).cycles i)).obj
        ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR M t)).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR M t))
            (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + j)))
    (hz₀' : (z₀' ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ K) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR M t))
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR M t)).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
              (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR M t))
              (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
              S.sheaf ⊤)) (ComplexShape.up ℤ) i j
            (i + j) rfl)) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ globalCycleClass w) ≫ totalCupPairing K (shiftR M t) i j ≫
        (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
          (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₂Iso K M
            (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
            (ComplexShape.up ℤ)) t (i + j) (i + (j + t)) (by omega)).hom =
      globalCycleClass (shiftCycles (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤
          (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
          (ComplexShape.up ℤ))) (i + (j + t)) (by omega)
        ((((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
            Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ z w ≫ z₀' ≫
          HomologicalComplex.cyclesMap
            (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ K (shiftR M t)) (i + j)) ≫
          HomologicalComplex.cyclesMap
              (((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (CochainComplex.mapBifunctorShift₂Iso K M
            (sheafTensor S.sheaf) t).hom) (i + j)) ≫
          HomologicalComplex.cyclesMap
              ((((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso t).hom.app (HomologicalComplex.mapBifunctor K M
              (sheafTensor S.sheaf) (ComplexShape.up ℤ))) (i + j))) :=
  (totalCupPairing_globalCycleClass_naive_assoc K (shiftR M t) z w z₀' hz₀' _).trans
    ((globalCycleClass_mapR_assoc _ _ _).trans
      (globalCycleClass_shiftCohomologyIsoR' _ t (i + j) (i + (j + t)) (by omega) _))

/-- The cocycle identity of `totalCupPairing_shift₂_globalCycleClass`. -/
theorem totalCupPairing_shift₂_cocycle (t i j : ℤ) (z : ModuleCat.of (baseRing S) (baseRing S) ⟶
    (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ (shiftR M t)).cycles j)
    (z₀' : (((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).cycles i)).obj
        ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR M t)).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR M t))
            (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + j)))
    (hz₀' : (z₀' ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ K) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR M t))
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR M t)).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
              (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR M t))
              (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
              S.sheaf ⊤)) (ComplexShape.up ℤ) i j
            (i + j) rfl))
    (z₀ : (((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).cycles i)).obj
        ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).cycles (j + t)) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + (j + t))))
    (hz₀ : (z₀ ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ K) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + (j + t)) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).iCycles (j + t)) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
              (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
              (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
              S.sheaf ⊤)) (ComplexShape.up ℤ) i (j + t)
            (i + (j + t)) rfl)) :
    (shiftCycles (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤
        (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
        (ComplexShape.up ℤ))) (i + (j + t)) (by omega)
        ((((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
            Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ z w ≫ z₀' ≫
          HomologicalComplex.cyclesMap
            (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ K (shiftR M t)) (i + j)) ≫
          HomologicalComplex.cyclesMap
              (((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (CochainComplex.mapBifunctorShift₂Iso K M
            (sheafTensor S.sheaf) t).hom) (i + j)) ≫
          HomologicalComplex.cyclesMap
              ((((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso t).hom.app (HomologicalComplex.mapBifunctor K M
              (sheafTensor S.sheaf) (ComplexShape.up ℤ))) (i + j))) =
      ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ ((i * t).negOnePow •
        (Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ z (shiftCycles
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M) (j + t) (by omega)
          (w ≫ HomologicalComplex.cyclesMap
              ((((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso t).hom.app M) j)) ≫ z₀ ≫
          HomologicalComplex.cyclesMap
            (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ K M)
              (i + (j + t))))) := by
  have k0 := @Stacks.Cech.SheafTensorPairing.cycles_naiveCupProductEval_shift₂ _ S.sheaf _ ⊤ K M t
    i j (ModuleCat.of (baseRing S) (baseRing S)) (ModuleCat.of (baseRing S) (baseRing S)) z w z₀'
  have k1 := k0 hz₀' z₀
  exact (shiftCycles_paste _ _ _ _ _ _ _ _ _).trans
    (congrArg ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ ·) (k1 hz₀))

/-- The right hand side of `totalCupPairing_shift₂_globalCycleClass`, as one global cocycle
class. -/
theorem totalCupPairing_shift₂_rhs (t i j : ℤ) (z : ModuleCat.of (baseRing S) (baseRing S) ⟶
    (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ (shiftR M t)).cycles j)
    (z₀ : (((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).cycles i)).obj
        ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).cycles (j + t)) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + (j + t))))
    (hz₀ : (z₀ ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ K) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + (j + t)) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).iCycles (j + t)) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
              (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
              (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
              S.sheaf ⊤)) (ComplexShape.up ℤ) i (j + t)
            (i + (j + t)) rfl)) :
    (i * t).negOnePow • ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ (globalCycleClass w ≫
          (shiftCohomologyIsoR M t j (j + t) (by omega)).hom)) ≫ totalCupPairing K M i (j + t)) =
      globalCycleClass ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ ((i * t).negOnePow •
        (Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ z (shiftCycles
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M) (j + t) (by omega)
          (w ≫ HomologicalComplex.cyclesMap
              ((((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso t).hom.app M) j)) ≫ z₀ ≫
          HomologicalComplex.cyclesMap
            (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ K M)
              (i + (j + t))))) := by
  have eR' := globalCycleClass_shiftCohomologyIsoR' M t j (j + t) (by omega) w
  have eR := totalCupPairing_globalCycleClass_naive K M z (shiftCycles
      (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M) (j + t) (by omega)
          (w ≫ HomologicalComplex.cyclesMap
              ((((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso t).hom.app M) j)) z₀ hz₀
  exact (congrArg ((i * t).negOnePow • ·) ((congrArg
    (fun x => (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (globalCycleClass z ⊗ₘ x) ≫
      totalCupPairing K M i (j + t)) eR').trans eR)).trans
    (globalCycleClass_unitor_units_smul _ _).symm

/-- **The cup product and the shift of the second factor, on classes of global cocycles.** For
global cocycles `z ∈ Zⁱ(Γ(S, 𝒦^•))` and `w ∈ Zʲ(Γ(S, ℳ^•[t]))`, the cup product of their classes,
carried to `Hⁱ⁺ʲ⁺ᵗ(S, Tot(𝒦^• ⊗ ℳ^•))` by `mapBifunctorShift₂Iso` and the shift identification,
is `(-1)^{it}` times the cup product of the class of `z` with the class of `w` moved to
`Hʲ⁺ᵗ(S, ℳ^•)`. -/
theorem totalCupPairing_shift₂_globalCycleClass (t i j : ℤ)
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶
        (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ (shiftR M t)).cycles j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ globalCycleClass w) ≫ totalCupPairing K (shiftR M t) i j ≫
        (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
          (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₂Iso K M
            (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
          (ComplexShape.up ℤ)) t (i + j) (i + (j + t)) (by omega)).hom =
      (i * t).negOnePow • ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ (globalCycleClass w ≫
          (shiftCohomologyIsoR M t j (j + t) (by omega)).hom)) ≫
              totalCupPairing K M i (j + t)) := by
  obtain ⟨z₀', hz₀'⟩ := exists_tensorCycles_naive K (shiftR M t) i j
  obtain ⟨z₀, hz₀⟩ := exists_tensorCycles_naive K M i (j + t)
  exact (totalCupPairing_shift₂_lhs K M t i j z w z₀' hz₀').trans
    ((congrArg globalCycleClass (totalCupPairing_shift₂_cocycle K M t i j z
        w z₀' hz₀' z₀ hz₀)).trans
      (totalCupPairing_shift₂_rhs K M t i j z w z₀ hz₀).symm)

/-- **Transport of the left hand side of the shift of the second factor along chain maps.** -/
theorem totalCupPairing_shift₂_transport_lhs {K₁ M₁ : (CochainComplex (SheafOfModules.{u}
    (ringSheaf.{u, u, u} S.sheaf)) ℤ)} (a : K ⟶ K₁) (b : M ⟶ M₁)
    (t i j : ℤ) (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj K) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj (shiftR M t)) j) :
    ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫ totalCupPairing K (shiftR M t) i
        j ≫ (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
        (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₂Iso K M
        (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
            (ComplexShape.up ℤ)) t (i + j) (i + (j + t)) (by omega)).hom) ≫
        (DerivedCategory.homologyFunctor _ (i + (j + t))).map ((baseSections S).map
            (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
            (sheafTensor S.sheaf) (ComplexShape.up ℤ)))) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
          ((ξ ≫ (DerivedCategory.homologyFunctor _ i).map ((baseSections S).map
          (DerivedCategory.Q.map a))) ⊗ₘ (η ≫ (DerivedCategory.homologyFunctor _ j).map
          ((baseSections S).map (DerivedCategory.Q.map ((CategoryTheory.shiftFunctor (CochainComplex
          (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map b))))) ≫
        totalCupPairing K₁ (shiftR M₁ t) i j ≫ (DerivedCategory.homologyFunctor _ (i + j)).map
            ((baseSections S).map (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₂Iso K₁ M₁
            (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K₁ M₁ (sheafTensor S.sheaf)
            (ComplexShape.up ℤ)) t (i + j) (i + (j + t)) (by omega)).hom := by
  have e1 := shiftCohomologyIsoR_naturality (HomologicalComplex.mapBifunctorMap a b
      (sheafTensor S.sheaf) (ComplexShape.up ℤ)) t (i + j) (i + (j + t)) (by omega)
  have e2 := homology_map_mapBifunctorShift₂Iso_naturality K M a b t (i + j)
  have e3 := totalCupPairing_naturality' a ((CategoryTheory.shiftFunctor (CochainComplex
      (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map b) i j ξ η
  exact paste_transport _ _ _ _ _ _ _ _ _ _ _ _ e1 e2 e3

/-- **Transport of the right hand side of the shift of the second factor along chain maps.** -/
theorem totalCupPairing_shift₂_transport_rhs {K₁ M₁ : (CochainComplex (SheafOfModules.{u}
    (ringSheaf.{u, u, u} S.sheaf)) ℤ)} (a : K ⟶ K₁) (b : M ⟶ M₁)
    (t i j : ℤ) (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj K) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj (shiftR M t)) j) :
    ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (ξ ⊗ₘ (η ≫ (shiftCohomologyIsoR M t j (j + t) (by omega)).hom)) ≫
        totalCupPairing K M i (j + t)) ≫ (DerivedCategory.homologyFunctor _ (i + (j + t))).map
            ((baseSections S).map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
            (sheafTensor S.sheaf) (ComplexShape.up ℤ)))) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
          ((ξ ≫ (DerivedCategory.homologyFunctor _ i).map ((baseSections S).map
          (DerivedCategory.Q.map a))) ⊗ₘ ((η ≫ (DerivedCategory.homologyFunctor _ j).map
          ((baseSections S).map (DerivedCategory.Q.map ((CategoryTheory.shiftFunctor (CochainComplex
          (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map b)))) ≫
        (shiftCohomologyIsoR M₁ t j (j + t) (by omega)).hom)) ≫
            totalCupPairing K₁ M₁ i (j + t) := by
  have e := totalCupPairing_naturality' a b i (j + t) ξ
    (η ≫ (shiftCohomologyIsoR M t j (j + t) (by omega)).hom)
  have hσ : (η ≫ (shiftCohomologyIsoR M t j (j + t) (by omega)).hom) ≫
      (DerivedCategory.homologyFunctor _ (j + t)).map ((baseSections S).map
      (DerivedCategory.Q.map b)) =
      (η ≫ (DerivedCategory.homologyFunctor _ j).map ((baseSections S).map (DerivedCategory.Q.map
          ((CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u}
          (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map b)))) ≫ (shiftCohomologyIsoR M₁ t j
          (j + t) (by omega)).hom :=
    (Category.assoc _ _ _).trans ((congrArg (η ≫ ·)
      (shiftCohomologyIsoR_naturality b t j (j + t) (by omega)).symm).trans
          (Category.assoc _ _ _).symm)
  exact ((Category.assoc _ _ _).trans (congrArg ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
      ·) (Category.assoc _ _ _))).trans
    (e.trans (congrArg (fun y => (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((ξ ≫ (DerivedCategory.homologyFunctor _ i).map ((baseSections S).map
        (DerivedCategory.Q.map a))) ⊗ₘ y) ≫
      totalCupPairing K₁ M₁ i (j + t)) hσ))

/-- `totalCupPairing_shift₂` on bounded below complexes of flasque modules, where every class is
the class of a global cocycle. -/
theorem totalCupPairing_shift₂_of_isFlasque (hK : ∃ n : ℤ, K.IsStrictlyGE n)
    (hM : ∃ n : ℤ, M.IsStrictlyGE n)
    (hKfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (K.X n)))
    (hMfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (M.X n)))
    (t i j : ℤ) (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj K) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj (shiftR M t)) j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫ totalCupPairing K (shiftR M t) i
        j ≫ (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
        (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₂Iso K M
        (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
            (ComplexShape.up ℤ)) t (i + j) (i + (j + t)) (by omega)).hom =
      (i * t).negOnePow • ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (ξ ⊗ₘ (η ≫ (shiftCohomologyIsoR M t j (j + t) (by omega)).hom)) ≫
          totalCupPairing K M i (j + t)) := by
  obtain ⟨z, rfl⟩ := exists_globalCycleClass_eq_of_isFlasque K hK hKfl i ξ
  obtain ⟨w, rfl⟩ := exists_globalCycleClass_eq_of_isFlasque (shiftR M t) (isStrictlyGE_shift hM t)
    (isFlasque_shift hMfl t) j η
  exact totalCupPairing_shift₂_globalCycleClass K M t i j z w

/-- **The cup product and the shift of the second factor.** For bounded below complexes `𝒦^•`,
`ℳ^•` of `𝒪_S`-modules and classes `ξ ∈ Hⁱ(S, 𝒦^•)`, `η ∈ Hʲ(S, ℳ^•[t])`, the cup product of `ξ`
and `η`, carried to `Hⁱ⁺ʲ⁺ᵗ(S, Tot(𝒦^• ⊗ ℳ^•))` by `mapBifunctorShift₂Iso` and the shift
identification, is `(-1)^{it}` times the cup product of `ξ` with `η` moved to `Hʲ⁺ᵗ(S, ℳ^•)`.

On flasque complexes this is `totalCupPairing_shift₂_globalCycleClass`; a general pair is
replaced by flasque resolutions whose total tensor complex is again a resolution
(`Stacks.Cohomology.FlasqueReduction.exists_flasqueResolution_quasiIso_tensor`), along which both
sides are natural. -/
theorem totalCupPairing_shift₂ (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hM : ∃ n : ℤ, M.IsStrictlyGE n)
    (t i j : ℤ) (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj K) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj (shiftR M t)) j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫ totalCupPairing K (shiftR M t) i
        j ≫ (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
        (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₂Iso K M
        (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
            (ComplexShape.up ℤ)) t (i + j) (i + (j + t)) (by omega)).hom =
      (i * t).negOnePow • ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (ξ ⊗ₘ (η ≫ (shiftCohomologyIsoR M t j (j + t) (by omega)).hom)) ≫
          totalCupPairing K M i (j + t)) := by
  obtain ⟨K₁, M₁, a, b, -, -, hK₁, hM₁, hKfl, hMfl, hab⟩ :=
    Stacks.Cohomology.FlasqueReduction.exists_flasqueResolution_quasiIso_tensor S K M hK hM
  have h1 : IsIso (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
      (sheafTensor S.sheaf) (ComplexShape.up ℤ))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := (HomologicalComplex.mapBifunctorMap a b
        (sheafTensor S.sheaf) (ComplexShape.up ℤ)))).2 hab
  have h2 : IsIso ((baseSections S).map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a
      b (sheafTensor S.sheaf) (ComplexShape.up ℤ)))) :=
    ((baseSections S).mapIso (@asIso _ _ _ _ (DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap a b (sheafTensor S.sheaf)
        (ComplexShape.up ℤ))) h1)).isIso_hom
  have h3 : IsIso ((DerivedCategory.homologyFunctor _ (i + (j + t))).map
      ((baseSections S).map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
          (sheafTensor S.sheaf) (ComplexShape.up ℤ))))) :=
    ((DerivedCategory.homologyFunctor _ (i + (j + t))).mapIso (@asIso _ _ _ _
      ((baseSections S).map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
          (sheafTensor S.sheaf) (ComplexShape.up ℤ)))) h2)).isIso_hom
  refine (cancel_mono ((DerivedCategory.homologyFunctor _ (i + (j + t))).map
      ((baseSections S).map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
          (sheafTensor S.sheaf) (ComplexShape.up ℤ)))))).1 ?_
  have eL := totalCupPairing_shift₂_transport_lhs K M a b t i j ξ η
  have eR := totalCupPairing_shift₂_transport_rhs K M a b t i j ξ η
  exact eL.trans ((totalCupPairing_shift₂_of_isFlasque K₁ M₁ hK₁ hM₁ hKfl hMfl t i j _ _).trans
    ((congrArg ((i * t).negOnePow • ·) eR.symm).trans (Linear.units_smul_comp _ _ _).symm))

end ShiftTwo

end Stacks.Cohomology.DerivedGlobalCupProduct

end
