module

public import StacksFrontier.AlgebraicGeometry.Cohomology.FlasqueReductionOfTheCupProductSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductCocycles
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupPairingNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductShift
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift.ShiftCohomologyIsoR

/-!
# The global cup product and the shift of the first factor

Let `(S, 𝒪_S)` be a ringed space. For bounded below complexes `𝒦^•`, `ℳ^•` of `𝒪_S`-modules and
classes `ξ ∈ Hⁱ(S, 𝒦^•[t])`, `η ∈ Hʲ(S, ℳ^•)`, the cup product of `ξ` and `η`, carried to
`Hⁱ⁺ᵗ⁺ʲ(S, Tot(𝒦^• ⊗ ℳ^•))` by `mapBifunctorShift₁Iso` and the shift identification, is the cup
product of `ξ` moved to `Hⁱ⁺ᵗ(S, 𝒦^•)` with `η`. There is no sign.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_shift₁_globalCycleClass`: the cup
  product and the shift of the first factor, on classes of global cocycles.
* `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_shift₁`: **the cup product and the
  shift of the first factor.**
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

section ShiftTwo

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose

open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans totalComplexPair)

variable (K M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)

/-! ### The cup product and the shift of the first factor -/

/-- `mapBifunctorShift₁Iso` is natural, read on cohomology. -/
theorem homology_map_mapBifunctorShift₁Iso_naturality {K₁ M₁ : (CochainComplex (SheafOfModules.{u}
    (ringSheaf.{u, u, u} S.sheaf)) ℤ)} (a : K ⟶ K₁) (b : M ⟶ M₁)
    (t n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).map ((baseSections S).map (DerivedCategory.Q.map
        (CochainComplex.mapBifunctorShift₁Iso K M (sheafTensor S.sheaf) t).hom)) ≫
        (DerivedCategory.homologyFunctor _ n).map ((baseSections S).map (DerivedCategory.Q.map
            ((CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u}
            (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map (HomologicalComplex.mapBifunctorMap a b
            (sheafTensor S.sheaf) (ComplexShape.up ℤ))))) =
      (DerivedCategory.homologyFunctor _ n).map ((baseSections S).map (DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap ((CategoryTheory.shiftFunctor (CochainComplex
          (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map a) b (sheafTensor S.sheaf)
          (ComplexShape.up ℤ)))) ≫ (DerivedCategory.homologyFunctor _ n).map ((baseSections S).map
          (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₁Iso K₁ M₁
          (sheafTensor S.sheaf) t).hom)) := by
  let Hn := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n
  have e := mapBifunctorShift₁Iso_hom_naturality (sheafTensor S.sheaf) a b t
  exact (Hn.map_comp _ _).symm.trans ((congrArg Hn.map ((baseSections S).map_comp _ _).symm).trans
    ((congrArg (fun g => Hn.map ((baseSections S).map g))
        ((DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map e.symm).trans (DerivedCategory.Q.map_comp _ _)))).trans
        ((congrArg Hn.map ((baseSections S).map_comp _ _)).trans (Hn.map_comp _ _))))

/-- The left hand side of `totalCupPairing_shift₁_globalCycleClass`, as one global cocycle
class. -/
theorem totalCupPairing_shift₁_lhs (t i j : ℤ) (z : ModuleCat.of (baseRing S) (baseRing S) ⟶
    (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR K t)).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶
        (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).cycles j)
    (z₀' : (((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤
        (shiftR K t)).cycles i)).obj
        ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤
            (shiftR K t)) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + j)))
    (hz₀' : (z₀' ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ (shiftR K t)) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR K t)).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤
              (shiftR K t)) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
              (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
              S.sheaf ⊤)) (ComplexShape.up ℤ) i j
            (i + j) rfl)) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ globalCycleClass w) ≫ totalCupPairing (shiftR K t) M i j ≫
        (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map (DerivedCategory.Q.map
            (CochainComplex.mapBifunctorShift₁Iso K M (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
            (ComplexShape.up ℤ)) t (i + j) ((i + t) + j) (by omega)).hom =
      globalCycleClass (shiftCycles (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤
          (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
          (ComplexShape.up ℤ))) ((i + t) + j) (by omega)
        ((((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
            Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ z w ≫ z₀' ≫
          HomologicalComplex.cyclesMap
            (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ (shiftR K t) M) (i + j)) ≫
          HomologicalComplex.cyclesMap
              (((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (CochainComplex.mapBifunctorShift₁Iso K M (sheafTensor S.sheaf) t).hom) (i + j)) ≫
          HomologicalComplex.cyclesMap
              ((((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso t).hom.app (HomologicalComplex.mapBifunctor K M
              (sheafTensor S.sheaf) (ComplexShape.up ℤ))) (i + j))) :=
  (totalCupPairing_globalCycleClass_naive_assoc (shiftR K t) M z w z₀' hz₀' _).trans
    ((globalCycleClass_mapR_assoc _ _ _).trans
      (globalCycleClass_shiftCohomologyIsoR' _ t (i + j) ((i + t) + j) (by omega) _))

/-- The cocycle identity of `totalCupPairing_shift₁_globalCycleClass`. -/
theorem totalCupPairing_shift₁_cocycle (t i j : ℤ) (z : ModuleCat.of (baseRing S) (baseRing S) ⟶
    (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR K t)).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶
        (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).cycles j)
    (z₀' : (((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤
        (shiftR K t)).cycles i)).obj
        ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤
            (shiftR K t)) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + j)))
    (hz₀' : (z₀' ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ (shiftR K t)) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR K t)).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤
              (shiftR K t)) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
              (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
              S.sheaf ⊤)) (ComplexShape.up ℤ) i j
            (i + j) rfl))
    (z₀ : (((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).cycles
        (i + t))).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles ((i + t) + j)))
    (hz₀ : (z₀ ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ K) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles ((i + t) + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).iCycles (i + t))
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
              (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
              (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
              S.sheaf ⊤)) (ComplexShape.up ℤ) (i + t) j
            ((i + t) + j) rfl)) :
    (shiftCycles (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤
        (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
        (ComplexShape.up ℤ))) ((i + t) + j) (by omega)
        ((((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
            Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ z w ≫ z₀' ≫
          HomologicalComplex.cyclesMap
            (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ (shiftR K t) M) (i + j)) ≫
          HomologicalComplex.cyclesMap
              (((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (CochainComplex.mapBifunctorShift₁Iso K M (sheafTensor S.sheaf) t).hom) (i + j)) ≫
          HomologicalComplex.cyclesMap
              ((((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso t).hom.app (HomologicalComplex.mapBifunctor K M
              (sheafTensor S.sheaf) (ComplexShape.up ℤ))) (i + j))) =
      ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ (shiftCycles
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K) (i + t) (by omega)
          (z ≫ HomologicalComplex.cyclesMap
              ((((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso t).hom.app K) i)) w ≫ z₀ ≫
          HomologicalComplex.cyclesMap
            (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ K M) ((i + t) + j)) := by
  have k0 := @Stacks.Cech.SheafTensorPairing.cycles_naiveCupProductEval_shift₁ _ S.sheaf _ ⊤ K M t
    i j (ModuleCat.of (baseRing S) (baseRing S)) (ModuleCat.of (baseRing S) (baseRing S)) z w z₀'
  have k1 := k0 hz₀' z₀
  exact (shiftCycles_paste _ _ _ _ _ _ _ _ _).trans
    (congrArg ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ ·) (k1 hz₀))

/-- The right hand side of `totalCupPairing_shift₁_globalCycleClass`, as one global cocycle
class. -/
theorem totalCupPairing_shift₁_rhs (t i j : ℤ) (z : ModuleCat.of (baseRing S) (baseRing S) ⟶
    (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR K t)).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶
        (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).cycles j)
    (z₀ : (((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).cycles
        (i + t))).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles ((i + t) + j)))
    (hz₀ : (z₀ ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ K) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles ((i + t) + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K).iCycles (i + t))
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
              (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
              (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
              S.sheaf ⊤)) (ComplexShape.up ℤ) (i + t) j
            ((i + t) + j) rfl)) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((globalCycleClass z ≫ (shiftCohomologyIsoR K t i (i + t) (by omega)).hom) ⊗ₘ
          globalCycleClass w) ≫ totalCupPairing K M (i + t) j =
      globalCycleClass ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ (shiftCycles
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K) (i + t) (by omega)
          (z ≫ HomologicalComplex.cyclesMap
              ((((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso t).hom.app K) i)) w ≫ z₀ ≫
          HomologicalComplex.cyclesMap
            (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ K M) ((i + t) + j)) := by
  have eR' := globalCycleClass_shiftCohomologyIsoR' K t i (i + t) (by omega) z
  have eR := totalCupPairing_globalCycleClass_naive K M (shiftCycles
      (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K) (i + t) (by omega)
          (z ≫ HomologicalComplex.cyclesMap
              ((((SheafOfModules.evaluation
              (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso t).hom.app K) i)) w z₀ hz₀
  exact (congrArg (fun x => (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
      (x ⊗ₘ globalCycleClass w) ≫
      totalCupPairing K M (i + t) j) eR').trans eR

/-- **The cup product and the shift of the first factor, on classes of global cocycles.** For
global cocycles `z ∈ Zⁱ(Γ(S, 𝒦^•[t]))` and `w ∈ Zʲ(Γ(S, ℳ^•))`, the cup product of their classes,
carried to `Hⁱ⁺ᵗ⁺ʲ(S, Tot(𝒦^• ⊗ ℳ^•))` by `mapBifunctorShift₁Iso` and the shift identification,
is the cup product of the class of `z` moved to `Hⁱ⁺ᵗ(S, 𝒦^•)` with the class of `w`. There is no
sign. -/
theorem totalCupPairing_shift₁_globalCycleClass (t i j : ℤ) (z : ModuleCat.of (baseRing S)
    (baseRing S) ⟶ (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ (shiftR K t)).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶
        (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M).cycles j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ globalCycleClass w) ≫ totalCupPairing (shiftR K t) M i j ≫
        (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map (DerivedCategory.Q.map
            (CochainComplex.mapBifunctorShift₁Iso K M (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
            (ComplexShape.up ℤ)) t (i + j) ((i + t) + j) (by omega)).hom =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((globalCycleClass z ≫ (shiftCohomologyIsoR K t i (i + t) (by omega)).hom) ⊗ₘ
          globalCycleClass w) ≫ totalCupPairing K M (i + t) j := by
  obtain ⟨z₀', hz₀'⟩ := exists_tensorCycles_naive (shiftR K t) M i j
  obtain ⟨z₀, hz₀⟩ := exists_tensorCycles_naive K M (i + t) j
  exact (totalCupPairing_shift₁_lhs K M t i j z w z₀' hz₀').trans
    ((congrArg globalCycleClass (totalCupPairing_shift₁_cocycle K M t i j z
        w z₀' hz₀' z₀ hz₀)).trans
      (totalCupPairing_shift₁_rhs K M t i j z w z₀ hz₀).symm)

/-- `totalCupPairing_shift₁` on bounded below complexes of flasque modules. -/
theorem totalCupPairing_shift₁_of_isFlasque (hK : ∃ n : ℤ, K.IsStrictlyGE n)
    (hM : ∃ n : ℤ, M.IsStrictlyGE n)
    (hKfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (K.X n)))
    (hMfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (M.X n)))
    (t i j : ℤ) (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj (shiftR K t)) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj M) j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫ totalCupPairing (shiftR K t) M i
        j ≫ (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
        (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₁Iso K M
        (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
            (ComplexShape.up ℤ)) t (i + j) ((i + t) + j) (by omega)).hom =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
          ((ξ ≫ (shiftCohomologyIsoR K t i (i + t) (by omega)).hom) ⊗ₘ η) ≫
        totalCupPairing K M (i + t) j := by
  obtain ⟨z, rfl⟩ := exists_globalCycleClass_eq_of_isFlasque (shiftR K t) (isStrictlyGE_shift hK t)
    (isFlasque_shift hKfl t) i ξ
  obtain ⟨w, rfl⟩ := exists_globalCycleClass_eq_of_isFlasque M hM hMfl j η
  exact totalCupPairing_shift₁_globalCycleClass K M t i j z w

/-- **Transport of the left hand side of the shift of the first factor along chain maps.** -/
theorem totalCupPairing_shift₁_transport_lhs {K₁ M₁ : (CochainComplex (SheafOfModules.{u}
    (ringSheaf.{u, u, u} S.sheaf)) ℤ)} (a : K ⟶ K₁) (b : M ⟶ M₁)
    (t i j : ℤ) (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj (shiftR K t)) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj M) j) :
    ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫ totalCupPairing (shiftR K t) M i
        j ≫ (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
        (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₁Iso K M
        (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
            (ComplexShape.up ℤ)) t (i + j) ((i + t) + j) (by omega)).hom) ≫
        (DerivedCategory.homologyFunctor _ ((i + t) + j)).map ((baseSections S).map
            (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
            (sheafTensor S.sheaf) (ComplexShape.up ℤ)))) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
          ((ξ ≫ (DerivedCategory.homologyFunctor _ i).map ((baseSections S).map
          (DerivedCategory.Q.map ((CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u}
          (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map a)))) ⊗ₘ
          (η ≫ (DerivedCategory.homologyFunctor _ j).map ((baseSections S).map
          (DerivedCategory.Q.map b)))) ≫
        totalCupPairing (shiftR K₁ t) M₁ i j ≫ (DerivedCategory.homologyFunctor _ (i + j)).map
            ((baseSections S).map (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₁Iso K₁ M₁
            (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K₁ M₁ (sheafTensor S.sheaf)
            (ComplexShape.up ℤ)) t (i + j) ((i + t) + j) (by omega)).hom := by
  have e1 := shiftCohomologyIsoR_naturality (HomologicalComplex.mapBifunctorMap a b
      (sheafTensor S.sheaf) (ComplexShape.up ℤ)) t (i + j) ((i + t) + j) (by omega)
  have e2 := homology_map_mapBifunctorShift₁Iso_naturality K M a b t (i + j)
  have e3 := totalCupPairing_naturality' ((CategoryTheory.shiftFunctor (CochainComplex
      (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map a) b i j ξ η
  exact paste_transport _ _ _ _ _ _ _ _ _ _ _ _ e1 e2 e3

/-- **Transport of the right hand side of the shift of the first factor along chain maps.** -/
theorem totalCupPairing_shift₁_transport_rhs {K₁ M₁ : (CochainComplex (SheafOfModules.{u}
    (ringSheaf.{u, u, u} S.sheaf)) ℤ)} (a : K ⟶ K₁) (b : M ⟶ M₁)
    (t i j : ℤ) (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj (shiftR K t)) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj M) j) :
    ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((ξ ≫ (shiftCohomologyIsoR K t i (i + t) (by omega)).hom) ⊗ₘ η) ≫
        totalCupPairing K M (i + t) j) ≫ (DerivedCategory.homologyFunctor _ ((i + t) + j)).map
            ((baseSections S).map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
            (sheafTensor S.sheaf) (ComplexShape.up ℤ)))) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
          (((ξ ≫ (DerivedCategory.homologyFunctor _ i).map ((baseSections S).map
          (DerivedCategory.Q.map ((CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u}
          (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map a)))) ≫ (shiftCohomologyIsoR K₁ t i
          (i + t) (by omega)).hom) ⊗ₘ
        (η ≫ (DerivedCategory.homologyFunctor _ j).map ((baseSections S).map
            (DerivedCategory.Q.map b)))) ≫ totalCupPairing K₁ M₁ (i + t) j := by
  have e := totalCupPairing_naturality' a b (i + t) j
    (ξ ≫ (shiftCohomologyIsoR K t i (i + t) (by omega)).hom) η
  have hσ : (ξ ≫ (shiftCohomologyIsoR K t i (i + t) (by omega)).hom) ≫
      (DerivedCategory.homologyFunctor _ (i + t)).map ((baseSections S).map
      (DerivedCategory.Q.map a)) =
      (ξ ≫ (DerivedCategory.homologyFunctor _ i).map ((baseSections S).map (DerivedCategory.Q.map
          ((CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u}
          (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map a)))) ≫ (shiftCohomologyIsoR K₁ t i
          (i + t) (by omega)).hom :=
    (Category.assoc _ _ _).trans ((congrArg (ξ ≫ ·)
      (shiftCohomologyIsoR_naturality a t i (i + t) (by omega)).symm).trans
          (Category.assoc _ _ _).symm)
  exact ((Category.assoc _ _ _).trans (congrArg ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
      ·) (Category.assoc _ _ _))).trans
    (e.trans (congrArg (fun y => (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (y ⊗ₘ (η ≫ (DerivedCategory.homologyFunctor _ j).map ((baseSections S).map
        (DerivedCategory.Q.map b)))) ≫
      totalCupPairing K₁ M₁ (i + t) j) hσ))

/-- **The cup product and the shift of the first factor.** For bounded below complexes `𝒦^•`,
`ℳ^•` of `𝒪_S`-modules and classes `ξ ∈ Hⁱ(S, 𝒦^•[t])`, `η ∈ Hʲ(S, ℳ^•)`, the cup product of `ξ`
and `η`, carried to `Hⁱ⁺ᵗ⁺ʲ(S, Tot(𝒦^• ⊗ ℳ^•))` by `mapBifunctorShift₁Iso` and the shift
identification, is the cup product of `ξ` moved to `Hⁱ⁺ᵗ(S, 𝒦^•)` with `η`. There is no sign. -/
theorem totalCupPairing_shift₁ (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hM : ∃ n : ℤ, M.IsStrictlyGE n)
    (t i j : ℤ) (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule
        (DerivedCategory.Q.obj (shiftR K t)) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj M) j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫ totalCupPairing (shiftR K t) M i
        j ≫ (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
        (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₁Iso K M
        (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
            (ComplexShape.up ℤ)) t (i + j) ((i + t) + j) (by omega)).hom =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
          ((ξ ≫ (shiftCohomologyIsoR K t i (i + t) (by omega)).hom) ⊗ₘ η) ≫
        totalCupPairing K M (i + t) j := by
  obtain ⟨K₁, M₁, a, b, -, -, hK₁, hM₁, hKfl, hMfl, hab⟩ :=
    Stacks.Cohomology.FlasqueReduction.exists_flasqueResolution_quasiIso_tensor S K M hK hM
  have h1 : IsIso (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
      (sheafTensor S.sheaf) (ComplexShape.up ℤ))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := (HomologicalComplex.mapBifunctorMap a b
        (sheafTensor S.sheaf) (ComplexShape.up ℤ)))).2 hab
  have h3 : IsIso ((DerivedCategory.homologyFunctor _ ((i + t) + j)).map
      ((baseSections S).map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
          (sheafTensor S.sheaf) (ComplexShape.up ℤ))))) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ h1)
  refine (cancel_mono ((DerivedCategory.homologyFunctor _ ((i + t) + j)).map
      ((baseSections S).map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
          (sheafTensor S.sheaf) (ComplexShape.up ℤ)))))).1 ?_
  have eL := totalCupPairing_shift₁_transport_lhs K M a b t i j ξ η
  have eR := totalCupPairing_shift₁_transport_rhs K M a b t i j ξ η
  exact eL.trans ((totalCupPairing_shift₁_of_isFlasque K₁ M₁ hK₁ hM₁ hKfl hMfl t i j _ _).trans
    eR.symm)

end ShiftTwo

end Stacks.Cohomology.DerivedGlobalCupProduct

end
