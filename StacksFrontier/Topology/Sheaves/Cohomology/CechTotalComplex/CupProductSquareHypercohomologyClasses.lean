module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquareHypercohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The global cup product and the Čech cup product on all hypercohomology classes

Let `(S, 𝒪_S)` be a ringed space and `K`, `M` bounded below complexes of `𝒪_S`-modules for which
Čech cohomology computes hypercohomology. Under the identification `θ` of the hypercohomology of
Section 01FP with the cohomology of derived global sections of Section 0FKU
(`Stacks.Cech.CupProductSquare.hypercohomologyToCohomologyModule`), the cup product of
Section 0FKU followed by the canonical map `𝒦^• ⊗^𝐋 ℳ^• ⟶ Tot(𝒦^• ⊗ ℳ^•)` is the Čech cup
product of Section 01FP at the sheaf-tensor coefficient pairing, on every pair of classes. This
is [Stacks, Tag 0FKV] read on cohomology: any two classes are represented by Čech cocycles of a
common covering, where
`Stacks.Cech.CupProductSquare.cupPairing_hypercohomologyToCohomologyModule_cycles` applies.

## Main results

* `Stacks.Cech.CupProductSquare.cupPairing_hypercohomologyToCohomologyModule`: **the two cup
  products agree.**

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cech.Hypercohomology

universe u

namespace Stacks.Cech.CupProductSquare

open scoped Stacks.StandardDerivedModel
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable (S : RingedSpace.{u, u})
  (K M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))

/-- Every class of the Čech cohomology of a covering is the class of a cycle of the total Čech
complex over `Γ(S, 𝒪_S)`. -/
theorem exists_homologyπ_totalCechBase {I : Type u} (Ui : I → Opens S.carrier)
    (hU : (⊤ : Opens S.carrier) = ⨆ i, Ui i) (n : ℤ)
    (x : ((cech S.sheaf Ui hU).obj K.obj).homology n) :
    ∃ z : (totalCechBase S Ui hU K).cycles n, (totalCechBase S Ui hU K).homologyπ n z = x :=
  (ModuleCat.epi_iff_surjective ((totalCechBase S Ui hU K).homologyπ n)).1 inferInstance x

/-- The tensoring of cycles of two total Čech complexes over `Γ(S, 𝒪_S)`. -/
theorem exists_tensorCycles_totalCechBase {I : Type u} (Ui : I → Opens S.carrier)
    (hU : (⊤ : Opens S.carrier) = ⨆ i, Ui i) (i j : ℤ) :
    ∃ z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j),
      z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
        ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
          HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
            (i + j) rfl :=
  RingTheory.TorProducts.exists_tensorCycles (R := baseRing S) _ _ i j

/-- The two cup products agree on the classes of two cycles of the total Čech complexes of a
common covering. -/
theorem cupPairing_hypercohomologyToCohomologyModule_homologyπ (hK : CechComputes S.sheaf K)
    (hM : CechComputes S.sheaf M) {J : Type u} (W : J → Opens S.carrier)
    (hW : (⊤ : Opens S.carrier) = ⨆ j, W j) {i j : ℤ} (zc : (totalCechBase S W hW K).cycles i)
    (wc : (totalCechBase S W hW M).cycles j) :
    (Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing K.1 M.1 i j).hom
      (hypercohomologyToCohomologyModule S K i (cechClass S.sheaf W hW K i
          ((totalCechBase S W hW K).homologyπ i zc)) ⊗ₜ
        hypercohomologyToCohomologyModule S M j (cechClass S.sheaf W hW M j
          ((totalCechBase S W hW M).homologyπ j wc))) =
      hypercohomologyToCohomologyModule S (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j)
        (cup S.sheaf hK hM (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2) i j (i + j) rfl
        (cechClass S.sheaf W hW K i ((totalCechBase S W hW K).homologyπ i zc))
        (cechClass S.sheaf W hW M j ((totalCechBase S W hW M).homologyπ j wc))) := by
  obtain ⟨z₀, hz₀⟩ := exists_tensorCycles_totalCechBase S K M W hW i j
  exact cupPairing_hypercohomologyToCohomologyModule_cycles S W hW K M hK hM zc wc z₀ hz₀

/-- The two cup products agree on classes of the Čech cohomology of a common covering. -/
theorem cupPairing_hypercohomologyToCohomologyModule_cechClass_homology
    (hK : CechComputes S.sheaf K) (hM : CechComputes S.sheaf M) {J : Type u}
    (W : J → Opens S.carrier) (hW : (⊤ : Opens S.carrier) = ⨆ j, W j) (i j : ℤ)
    (x : ((cech S.sheaf W hW).obj K.obj).homology i)
    (y : ((cech S.sheaf W hW).obj M.obj).homology j) :
    (Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing K.1 M.1 i j).hom
      (hypercohomologyToCohomologyModule S K i (cechClass S.sheaf W hW K i x) ⊗ₜ
        hypercohomologyToCohomologyModule S M j (cechClass S.sheaf W hW M j y)) =
      hypercohomologyToCohomologyModule S (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j)
        (cup S.sheaf hK hM (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2) i j (i + j) rfl
          (cechClass S.sheaf W hW K i x) (cechClass S.sheaf W hW M j y)) := by
  obtain ⟨zc, rfl⟩ := exists_homologyπ_totalCechBase S K W hW i x
  obtain ⟨wc, rfl⟩ := exists_homologyπ_totalCechBase S M W hW j y
  exact cupPairing_hypercohomologyToCohomologyModule_homologyπ S K M hK hM W hW zc wc

/-- **The cup product of Section 0FKU, followed by the canonical map to the total tensor complex,
is the Čech cup product of Section 01FP at the sheaf-tensor coefficients** ([Stacks, Tag 0FKV] on
cohomology classes): for bounded below complexes `K`, `M` whose hypercohomology Čech cohomology
computes, under the identification `θ` of the two models of hypercohomology. -/
theorem cupPairing_hypercohomologyToCohomologyModule (hK : CechComputes S.sheaf K)
    (hM : CechComputes S.sheaf M) (i j : ℤ) (a : hypercohomology S.sheaf K i)
    (b : hypercohomology S.sheaf M j) :
    (Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing K.1 M.1 i j).hom
      (hypercohomologyToCohomologyModule S K i a ⊗ₜ hypercohomologyToCohomologyModule S M j b) =
      hypercohomologyToCohomologyModule S (tensorPlusOf S.sheaf K M (tensorPlus S K M).2) (i + j)
        (cup S.sheaf hK hM (sheafTensorPairingOf S.sheaf K M (tensorPlus S K M).2) i j (i + j) rfl
          a b) := by
  obtain ⟨J, W, hW, x, -, y, rfl, -, rfl⟩ := exists_common_cechClass S.sheaf hK hM i j a a b
  exact cupPairing_hypercohomologyToCohomologyModule_cechClass_homology S K M hK hM W hW i j x y

/-- **The identification `θ` of the two models of hypercohomology is natural** in morphisms of
bounded below complexes. -/
theorem hypercohomologyToCohomologyModule_hypercohomologyMap {K L : CochainComplex.Plus
      (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))} (φ : K ⟶ L) (n : ℤ)
    (a : hypercohomology S.sheaf K n) :
    hypercohomologyToCohomologyModule S L n (hypercohomologyMap S.sheaf φ n a) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections S).map (DerivedCategory.Q.map φ.hom))).hom
        (hypercohomologyToCohomologyModule S K n a) := by
  have h := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
    (NatTrans.naturality
      (Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections S).hom φ)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h a

end Stacks.Cech.CupProductSquare

end
