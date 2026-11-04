module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquareCommutes
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductCocycles
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The global cup product on classes of Čech cocycles

Let `(S, 𝒪_S)` be a ringed space, `A = Γ(S, 𝒪_S)`, `𝒦^•` and `ℳ^•` bounded below complexes of
`𝒪_S`-modules and `𝒰` an open covering of `S`. A cocycle `z` of the total Čech complex
`Tot(Č(𝒰, 𝒦^•))` has a class in `Hⁱ(S, 𝒦^•)`, its image under the comparison
`Tot(Č(𝒰, 𝒦^•)) ⟶ RΓ(S, 𝒦^•)` of [Stacks, Tag 08BN]. This file proves that the cup product of
Cohomology, Section 0FKU, followed by `RΓ` of the canonical map
`𝒦^• ⊗^𝐋 ℳ^• ⟶ Tot(𝒦^• ⊗ ℳ^•)`, sends the classes of two Čech cocycles `z` and `w` to the class
of their Čech cup product of [Stacks, Tag 07MB].

This is the commutative square of [Stacks, Tag 0FKV]
(`Stacks.Cech.CupProductSquare.cupProductSquareCommutes`) read on cohomology classes, exactly as
`Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_globalCycleClass` reads the diagram
before Tag 0FKV on classes of global cocycles.

## Main results

* `Stacks.Cech.CupProductSquare.cupPairing_cechCycleClass`: **the cup product of the classes of
  two Čech cocycles is the class of their Čech cup product.**

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.DerivedGlobalCupProduct (cupProductOnSpace cupPairing)
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections tensorBase)
open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans)
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cech.ModuleCupProduct (CoeffRing totalCechComplexFunctorA)
open CochainComplex.DerivedTensor.ToTotal (canonicalDerivedToTensorNatTrans)
open RingTheory.TorProducts (cycleClass)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cech.CupProductSquare

open scoped Stacks.StandardDerivedModel

/-- The first half of the pasting in the proof of `cupPairing_cechCycleClass`, stated with every
object and morphism a variable, so that it applies by unification at default transparency: the
spellings `CoeffRing 𝒪_S ⊤` and `Γ(S, 𝒪_S)` of the ring of sections, and
`Stacks.SheafOfModules.Tensor.ringSheaf 𝒪_S` and `structureSheafRing S` of the structure sheaf,
agree only there. The last two arrows of the target are one variable `qr`, so that the object
between them is never unified afresh. -/
private theorem paste_left {C : Type*} [Category* C] {a b c d e f c' d' g : C}
    (l : a ⟶ b) (X : b ⟶ c) (T : c ⟶ d) (κ : d ⟶ e) (B : e ⟶ f) (X' : b ⟶ c') (T' : c' ⟶ d')
    (N : d' ⟶ d) (t : d' ⟶ g) (qr : g ⟶ f)
    (h₁ : l ≫ X ≫ T = l ≫ X' ≫ T' ≫ N) (hsq : t ≫ qr = N ≫ κ ≫ B) :
    l ≫ X ≫ (T ≫ κ) ≫ B = l ≫ X' ≫ T' ≫ t ≫ qr := by
  rw [hsq, Category.assoc, reassoc_of% h₁]

/-- The second half of the pasting in the proof of `cupPairing_cechCycleClass`. -/
private theorem paste_right {C : Type*} [Category* C] {a b c' d' g h f : C}
    (l : a ⟶ b) (X' : b ⟶ c') (T' : c' ⟶ d') (t : d' ⟶ g) (qr : g ⟶ f)
    (zw : b ⟶ h) (cz : h ⟶ g) (h₂ : l ≫ X' ≫ T' ≫ t = l ≫ zw ≫ cz) :
    l ≫ X' ≫ T' ≫ t ≫ qr = l ≫ zw ≫ cz ≫ qr := by
  rw [reassoc_of% h₂]

/-- A functor applied to an equation `(a ≫ b) ≫ c = d ≫ e ≫ f`, stated with every object and
morphism a variable. -/
private theorem map_comp_three {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {x y z w y' z' : C} (a : x ⟶ y) (b : y ⟶ z) (c : z ⟶ w) (d : x ⟶ y') (e : y' ⟶ z')
    (f : z' ⟶ w) (h : (a ≫ b) ≫ c = d ≫ e ≫ f) :
    F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e ≫ F.map f := by
  simpa only [Functor.map_comp, Category.assoc] using congrArg F.map h

variable (S : RingedSpace.{u, u}) {I : Type u} (Ui : I → Opens S.carrier)
  (hU : (⊤ : Opens S.carrier) = ⨆ i, Ui i)
  (K M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))

/-- The total Čech complex `Tot(Č(𝒰, 𝒦^•))`, read as a complex of modules over `Γ(S, 𝒪_S)`: the
spelling of the ring in which the cup product of Section 0FKU is stated. -/
abbrev totalCechBase : CochainComplex (ModuleCat.{u} (baseRing S)) ℤ :=
  (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj K.1

/-- **The cup product of the classes of two Čech cocycles is the class of their Čech cup
product.** For cocycles `z ∈ Zⁱ(Tot(Č(𝒰, 𝒦^•)))` and `w ∈ Zʲ(Tot(Č(𝒰, ℳ^•)))`, and `z₀` the
tensoring of cocycles `Zⁱ ⊗ Zʲ ⟶ Zⁱ⁺ʲ(Tot(Tot Č(𝒰, 𝒦^•) ⊗_A Tot Č(𝒰, ℳ^•)))`, the cup product
of Section 0FKU of the classes of `z` and `w`, followed by `RΓ` of the canonical map to
`Tot(𝒦^• ⊗ ℳ^•)`, is the class of `z ⊗ w` pushed along the Čech cup product. -/
theorem cupPairing_cechCycleClass {i j : ℤ}
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (totalCechBase S Ui hU K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (totalCechBase S Ui hU M).cycles j)
    (z₀ : (totalCechBase S Ui hU K).cycles i ⊗ (totalCechBase S Ui hU M).cycles j ⟶
      (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (totalCechBase S Ui hU K ⊗ totalCechBase S Ui hU M).iCycles (i + j) =
      ((totalCechBase S Ui hU K).iCycles i ⊗ₘ (totalCechBase S Ui hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (totalCechBase S Ui hU K) (totalCechBase S Ui hU M) i j
          (i + j) rfl) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((cycleClass z ≫ (DerivedCategory.homologyFunctor _ i).map
            ((cechToBaseSections S Ui hU).app K)) ⊗ₘ
          (cycleClass w ≫ (DerivedCategory.homologyFunctor _ j).map
            ((cechToBaseSections S Ui hU).app M))) ≫
        cupPairing (cupProductOnSpace S) (DerivedCategory.Q.obj K.1) (DerivedCategory.Q.obj M.1)
          i j ≫
        (DerivedCategory.homologyFunctor _ (i + j)).map
          ((baseSections S).map ((derivedToTensorNatTrans S).app (K.1, M.1))) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫
        cycleClass z₀ ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
          ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
            (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj (tensorPlus S K M).1)
            (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
          ((cechToBaseSections S Ui hU).app (tensorPlus S K M)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)
  have hsq := map_comp_three H _ _ _ _ _ _ (cupProductSquareCommutes S Ui hU (K := K) (M := M))
  let cK : DerivedCategory.Q.obj ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj K.1) ⟶
      (baseSections S).obj (DerivedCategory.Q.obj K.1) := (cechToBaseSections S Ui hU).app K
  let cM : DerivedCategory.Q.obj ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj M.1) ⟶
      (baseSections S).obj (DerivedCategory.Q.obj M.1) := (cechToBaseSections S Ui hU).app M
  have h1 := RingTheory.TorProducts.tensor_cycleClass_naturality (R := baseRing S) z w cK cM
  have h2 := RingTheory.TorProducts.cycleClass_tensor_toTensor (R := baseRing S) z w z₀ hz₀
  have hsq' : H.map ((canonicalDerivedToTensorNatTrans (baseRing S)).app
        (totalCechBase S Ui hU K, totalCechBase S Ui hU M)) ≫
      H.map ((DerivedCategory.Q (C := ModuleCat.{u} (CoeffRing S.sheaf ⊤))).map
        (Y := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj (tensorPlus S K M).1)
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU)) ≫
      H.map ((cechToBaseSections S Ui hU).app (tensorPlus S K M)) =
      H.map ((Functor.uncurry.obj (tensorBase S)).map (cK ×ₘ cM)) ≫
      H.map ((cupProductOnSpace S).app (DerivedCategory.Q.obj K.1, DerivedCategory.Q.obj M.1)) ≫
      H.map ((baseSections S).map ((derivedToTensorNatTrans S).app (K.1, M.1))) := hsq
  have h2' : (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (cycleClass z ⊗ₘ cycleClass w) ≫
      (RingTheory.TorProducts.cohomologyTensorProduct
        (DerivedCategory.Q.obj (totalCechBase S Ui hU K))
        (DerivedCategory.Q.obj (totalCechBase S Ui hU M)) i j).map ≫
      H.map ((canonicalDerivedToTensorNatTrans (baseRing S)).app
        (totalCechBase S Ui hU K, totalCechBase S Ui hU M)) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ cycleClass z₀ := h2
  have h1' : (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
      ((cycleClass z ≫ (DerivedCategory.homologyFunctor _ i).map cK) ⊗ₘ
        (cycleClass w ≫ (DerivedCategory.homologyFunctor _ j).map cM)) ≫
      (RingTheory.TorProducts.cohomologyTensorProduct ((baseSections S).obj
        (DerivedCategory.Q.obj K.1)) ((baseSections S).obj (DerivedCategory.Q.obj M.1)) i j).map =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (cycleClass z ⊗ₘ cycleClass w) ≫
      (RingTheory.TorProducts.cohomologyTensorProduct
        (DerivedCategory.Q.obj (totalCechBase S Ui hU K))
        (DerivedCategory.Q.obj (totalCechBase S Ui hU M)) i j).map ≫
      H.map ((Functor.uncurry.obj (tensorBase S)).map (cK ×ₘ cM)) := h1
  exact (paste_left _ _ _ _ _ _ _ _ _ _ h1' hsq').trans (paste_right _ _ _ _ _ _ _ h2')

end Stacks.Cech.CupProductSquare

end
