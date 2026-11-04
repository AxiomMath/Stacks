module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquareSections
public import StacksFrontier.Homology.Tor.ProductOfCycleClasses

/-!
# The global cup product on classes of global cocycles

Let `(S, 𝒪_S)` be a ringed space, `A = Γ(S, 𝒪_S)`, and let `𝒦^•`, `ℳ^•` be complexes of
`𝒪_S`-modules.  A global cocycle `z ∈ Zⁱ(Γ(S, 𝒦^•))` has a class `[z] ∈ Hⁱ(S, 𝒦^•)`, the image
of its class in `Hⁱ(Γ(S, 𝒦^•))` under the unit `Γ ⟶ RΓ`.  This file proves that the cup product
of Cohomology, Section 0FKU, followed by `RΓ` of the canonical map
`𝒦^• ⊗^𝐋 ℳ^• ⟶ Tot(𝒦^• ⊗ ℳ^•)`, sends `[z] ⊗ [w]` to the class of the global cocycle
`z ⊗ w ∈ Zⁱ⁺ʲ(Γ(S, Tot(𝒦^• ⊗ ℳ^•)))`, the naive cup product of the two sections.

This is the commutative diagram displayed before [Stacks, Tag 0FKV] (Tag 0FP3 for the morphism
to the point), `Stacks.Cech.CupProductSquare.globalCupProduct_naiveCupProduct`, read on
cohomology classes: the tensoring of classes of Tag 068H, followed by the canonical map to the
total tensor complex, is the class of the tensor product of cocycles
(`RingTheory.TorProducts.cycleClass_tensor_toTensor`), and the tensoring is natural along the
units (`RingTheory.TorProducts.tensor_cycleClass_naturality`).

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.sectionsComplex`: the complex `Γ(S, 𝒦^•)`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.globalCycleClass`: the class in `Hⁱ(S, 𝒦^•)` of a
  global cocycle.
* `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing`: the cup product followed by `RΓ` of
  the canonical map to the total tensor complex.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_globalCycleClass`: **the cup product
  of the classes of two global cocycles is the class of their naive cup product.**

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.GlobalKunneth
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans totalComplexPair)
open CochainComplex.DerivedTensor CochainComplex.DerivedTensor.ToTotal
open RingTheory.TorProducts (cycleClass)
open Stacks.Cohomology.DerivedSectionsLeray (sectionsUnitQ sectionsUnitQ_naturality)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

variable (S : RingedSpace.{u, u})

/-- **The global cup product of Cohomology, Section 0FKU** used below: the relative cup product of
Tag 0B68 for the morphism from `S` to the point `({*}, Γ(S, 𝒪_S))`, built from the canonical
one-point comparison. It is the global cup product for which Tag 0FKV and the diagram before it
are proved. -/
abbrev cupProductOnSpace : GlobalCupProduct S :=
  globalCupProduct (canonicalOnePointComparison S)

/-- The complex of global sections `Γ(S, 𝒦^•)` of a complex of `𝒪_S`-modules. -/
abbrev sectionsComplex (K : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ) :
    CochainComplex (ModuleCat.{u} (baseRing S)) ℤ :=
  ((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

variable {S}

/-- **The class in `Hⁱ(S, 𝒦^•)` of a family of global cocycles** `z : M ⟶ Zⁱ(Γ(S, 𝒦^•))`: its
class in `Hⁱ(Γ(S, 𝒦^•))` followed by the unit `Γ ⟶ RΓ`. -/
def globalCycleClass {M : ModuleCat.{u} (baseRing S)}
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ} {i : ℤ}
    (z : M ⟶ (sectionsComplex S K).cycles i) :
    M ⟶ cohomologyModule (DerivedCategory.Q.obj K) i :=
  cycleClass z ≫ (DerivedCategory.homologyFunctor _ i).map (sectionsUnitQ S ⊤ K)

/-- Precomposing a family of global cocycles precomposes its class. -/
theorem comp_globalCycleClass {M N : ModuleCat.{u} (baseRing S)}
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ} {i : ℤ}
    (a : N ⟶ M) (z : M ⟶ (sectionsComplex S K).cycles i) :
    a ≫ globalCycleClass z = globalCycleClass (a ≫ z) := by
  rw [globalCycleClass, globalCycleClass, ← Category.assoc, RingTheory.TorProducts.comp_cycleClass]

/-- The class of a family of global cocycles is natural along chain maps. -/
theorem globalCycleClass_map {M : ModuleCat.{u} (baseRing S)}
    {K K' : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ} {i : ℤ}
    (z : M ⟶ (sectionsComplex S K).cycles i) (f : K ⟶ K') :
    globalCycleClass z ≫ (DerivedCategory.homologyFunctor _ i).map
        ((baseSections S).map (DerivedCategory.Q.map f)) =
      globalCycleClass (z ≫ HomologicalComplex.cyclesMap
        (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).map f) i) := by
  rw [globalCycleClass, globalCycleClass, Category.assoc, ← Functor.map_comp]
  refine (congrArg (fun t => cycleClass z ≫ (DerivedCategory.homologyFunctor _ i).map t)
    (sectionsUnitQ_naturality S ⊤ f).symm).trans ?_
  rw [Functor.map_comp, ← Category.assoc, RingTheory.TorProducts.cycleClass_comp_map]

/-- **The cup product followed by `RΓ` of the canonical map to the total tensor complex**,

`Hⁱ(S, 𝒦^•) ⊗_A Hʲ(S, ℳ^•) ⟶ Hⁱ⁺ʲ(S, 𝒦^• ⊗^𝐋 ℳ^•) ⟶ Hⁱ⁺ʲ(S, Tot(𝒦^• ⊗ ℳ^•))`. -/
def totalCupPairing (K M : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ)
    (i j : ℤ) :
    cohomologyModule (DerivedCategory.Q.obj K) i ⊗ cohomologyModule (DerivedCategory.Q.obj M) j ⟶
      cohomologyModule (DerivedCategory.Q.obj ((totalComplexPair (sheafTensor S.sheaf)).obj (K, M)))
        (i + j) :=
  cupPairing (cupProductOnSpace S) (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) i j ≫
    (DerivedCategory.homologyFunctor _ (i + j)).map
      ((baseSections S).map ((derivedToTensorNatTrans S).app (K, M)))

/-- **The cup product of the classes of two global cocycles is the class of their naive cup
product.** For global cocycles `z ∈ Zⁱ(Γ(S, 𝒦^•))` and `w ∈ Zʲ(Γ(S, ℳ^•))`, and `z₀` the
tensoring of cocycles `Zⁱ(Γ 𝒦^•) ⊗ Zʲ(Γ ℳ^•) ⟶ Zⁱ⁺ʲ(Tot(Γ 𝒦^• ⊗ Γ ℳ^•))`, the class of
`z ⊗ w` under `totalCupPairing` is the class of the image of `z ⊗ w` under the naive cup product
`Tot(Γ(S, 𝒦^•) ⊗_A Γ(S, ℳ^•)) ⟶ Γ(S, Tot(𝒦^• ⊗ ℳ^•))`. -/
theorem totalCupPairing_globalCycleClass
    {K M : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ} {i j : ℤ}
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S M).cycles j)
    (z₀ : (sectionsComplex S K).cycles i ⊗ (sectionsComplex S M).cycles j ⟶
      (sectionsComplex S K ⊗ sectionsComplex S M).cycles (i + j))
    (hz₀ : z₀ ≫ (sectionsComplex S K ⊗ sectionsComplex S M).iCycles (i + j) =
      ((sectionsComplex S K).iCycles i ⊗ₘ (sectionsComplex S M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (sectionsComplex S K) (sectionsComplex S M) i j (i + j)
          rfl) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ globalCycleClass w) ≫ totalCupPairing K M i j =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫
        cycleClass z₀ ≫ (DerivedCategory.homologyFunctor _ (i + j)).map
          (DerivedCategory.Q.map
              (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ K M) ≫
            sectionsUnitQ S ⊤ ((totalComplexPair (sheafTensor S.sheaf)).obj (K, M))) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)
  have hsq := congrArg H.map (Stacks.Cech.CupProductSquare.globalCupProduct_naiveCupProduct S K M)
  simp only [H.map_comp] at hsq
  have h2 := RingTheory.TorProducts.cycleClass_tensor_toTensor z w z₀ hz₀
  have e1 : (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ globalCycleClass w) ≫ totalCupPairing K M i j =
      ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (cycleClass z ⊗ₘ cycleClass w) ≫
        (RingTheory.TorProducts.cohomologyTensorProduct
          (DerivedCategory.Q.obj (sectionsComplex S K))
          (DerivedCategory.Q.obj (sectionsComplex S M)) i j).map) ≫
        H.map ((Functor.uncurry.obj (tensorBase S)).map
          (sectionsUnitQ S ⊤ K ×ₘ sectionsUnitQ S ⊤ M)) ≫
        H.map ((cupProductOnSpace S).app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj M)) ≫
        H.map ((baseSections S).map ((derivedToTensorNatTrans S).app (K, M))) := by
    have h1' := RingTheory.TorProducts.tensor_cycleClass_naturality z w (sectionsUnitQ S ⊤ K)
      (sectionsUnitQ S ⊤ M) =≫ (H.map ((cupProductOnSpace S).app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj M)) ≫
          H.map ((baseSections S).map ((derivedToTensorNatTrans S).app (K, M))))
    simp only [Category.assoc] at h1' ⊢
    exact h1'
  refine e1.trans ?_
  rw [hsq]
  exact (congrArg (_ ≫ ·) (H.map_comp _ _)).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (Category.assoc _ _ _)).trans h2))).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))))

end Stacks.Cohomology.DerivedGlobalCupProduct

end
