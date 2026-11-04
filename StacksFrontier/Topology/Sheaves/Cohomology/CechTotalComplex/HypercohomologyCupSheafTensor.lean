module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupElementwise
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.SheafTensorPairing

/-!
# The Čech cup product at the sheaf-tensor coefficients, on classes of cocycles

Let `𝒪_X` be a sheaf of commutative rings, `K`, `M` bounded below complexes of `𝒪_X`-modules and
`Tot(K ⊗_{𝒪_X} M)` their total tensor complex. The cup product of Cohomology, Section 01FP
(`Stacks.Cech.Hypercohomology.cup`) along the sheaf-tensor coefficient pairing
`Kᵃ ⊗ Mᵇ ⟶ Tot(K ⊗ M)^{a+b}` of the classes of two Čech cocycles `zK`, `zM` on a common covering
is the class of any Čech cocycle whose cochain is the Čech cup product of [Stacks, Tag 07MB] of
`zK ⊗ zM`. This is the elementwise form of the Čech cup product used to compare it with the
global cup product of Section 0FKU through [Stacks, Tag 0FKV].

## Main definitions

* `Stacks.Cech.Hypercohomology.tensorPlusOf`: `Tot(K ⊗ M)` as a bounded below complex.
* `Stacks.Cech.Hypercohomology.sheafTensorPairingOf`: the sheaf-tensor coefficient pairing as a
  pairing of bounded below complexes.

## Main results

* `Stacks.Cech.Hypercohomology.cup_sheafTensorPairingOf_cechClass`.

## References

* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cohomology.CechSheaf (coverObject SectionRing)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (K M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
  (hKM : CochainComplex.plus _ (HomologicalComplex.mapBifunctor K.1 M.1 (sheafTensor O) (up ℤ)))

/-- `Tot(K ⊗_{𝒪_X} M)` as a bounded below complex, given that it is bounded below. -/
abbrev tensorPlusOf : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)) :=
  ⟨HomologicalComplex.mapBifunctor K.1 M.1 (sheafTensor O) (up ℤ), hKM⟩

/-- The sheaf-tensor coefficient pairing `Kᵃ ⊗ Mᵇ ⟶ Tot(K ⊗ M)^{a+b}` as a pairing of bounded
below complexes. -/
abbrev sheafTensorPairingOf : Pairing O K M (tensorPlusOf O K M hKM) :=
  Stacks.Cech.SheafTensorPairing.sheafTensorComplexPairing O ⊤ K.1 M.1

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The class of a cycle of a total Čech complex, as a morphism out of the unit, is the class of
the cocycle underlying it. -/
theorem toMor_homologyπ_eq_cocycleClass {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ)
    (z : ((cech O U hU).obj L.obj).cycles n) :
    toMor (((cech O U hU).obj L.obj).homologyπ n z) =
      cocycleClass n (toMor (((cech O U hU).obj L.obj).iCycles n z)) (by
        rw [← toMor_comp, Category.assoc, HomologicalComplex.iCycles_d, Limits.comp_zero]) := by
  have h : ∀ hz, ((cech O U hU).obj L.obj).liftCycles
      (toMor (((cech O U hU).obj L.obj).iCycles n z)) (n + 1) (CochainComplex.next ℤ n) hz =
        toMor z := fun hz => by
    rw [← cancel_mono (((cech O U hU).obj L.obj).iCycles n), HomologicalComplex.liftCycles_i,
      toMor_comp]
  rw [cocycleClass, h, toMor_comp]

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The class of a cycle is the class of its underlying cocycle, on elements. -/
theorem homologyπ_eq_cocycleClass {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ)
    (z : ((cech O U hU).obj L.obj).cycles n) :
    ((cech O U hU).obj L.obj).homologyπ n z =
      cocycleClass n (toMor (((cech O U hU).obj L.obj).iCycles n z)) (by
        rw [← toMor_comp, Category.assoc, HomologicalComplex.iCycles_d, Limits.comp_zero])
        (1 : SectionRing (ringSheaf O) ⊤) := by
  rw [← toMor_homologyπ_eq_cocycleClass O U hU L n z, toMor_apply_one]

/-- **The Čech cup product at the sheaf-tensor coefficients of the classes of two Čech cocycles**
is the class of any cycle whose cochain is their Čech cup product of [Stacks, Tag 07MB]. -/
theorem cup_sheafTensorPairingOf_cechClass {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (hK : CechComputes O K) (hM : CechComputes O M) {p q : ℤ}
    (zK : ((cech O U hU).obj K.obj).cycles p) (zM : ((cech O U hU).obj M.obj).cycles q)
    (y : ((cech O U hU).obj (tensorPlusOf O K M hKM).obj).cycles (p + q))
    (hy : ((cech O U hU).obj (tensorPlusOf O K M hKM).obj).iCycles (p + q) y =
      (Stacks.CategoryTheory.CechComplex.ιTot (coverObject U hU)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj M.obj) p q (p + q) rfl ≫
        (Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject U hU) _
          (sheafTensorPairingOf O K M hKM)).f (p + q)).hom
        (Stacks.CategoryTheory.CechComplex.tmulHom
          (show ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU) _).obj
            ((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj)).X p from
              ((cech O U hU).obj K.obj).iCycles p zK)
          (show ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU) _).obj
            ((Stacks.Cech.Refinement.sectionsComplex O).obj M.obj)).X q from
              ((cech O U hU).obj M.obj).iCycles q zM))) :
    cup O hK hM (sheafTensorPairingOf O K M hKM) p q (p + q) rfl
        (cechClass O U hU K p (((cech O U hU).obj K.obj).homologyπ p zK))
        (cechClass O U hU M q (((cech O U hU).obj M.obj).homologyπ q zM)) =
      cechClass O U hU (tensorPlusOf O K M hKM) (p + q)
        (((cech O U hU).obj (tensorPlusOf O K M hKM).obj).homologyπ (p + q) y) := by
  rw [homologyπ_eq_cocycleClass O U hU K p zK, homologyπ_eq_cocycleClass O U hU M q zM,
    cup_cechClass_cocycleClass, homologyπ_eq_cocycleClass O U hU _ (p + q) y]
  have e : unitTensor O ≫ Stacks.CupProduct.cupPair (Stacks.Cech.CupProduct.tensorModules _) _ _ p
      q (p + q) rfl (toMor (((cech O U hU).obj K.obj).iCycles p zK))
      (toMor (((cech O U hU).obj M.obj).iCycles q zM)) ≫
        (cechCup O U hU (sheafTensorPairingOf O K M hKM)).f (p + q) =
      toMor (((cech O U hU).obj (tensorPlusOf O K M hKM).obj).iCycles (p + q) y) := by
    rw [hy, ← unitTensor_cupPair_toMor_cechCup, toMor_apply]
  rw [cocycleClass_congr (p + q) e]

/-- The cup-model and comparison-model spellings of the cochain of a cup product agree. -/
theorem tmulHom_iCycles_cechSections {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) {p q : ℤ}
    (zK : ((cechSections O U hU).obj K.obj).cycles p)
    (zM : ((cechSections O U hU).obj M.obj).cycles q) :
    (Stacks.CategoryTheory.CechComplex.ιTot (coverObject U hU)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj M.obj) p q (p + q) rfl ≫
        (Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject U hU) _
          (sheafTensorPairingOf O K M hKM)).f (p + q)).hom
        (Stacks.CategoryTheory.CechComplex.tmulHom
          (((cechSections O U hU).obj K.obj).iCycles p zK)
          (((cechSections O U hU).obj M.obj).iCycles q zM)) =
    (Stacks.CategoryTheory.CechComplex.ιTot (coverObject U hU)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj M.obj) p q (p + q) rfl ≫
        (Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject U hU) _
          (sheafTensorPairingOf O K M hKM)).f (p + q)).hom
        (Stacks.CategoryTheory.CechComplex.tmulHom
          (show ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU) _).obj
            ((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj)).X p from
              ((cech O U hU).obj K.obj).iCycles p zK)
          (show ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU) _).obj
            ((Stacks.Cech.Refinement.sectionsComplex O).obj M.obj)).X q from
              ((cech O U hU).obj M.obj).iCycles q zM)) :=
  rfl

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The class of a cycle in the two spellings of the total Čech complex. -/
theorem homologyπ_cechSections_heq {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (p : ℤ)
    (z : ((cechSections O U hU).obj L.obj).cycles p) :
    HEq (((cech O U hU).obj L.obj).homologyπ p z)
      (((cechSections O U hU).obj L.obj).homologyπ p z) :=
  HEq.rfl

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The class of a cycle in the two spellings of the total Čech complex. -/
theorem homologyπ_cechSections {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (p : ℤ)
    (z : ((cechSections O U hU).obj L.obj).cycles p) :
    ((cech O U hU).obj L.obj).homologyπ p z = (((cechSections O U hU).obj L.obj).homologyπ p z :
      ((cech O U hU).obj L.obj).homology p) :=
  rfl

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The class in hypercohomology of a cycle, in the two spellings of the total Čech complex. -/
theorem cechClass_homologyπ_cechSections {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (p : ℤ)
    (z : ((cechSections O U hU).obj L.obj).cycles p) :
    cechClass O U hU L p (((cechSections O U hU).obj L.obj).homologyπ p z) =
      cechClass O U hU L p (((cech O U hU).obj L.obj).homologyπ p z) :=
  congrArg _ (homologyπ_cechSections O U hU L p z).symm

/-- **The Čech cup product at the sheaf-tensor coefficients of the classes of two cocycles of the
module-valued total Čech complexes** `Tot(Č(𝒰, K))`, `Tot(Č(𝒰, M))` over `A = Γ(X, 𝒪_X)`: it is
the class of any cycle of `Tot(Č(𝒰, Tot(K ⊗ M)))` whose cochain is the image of `zK ⊗ zM` under
the Čech cup product of [Stacks, Tag 07MB] at the sheaf-tensor coefficient pairing. -/
theorem cup_sheafTensorPairingOf_cechClass_ofSections {I : Type u} (U : I → Opens X)
    (hU : ⊤ = ⨆ i, U i) (hK : CechComputes O K) (hM : CechComputes O M) {p q : ℤ}
    (zK : ((cechSections O U hU).obj K.obj).cycles p)
    (zM : ((cechSections O U hU).obj M.obj).cycles q)
    (y : ((cechSections O U hU).obj (tensorPlusOf O K M hKM).obj).cycles (p + q))
    (hy : ((cechSections O U hU).obj (tensorPlusOf O K M hKM).obj).iCycles (p + q) y =
      (Stacks.CategoryTheory.CechComplex.ιTot (coverObject U hU)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj M.obj) p q (p + q) rfl ≫
        (Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject U hU) _
          (sheafTensorPairingOf O K M hKM)).f (p + q)).hom
        (Stacks.CategoryTheory.CechComplex.tmulHom (((cechSections O U hU).obj K.obj).iCycles p zK)
          (((cechSections O U hU).obj M.obj).iCycles q zM))) :
    cup O hK hM (sheafTensorPairingOf O K M hKM) p q (p + q) rfl
        (cechClass O U hU K p (((cechSections O U hU).obj K.obj).homologyπ p zK))
        (cechClass O U hU M q (((cechSections O U hU).obj M.obj).homologyπ q zM)) =
      cechClass O U hU (tensorPlusOf O K M hKM) (p + q)
        (((cechSections O U hU).obj (tensorPlusOf O K M hKM).obj).homologyπ (p + q) y) :=
  (congrArg₂ (cup O hK hM (sheafTensorPairingOf O K M hKM) p q (p + q) rfl)
    (cechClass_homologyπ_cechSections O U hU K p zK)
    (cechClass_homologyπ_cechSections O U hU M q zM)).trans
      ((cup_sheafTensorPairingOf_cechClass O K M hKM U hU hK hM zK zM y
        (hy.trans (tmulHom_iCycles_cechSections O K M hKM U hU zK zM))).trans
          (cechClass_homologyπ_cechSections O U hU _ (p + q) y).symm)

end Stacks.Cech.Hypercohomology

end
