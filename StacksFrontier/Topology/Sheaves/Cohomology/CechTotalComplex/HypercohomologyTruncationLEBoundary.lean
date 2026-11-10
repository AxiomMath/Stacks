module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyTruncationLEPairing
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyShiftedSingleCochains
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The boundary maps of the quotient brutal truncations on Čech cocycles

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings and `K` a bounded below
complex of `𝒪_X`-modules. For the short exact sequence

`0 ⟶ K^{p+1}[-p-1] ⟶ σ^{≤p+1}K ⟶ σ^{≤p}K ⟶ 0`

the boundary map `∂ : Hⁿ(X, σ^{≤p}K) ⟶ Hⁿ⁺¹(X, K^{p+1}[-p-1])` is computed on Čech cocycles: if
`c` is a Čech `q`-cocycle of `Kᵖ`, `q + p = n`, the class of `c` in `Hⁿ(X, Kᵖ[-p])` pushed to
`Hⁿ(X, σ^{≤p}K)` goes to `(-1)^q` times the class of `d(c)`, the cocycle obtained by applying the
differential `d : Kᵖ ⟶ K^{p+1}`. This is the familiar description of the connecting map of a
two-step filtration: lift `c` to a cochain of the total Čech complex of `σ^{≤p+1}K`, whose total
differential is `(-1)^q d(c)`.

## Main definitions

* `Stacks.Cech.Hypercohomology.truncLECochainTo`: the cochain of the total Čech complex of
  `σ^{≤a}K` attached to an explicit Čech cochain of a term `Kⁿ`, `n ≤ a`.

## Main results

* `Stacks.Cech.Hypercohomology.boundary_truncLESC_hypercohomologyMap_truncLEι`: the boundary map
  of `0 ⟶ K^{p+1}[-p-1] ⟶ σ^{≤p+1}K ⟶ σ^{≤p}K ⟶ 0` sends the image of the class of a Čech
  `q`-cocycle `c` of `Kᵖ` to `(-1)^q` times the class of `d(c)`.

## References

* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor coverObject abSections)
open Stacks.Cech.LinearCupProduct (cechCochainsMap ιTotalCechTo)
open StacksDraft.StupidTruncation

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing
attribute [local implicit_reducible] CechCochains.Cochain
open scoped Stacks.StandardDerivedModel

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
  (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))

/-- The identification of the sections of a retained term of `σ^{≤a}K` with those of `K`, from
the side of `K`. -/
abbrev truncLESectionsInv (a n : ℤ) (hn : n ≤ a) :
    sectionsP O (K.obj.X n) ⟶ ((Stacks.Cech.Refinement.sectionsComplex O).obj
      (truncLEPlus O K a).obj).X n :=
  (truncLESectionsXIso K a n hn).inv

/-- **The cochain of the total Čech complex of `σ^{≤a}K` attached to an explicit Čech
`p`-cochain of a term `Kⁿ`**, `n ≤ a`, placed in Čech degree `p` and coefficient degree `n`, at
a total degree `m = p + n`. -/
def truncLECochainTo (a n : ℤ) (hn : n ≤ a) {p : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X n)) p) (m : ℤ) (hm : (p : ℤ) + n = m) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤)).obj
          ((Stacks.Cech.Refinement.sectionsComplex O).obj (truncLEPlus O K a).obj)).X m :=
  sliceMor U hU (K.obj.X n) c ≫
    cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      (truncLESectionsInv K a n hn) p ≫
    ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      ((Stacks.Cech.Refinement.sectionsComplex O).obj (truncLEPlus O K a).obj) p n m hm

/-- The identification of the terms of `σ^{≤a}K`, on sections, carries the differential of `K`
to that of `σ^{≤a}K` below the top degree. -/
theorem truncLESectionsInv_d (a n : ℤ) (hn : n + 1 ≤ a) :
    truncLESectionsInv K a n (by omega) ≫
        ((Stacks.Cech.Refinement.sectionsComplex O).obj (truncLEPlus O K a).obj).d n (n + 1) =
      (sectionsPresheafFunctor (R := ringSheaf O) ⊤).map (K.obj.d n (n + 1)) ≫
        truncLESectionsInv K a (n + 1) hn := by
  have h := truncLESectionsXIso_comm K a n hn
  rw [← cancel_mono (truncLESectionsXIso K a (n + 1) hn).hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← h, Iso.inv_hom_id_assoc]
  rfl

/-- The cochain of a Čech cocycle, pushed along `f` and then through the Čech differential, is
zero. -/
private theorem sliceMor_comp_cechD_comp_eq_zero {F : SheafOfModules.{u} (ringSheaf O)} {Q}
    (f : sectionsP O F ⟶ Q) {p : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) {T}
    (k : Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) Q (p + 1) ⟶ T) :
    sliceMor U hU F c ≫ cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤) f p ≫
      Stacks.Cech.LinearCupProduct.cechD (coverObject U hU) (SectionRing (ringSheaf O) ⊤) Q p ≫
        k = 0 := by
  rw [reassoc_of% Stacks.Cech.LinearCupProduct.cechCochainsMap_d (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤) f p, ← Category.assoc (sliceMor U hU _ c), sliceMor_cechD, hc,
    sliceMor_zero, Limits.zero_comp]

/-- **The total differential of the cochain attached to a Čech cocycle below the top degree** is
`(-1)^p` times the cochain attached to its image under the coefficient differential
`Kⁿ ⟶ Kⁿ⁺¹`. -/
theorem truncLECochainTo_d (a n : ℤ) (hn : n + 1 ≤ a) {p : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X n)) p)
    (hc : CechCochains.cechD U (abSections (K.obj.X n)) p c = 0) (m : ℤ) (hm : (p : ℤ) + n = m) :
    truncLECochainTo U hU K a n (by omega) c m hm ≫
        ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
          (SectionRing (ringSheaf O) ⊤)).obj
            ((Stacks.Cech.Refinement.sectionsComplex O).obj (truncLEPlus O K a).obj)).d m (m + 1) =
      (p : ℤ).negOnePow • truncLECochainTo U hU K a (n + 1) hn
          (Stacks.Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map (K.obj.d n (n + 1))).hom
            p c) (m + 1) (by omega) := by
  have hd := Stacks.Cech.LinearCupProduct.ιTotalCechTo_d (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤)
    ((Stacks.Cech.Refinement.sectionsComplex O).obj (truncLEPlus O K a).obj) p n m hm
  unfold truncLECochainTo
  rw [Category.assoc, Category.assoc, hd, Preadditive.comp_add, Preadditive.comp_add,
    sliceMor_comp_cechD_comp_eq_zero U hU _ c hc, zero_add, Linear.comp_units_smul,
    Linear.comp_units_smul]
  refine congrArg (((p : ℤ).negOnePow) • ·) ?_
  rw [← Stacks.Cech.LinearCupProduct.cechCochainsMap_comp_assoc (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤), truncLESectionsInv_d K a n hn,
    Stacks.Cech.LinearCupProduct.cechCochainsMap_comp_assoc (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤)]
  simp only [← Category.assoc, sliceMor_map]

/-- **In the top degree the cochain attached to a Čech cocycle is a cocycle**: `σ^{≤a}K` vanishes
in degree `a + 1`. -/
theorem truncLECochainTo_d_top (a : ℤ) {p : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X a)) p)
    (hc : CechCochains.cechD U (abSections (K.obj.X a)) p c = 0) (m : ℤ) (hm : (p : ℤ) + a = m) :
    truncLECochainTo U hU K a a le_rfl c m hm ≫
        ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
          (SectionRing (ringSheaf O) ⊤)).obj
            ((Stacks.Cech.Refinement.sectionsComplex O).obj (truncLEPlus O K a).obj)).d m (m + 1) =
      0 := by
  have hd := Stacks.Cech.LinearCupProduct.ιTotalCechTo_d (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤)
    ((Stacks.Cech.Refinement.sectionsComplex O).obj (truncLEPlus O K a).obj) p a m hm
  have h0 : cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      (((Stacks.Cech.Refinement.sectionsComplex O).obj (truncLEPlus O K a).obj).d a (a + 1)) p =
        0 := by
    rw [(isZero_truncLESections_X K (show a < a + 1 by omega)).eq_of_tgt
      (((Stacks.Cech.Refinement.sectionsComplex O).obj (truncLEPlus O K a).obj).d a (a + 1)) 0]
    change ((CategoryTheory.cechComplexFunctor (coverObject U hU)).map (0 : _ ⟶ _)).f p = 0
    rw [Functor.map_zero]
    rfl
  unfold truncLECochainTo
  rw [Category.assoc, Category.assoc, hd, h0, Limits.zero_comp, smul_zero, add_zero,
    sliceMor_comp_cechD_comp_eq_zero U hU _ c hc]

/-- **The attached cochains are compatible with the comparisons `σ^{≤a}K ⟶ σ^{≤b}K`.** -/
theorem truncLECochainTo_truncLEMap {a b : ℤ} (h : b ≤ a) (n : ℤ) (hn : n ≤ b) {p : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X n)) p) (m : ℤ) (hm : (p : ℤ) + n = m) :
    truncLECochainTo U hU K a n (hn.trans h) c m hm ≫
        ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
          (SectionRing (ringSheaf O) ⊤)).map
            ((Stacks.Cech.Refinement.sectionsComplex O).map (truncLEMap O K h).hom)).f m =
      truncLECochainTo U hU K b n hn c m hm := by
  have hι := Stacks.Cech.LinearCupProduct.ιTotalCechTo_totalCechComplexFunctor_map
    (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
    ((Stacks.Cech.Refinement.sectionsComplex O).map (truncLEMap O K h).hom) p n m hm
  have hcomp : truncLESectionsInv K a n (hn.trans h) ≫
      ((Stacks.Cech.Refinement.sectionsComplex O).map (truncLEMap O K h).hom).f n =
      truncLESectionsInv K b n hn := by
    rw [← cancel_mono (truncLESectionsXIso K b n hn).hom, Category.assoc,
      sectionsComplex_truncLEMap_f K h n hn, Iso.inv_hom_id, Iso.inv_hom_id]
  unfold truncLECochainTo
  rw [Category.assoc, Category.assoc, hι,
    ← Stacks.Cech.LinearCupProduct.cechCochainsMap_comp_assoc (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤), hcomp]

/-- **The cochain attached to a Čech cochain of `Kᵃ` placed in degree `a`, pushed along
`Kᵃ[-a] ⟶ σ^{≤a}K`, is the cochain attached to it in `σ^{≤a}K`.** -/
theorem cochainOfAtTo_truncLEι (a : ℤ) {p : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X a)) p) (m : ℤ) (hm : (p : ℤ) + a = m) :
    cochainOfAtTo U hU (K.obj.X a) a c m hm ≫
        ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
          (SectionRing (ringSheaf O) ⊤)).map
            ((Stacks.Cech.Refinement.sectionsComplex O).map (truncLEι O K a).hom)).f m =
      truncLECochainTo U hU K a a le_rfl c m hm := by
  have hι := Stacks.Cech.LinearCupProduct.ιTotalCechTo_totalCechComplexFunctor_map
    (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
    ((Stacks.Cech.Refinement.sectionsComplex O).map (truncLEι O K a).hom) p a m hm
  have hcomp : (singleXIsoAt O (K.obj.X a) a a rfl).inv ≫
      ((Stacks.Cech.Refinement.sectionsComplex O).map (truncLEι O K a).hom).f a =
      truncLESectionsInv K a a le_rfl := by
    rw [← cancel_mono (truncLESectionsXIso K a a le_rfl).hom, Category.assoc,
      sectionsComplex_truncLEι_f K a, Iso.inv_hom_id, Iso.inv_hom_id]
  unfold cochainOfAtTo truncLECochainTo
  rw [Category.assoc, Category.assoc, hι,
    ← Stacks.Cech.LinearCupProduct.cechCochainsMap_comp_assoc (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤), hcomp]

/-! ### The same cochains in the total Čech complexes of hypercohomology -/

/-- The cochain `truncLECochainTo`, in the total Čech complex `cech` of hypercohomology. -/
abbrev truncLECochain (a n : ℤ) (hn : n ≤ a) {p : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X n)) p) (m : ℤ) (hm : (p : ℤ) + n = m) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶ ((cech O U hU).obj (truncLEPlus O K a).obj).X m :=
  truncLECochainTo U hU K a n hn c m hm

/-- The cochain `cochainOfAtTo`, in the total Čech complex `cech` of hypercohomology. -/
abbrev cochainOfAtCech (F : SheafOfModules.{u} (ringSheaf O)) (a : ℤ) {p : ℕ}
    (c : CechCochains.Cochain U (abSections F) p) (m : ℤ) (hm : (p : ℤ) + a = m) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶ ((cech O U hU).obj (singlePlus O F a).obj).X m :=
  cochainOfAtTo U hU F a c m hm

/-- `truncLECochainTo_d` for the cochains `truncLECochain` in the total Čech complex `cech`. -/
theorem truncLECochain_d (a n : ℤ) (hn : n + 1 ≤ a) {p : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X n)) p)
    (hc : CechCochains.cechD U (abSections (K.obj.X n)) p c = 0) (m : ℤ) (hm : (p : ℤ) + n = m) :
    truncLECochain U hU K a n (by omega) c m hm ≫
        ((cech O U hU).obj (truncLEPlus O K a).obj).d m (m + 1) =
      (p : ℤ).negOnePow • truncLECochain U hU K a (n + 1) hn
          (Stacks.Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map (K.obj.d n (n + 1))).hom
            p c) (m + 1) (by omega) :=
  truncLECochainTo_d U hU K a n hn c hc m hm

/-- `truncLECochainTo_d_top` for the cochains `truncLECochain` in the total Čech complex
`cech`. -/
theorem truncLECochain_d_top (a : ℤ) {p : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X a)) p)
    (hc : CechCochains.cechD U (abSections (K.obj.X a)) p c = 0) (m : ℤ) (hm : (p : ℤ) + a = m) :
    truncLECochain U hU K a a le_rfl c m hm ≫
        ((cech O U hU).obj (truncLEPlus O K a).obj).d m (m + 1) = 0 :=
  truncLECochainTo_d_top U hU K a c hc m hm

/-- `truncLECochainTo_truncLEMap` for the cochains `truncLECochain` in the total Čech complex
`cech`. -/
theorem truncLECochain_truncLEMap {a b : ℤ} (h : b ≤ a) (n : ℤ) (hn : n ≤ b) {p : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X n)) p) (m : ℤ) (hm : (p : ℤ) + n = m) :
    truncLECochain U hU K a n (hn.trans h) c m hm ≫
        ((cech O U hU).map (truncLEMap O K h).hom).f m =
      truncLECochain U hU K b n hn c m hm :=
  truncLECochainTo_truncLEMap U hU K h n hn c m hm

/-- `cochainOfAtTo_truncLEι` for the cochains `cochainOfAtCech` and `truncLECochain` in the total
Čech complex `cech`. -/
theorem cochainOfAtCech_truncLEι (a : ℤ) {p : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X a)) p) (m : ℤ) (hm : (p : ℤ) + a = m) :
    cochainOfAtCech U hU (K.obj.X a) a c m hm ≫ ((cech O U hU).map (truncLEι O K a).hom).f m =
      truncLECochain U hU K a a le_rfl c m hm :=
  cochainOfAtTo_truncLEι U hU K a c m hm

/-- The total differential of the cochain `cochainOfAtCech` attached to a Čech `p`-cochain `c` of
`F` is the cochain attached to `d(c)`. -/
theorem cochainOfAtCech_d (F : SheafOfModules.{u} (ringSheaf O)) (a : ℤ) {p : ℕ}
    (c : CechCochains.Cochain U (abSections F) p) (m : ℤ) (hm : (p : ℤ) + a = m) :
    cochainOfAtCech U hU F a c m hm ≫ ((cech O U hU).obj (singlePlus O F a).obj).d m (m + 1) =
      cochainOfAtCech U hU F a (CechCochains.cechD U (abSections F) p c) (m + 1)
        (by push_cast; omega) :=
  cochainOfAtTo_d U hU F a c m hm

/-- The class in `H^{q+p}(X, σ^{≤p}K)` of the cochain attached to a Čech `q`-cocycle of `Kᵖ` is
the image of its class in `H^{q+p}(X, Kᵖ[-p])`. -/
theorem cechClass_truncLECochain (p : ℤ) {q : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X p)) q)
    (hc : CechCochains.cechD U (abSections (K.obj.X p)) q c = 0)
    (h : truncLECochain U hU K p p le_rfl c ((q : ℤ) + p) rfl ≫
      ((cech O U hU).obj (truncLEPlus O K p).obj).d ((q : ℤ) + p) ((q : ℤ) + p + 1) = 0) :
    cechClass O U hU (truncLEPlus O K p) ((q : ℤ) + p)
        (cocycleClass ((q : ℤ) + p) (truncLECochain U hU K p p le_rfl c ((q : ℤ) + p) rfl) h
          (1 : SectionRing (ringSheaf O) ⊤)) =
      hypercohomologyMap O (truncLEι O K p) ((q : ℤ) + p)
        (cechCocycleClassAt U hU (K.obj.X p) p c hc) := by
  unfold cechCocycleClassAt
  symm
  rw [← ConcreteCategory.comp_apply, ← cechClass_naturality, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply (cocycleClass _ _ _), cocycleClass_comp_homologyMap]
  congr 2
  exact congrArg ConcreteCategory.hom
    (cocycleClass_congr _ (cochainOfAtCech_truncLEι U hU K p c ((q : ℤ) + p) rfl) _ _)

/-- **The boundary map of `0 ⟶ K^{p+1}[-p-1] ⟶ σ^{≤p+1}K ⟶ σ^{≤p}K ⟶ 0` on Čech cocycles.** For
a Čech `q`-cocycle `c` of `Kᵖ`, the class of `c` in `H^{q+p}(X, Kᵖ[-p])`, pushed to
`H^{q+p}(X, σ^{≤p}K)`, goes to `(-1)^q` times the class of the cocycle `d(c)` of `K^{p+1}`. -/
theorem boundary_truncLESC_hypercohomologyMap_truncLEι (p : ℤ) {q : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X p)) q)
    (hc : CechCochains.cechD U (abSections (K.obj.X p)) q c = 0) (n₁ : ℤ)
    (hn₁ : (q : ℤ) + p + 1 = n₁) :
    boundary O (truncLESC O K (p + 1) p rfl) (truncLESC_shortExact O K (p + 1) p rfl) ((q : ℤ) + p)
        n₁ hn₁ (hypercohomologyMap O (truncLEι O K p) ((q : ℤ) + p)
          (cechCocycleClassAt U hU (K.obj.X p) p c hc)) =
      (q : ℤ).negOnePow • cechClass O U hU (singlePlus O (K.obj.X (p + 1)) (p + 1)) n₁
        (cocycleClass n₁ (cochainOfAtCech U hU (K.obj.X (p + 1)) (p + 1)
          (Stacks.Cohomology.CechOne.push U
            ((SheafOfModules.toSheaf _).map (K.obj.d p (p + 1))).hom q c) n₁ (by omega))
          (by
            rw [cochainOfAtCech_d U hU (K.obj.X (p + 1)) (p + 1) _ n₁ (by omega),
              ← Stacks.Cohomology.CechOne.push_cechD, hc, map_zero]
            exact cochainOfAtTo_zero U hU _ _ _ _)
          (1 : SectionRing (ringSheaf O) ⊤)) := by
  subst hn₁
  have hα₃ : (truncLECochain U hU K (p + 1) p (by omega) c ((q : ℤ) + p) rfl ≫
      ((cech O U hU).map (truncLEMap O K (show p ≤ p + 1 by omega)).hom).f ((q : ℤ) + p)) ≫
      ((cech O U hU).obj (truncLEPlus O K p).obj).d ((q : ℤ) + p) ((q : ℤ) + p + 1) = 0 := by
    rw [truncLECochain_truncLEMap U hU K (show p ≤ p + 1 by omega) p le_rfl c ((q : ℤ) + p) rfl]
    exact truncLECochain_d_top U hU K p c hc ((q : ℤ) + p) rfl
  have hpush : CechCochains.cechD U (abSections (K.obj.X (p + 1))) q
      (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map (K.obj.d p (p + 1))).hom q c) = 0 := by
    rw [← Stacks.Cohomology.CechOne.push_cechD, hc, map_zero]
  have hy : cochainOfAtCech U hU (K.obj.X (p + 1)) (p + 1)
      (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map (K.obj.d p (p + 1))).hom q c) ((q : ℤ) + p + 1)
        (by omega) ≫
      ((cech O U hU).obj (singlePlus O (K.obj.X (p + 1)) (p + 1)).obj).d ((q : ℤ) + p + 1)
        ((q : ℤ) + p + 1 + 1) = 0 := by
    rw [cochainOfAtCech_d U hU (K.obj.X (p + 1)) (p + 1) _ _ (by omega), hpush]
    exact cochainOfAtTo_zero U hU _ _ _ _
  have hα₁ : (((q : ℤ).negOnePow : ℤ) • cochainOfAtCech U hU (K.obj.X (p + 1)) (p + 1)
      (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map (K.obj.d p (p + 1))).hom q c) ((q : ℤ) + p + 1)
        (by omega)) ≫
      ((cech O U hU).obj (singlePlus O (K.obj.X (p + 1)) (p + 1)).obj).d ((q : ℤ) + p + 1)
        ((q : ℤ) + p + 1 + 1) = 0 := by
    rw [Preadditive.zsmul_comp, hy, smul_zero]
  have hα : (((q : ℤ).negOnePow : ℤ) • cochainOfAtCech U hU (K.obj.X (p + 1)) (p + 1)
      (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map (K.obj.d p (p + 1))).hom q c) ((q : ℤ) + p + 1)
        (by omega)) ≫
      ((cech O U hU).map (truncLEι O K (p + 1)).hom).f ((q : ℤ) + p + 1) =
      truncLECochain U hU K (p + 1) p (by omega) c ((q : ℤ) + p) rfl ≫
      ((cech O U hU).obj (truncLEPlus O K (p + 1)).obj).d ((q : ℤ) + p) ((q : ℤ) + p + 1) := by
    rw [Preadditive.zsmul_comp, cochainOfAtCech_truncLEι U hU K (p + 1),
      truncLECochain_d U hU K (p + 1) p le_rfl c hc ((q : ℤ) + p) rfl, Units.smul_def]
  have key₀ : cocycleClass ((q : ℤ) + p + 1) _ hα₁ ≫
      cechClass O U hU (singlePlus O (K.obj.X (p + 1)) (p + 1)) ((q : ℤ) + p + 1) =
      cocycleClass ((q : ℤ) + p) _ hα₃ ≫ cechClass O U hU (truncLEPlus O K p) ((q : ℤ) + p) ≫
        boundary O (truncLESC O K (p + 1) p rfl) (truncLESC_shortExact O K (p + 1) p rfl)
          ((q : ℤ) + p) ((q : ℤ) + p + 1) rfl :=
    cechClass_boundary O U hU (truncLESC O K (p + 1) p rfl)
      (truncLESC_shortExact O K (p + 1) p rfl) ((q : ℤ) + p) _ _ hα₃ hα₁ hα
  have hz := cocycleClass_zsmul ((q : ℤ).negOnePow : ℤ) ((q : ℤ) + p + 1) _ hy hα₁
  rw [hz, Preadditive.zsmul_comp] at key₀
  have h₂ := cechClass_truncLECochain U hU K p c hc
    (by rw [← truncLECochain_truncLEMap U hU K (show p ≤ p + 1 by omega) p le_rfl c
      ((q : ℤ) + p) rfl]; exact hα₃)
  have h₃ : cechClass O U hU (truncLEPlus O K p) ((q : ℤ) + p)
      (cocycleClass ((q : ℤ) + p) _ hα₃ (1 : SectionRing (ringSheaf O) ⊤)) =
      hypercohomologyMap O (truncLEι O K p) ((q : ℤ) + p)
        (cechCocycleClassAt U hU (K.obj.X p) p c hc) :=
    (congrArg (fun z => cechClass O U hU (truncLEPlus O K p) ((q : ℤ) + p) z)
      (congrArg (fun φ => φ (1 : SectionRing (ringSheaf O) ⊤)) (congrArg ConcreteCategory.hom
        (cocycleClass_congr _ (truncLECochain_truncLEMap U hU K (show p ≤ p + 1 by omega) p
          le_rfl c ((q : ℤ) + p) rfl) hα₃ _)))).trans h₂
  have key := (ConcreteCategory.congr_hom key₀ (1 : SectionRing (ringSheaf O) ⊤)).symm
  rw [← h₃]
  refine key.trans ?_
  rw [Units.smul_def]
  rfl

/-- `boundary_truncLESC_hypercohomologyMap_truncLEι` for the short exact sequence
`0 ⟶ Kᵖ[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p'}K ⟶ 0` with `p' + 1 = p` given by an equation. -/
theorem boundary_truncLESC_hypercohomologyMap_truncLEι' (p p' : ℤ) (hp : p' + 1 = p) {q : ℕ}
    (c : CechCochains.Cochain U (abSections (K.obj.X p')) q)
    (hc : CechCochains.cechD U (abSections (K.obj.X p')) q c = 0) (n₁ : ℤ)
    (hn₁ : (q : ℤ) + p' + 1 = n₁) :
    boundary O (truncLESC O K p p' hp) (truncLESC_shortExact O K p p' hp) ((q : ℤ) + p') n₁ hn₁
        (hypercohomologyMap O (truncLEι O K p') ((q : ℤ) + p')
          (cechCocycleClassAt U hU (K.obj.X p') p' c hc)) =
      (q : ℤ).negOnePow • cechClass O U hU (singlePlus O (K.obj.X p) p) n₁
        (cocycleClass n₁ (cochainOfAtCech U hU (K.obj.X p) p
          (Stacks.Cohomology.CechOne.push U
            ((SheafOfModules.toSheaf _).map (K.obj.d p' p)).hom q c) n₁ (by omega))
          (by
            rw [cochainOfAtCech_d U hU (K.obj.X p) p _ n₁ (by omega),
              ← Stacks.Cohomology.CechOne.push_cechD, hc, map_zero]
            exact cochainOfAtTo_zero U hU _ _ _ _)
          (1 : SectionRing (ringSheaf O) ⊤)) := by
  subst hp
  exact boundary_truncLESC_hypercohomologyMap_truncLEι U hU K p' c hc n₁ hn₁

end Stacks.Cech.Hypercohomology

end
