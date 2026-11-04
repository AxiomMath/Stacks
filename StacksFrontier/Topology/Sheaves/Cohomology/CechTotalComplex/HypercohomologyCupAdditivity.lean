module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupNaturality

/-!
# Additivity of the cup product on hypercohomology

The cup product `Stacks.Cech.Hypercohomology.cup` of Cohomology, Section 01FP is additive in each
variable. Together with `Stacks.Cech.Hypercohomology.cup_smul_left` and
`Stacks.Cech.Hypercohomology.cup_smul_right` this makes it a bilinear map over the global
sections of `𝒪_X`, `Stacks.Cech.Hypercohomology.cupBilin`.

## Main results

* `Stacks.Cech.Hypercohomology.cup_add_left`, `Stacks.Cech.Hypercohomology.cup_add_right`.
* `Stacks.Cech.Hypercohomology.cupBilin`: the cup product as a bilinear map.

## References

* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)
open Stacks.Cech.CupProduct (tensorModules)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

/-- The cup product of cochains is additive in its first factor. -/
theorem cupPair_add_left {R : Type u} [CommRing R] (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    {P Q : ModuleCat.{u} R} (p q t : ℤ) (ht : p + q = t) (α α' : P ⟶ K.X p) (β : Q ⟶ L.X q) :
    Stacks.CupProduct.cupPair (tensorModules R) K L p q t ht (α + α') β =
      Stacks.CupProduct.cupPair (tensorModules R) K L p q t ht α β +
        Stacks.CupProduct.cupPair (tensorModules R) K L p q t ht α' β := by
  have h : ((tensorModules R).map (α + α')).app Q =
      ((tensorModules R).map α).app Q + ((tensorModules R).map α').app Q :=
    ModuleCat.hom_ext (TensorProduct.map_add_left _ _ _)
  dsimp only [Stacks.CupProduct.cupPair]
  rw [h, Preadditive.add_comp]

/-- The cup product of cochains is additive in its second factor. -/
theorem cupPair_add_right {R : Type u} [CommRing R] (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    {P Q : ModuleCat.{u} R} (p q t : ℤ) (ht : p + q = t) (α : P ⟶ K.X p) (β β' : Q ⟶ L.X q) :
    Stacks.CupProduct.cupPair (tensorModules R) K L p q t ht α (β + β') =
      Stacks.CupProduct.cupPair (tensorModules R) K L p q t ht α β +
        Stacks.CupProduct.cupPair (tensorModules R) K L p q t ht α β' := by
  have h : ((tensorModules R).obj (K.X p)).map (β + β') =
      ((tensorModules R).obj (K.X p)).map β + ((tensorModules R).obj (K.X p)).map β' :=
    ModuleCat.hom_ext (TensorProduct.map_add_right _ _ _)
  dsimp only [Stacks.CupProduct.cupPair]
  rw [h, Preadditive.add_comp, Preadditive.comp_add]

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)

/-- **The cup product of Čech classes is additive in the first factor.** -/
theorem cechCupClass_add_left {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) (p q t : ℤ) (ht : p + q = t)
    (x x' : ((cech O U hU).obj F.obj).homology p)
    (y : unitModule _ ⟶ ((cech O U hU).obj G.obj).homology q) :
    cechCupClass O U hU γ p q t ht (toMor (x + x')) y =
      cechCupClass O U hU γ p q t ht (toMor x) y + cechCupClass O U hU γ p q t ht (toMor x') y := by
  obtain ⟨zx, hzx, hx⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O U hU).obj F.obj) p (p + 1) (CochainComplex.next ℤ p) (toMor x)
  obtain ⟨zx', hzx', hx'⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O U hU).obj F.obj) p (p + 1) (CochainComplex.next ℤ p) (toMor x')
  obtain ⟨zy, hzy, hy⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O U hU).obj G.obj) q (q + 1) (CochainComplex.next ℤ q) y
  have hsum : (zx + zx') ≫ ((cech O U hU).obj F.obj).d p (p + 1) = 0 := by
    rw [Preadditive.add_comp, hzx, hzx', add_zero]
  have e₁ : toMor x = cocycleClass p zx hzx := hx.symm
  have e₂ : toMor x' = cocycleClass p zx' hzx' := hx'.symm
  have e₃ : y = cocycleClass q zy hzy := hy.symm
  have hxx : toMor (x + x') = cocycleClass p (zx + zx') hsum := by
    rw [toMor_add, e₁, e₂, cocycleClass_add]
  rw [hxx, e₁, e₂, e₃, cechCupClass_eq, cechCupClass_eq, cechCupClass_eq,
    ← Preadditive.comp_add]
  congr 1
  have e : Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
      ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht (zx + zx') zy ≫
        (cechCup O U hU γ).f t =
      Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
        ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht zx zy ≫
          (cechCup O U hU γ).f t +
      Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
        ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht zx' zy ≫
          (cechCup O U hU γ).f t := by
    rw [cupPair_add_left, Preadditive.add_comp]
  exact (cocycleClass_congr t e _ _).trans (cocycleClass_add t _ _ _ _)

/-- **The cup product of Čech classes is additive in the second factor.** -/
theorem cechCupClass_add_right {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) (p q t : ℤ) (ht : p + q = t)
    (x : unitModule _ ⟶ ((cech O U hU).obj F.obj).homology p)
    (y y' : ((cech O U hU).obj G.obj).homology q) :
    cechCupClass O U hU γ p q t ht x (toMor (y + y')) =
      cechCupClass O U hU γ p q t ht x (toMor y) + cechCupClass O U hU γ p q t ht x (toMor y') := by
  obtain ⟨zx, hzx, hx⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O U hU).obj F.obj) p (p + 1) (CochainComplex.next ℤ p) x
  obtain ⟨zy, hzy, hy⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O U hU).obj G.obj) q (q + 1) (CochainComplex.next ℤ q) (toMor y)
  obtain ⟨zy', hzy', hy'⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O U hU).obj G.obj) q (q + 1) (CochainComplex.next ℤ q) (toMor y')
  have hsum : (zy + zy') ≫ ((cech O U hU).obj G.obj).d q (q + 1) = 0 := by
    rw [Preadditive.add_comp, hzy, hzy', add_zero]
  have e₁ : x = cocycleClass p zx hzx := hx.symm
  have e₂ : toMor y = cocycleClass q zy hzy := hy.symm
  have e₃ : toMor y' = cocycleClass q zy' hzy' := hy'.symm
  have hyy : toMor (y + y') = cocycleClass q (zy + zy') hsum := by
    rw [toMor_add, e₂, e₃, cocycleClass_add]
  rw [hyy, e₁, e₂, e₃, cechCupClass_eq, cechCupClass_eq, cechCupClass_eq,
    ← Preadditive.comp_add]
  congr 1
  have e : Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
      ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht zx (zy + zy') ≫
        (cechCup O U hU γ).f t =
      Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
        ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht zx zy ≫
          (cechCup O U hU γ).f t +
      Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
        ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht zx zy' ≫
          (cechCup O U hU γ).f t := by
    rw [cupPair_add_right, Preadditive.add_comp]
  exact (cocycleClass_congr t e _ _).trans (cocycleClass_add t _ _ _ _)

/-- Two classes of hypercohomology and a third one are represented on a common covering. -/
theorem exists_common_cechClass {F G : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (p q : ℤ) (a a' : hypercohomology O F p)
    (b : hypercohomology O G q) :
    ∃ (J : Type u) (W : J → Opens X) (hW : ⊤ = ⨆ j, W j)
      (x x' : ((cech O W hW).obj F.obj).homology p) (y : ((cech O W hW).obj G.obj).homology q),
      cechClass O W hW F p x = a ∧ cechClass O W hW F p x' = a' ∧ cechClass O W hW G q y = b := by
  obtain ⟨I₁, U₁, hU₁, x₁, rfl⟩ := (hF p).1 a
  obtain ⟨I₂, U₂, hU₂, x₂, rfl⟩ := (hF p).1 a'
  obtain ⟨I₃, U₃, hU₃, y₃, rfl⟩ := (hG q).1 b
  have hW₁₂ := iSup_inf_eq_top U₁ hU₁ U₂ hU₂
  have hW := iSup_inf_eq_top _ hW₁₂ U₃ hU₃
  refine ⟨_, _, hW, HomologicalComplex.homologyMap
      ((Stacks.Cech.Refinement.cechRefinement O U₁ hU₁ _ hW (fun j => j.1.1)
        (fun j => inf_le_left.trans inf_le_left)).app F.obj) p x₁,
    HomologicalComplex.homologyMap
      ((Stacks.Cech.Refinement.cechRefinement O U₂ hU₂ _ hW (fun j => j.1.2)
        (fun j => inf_le_left.trans inf_le_right)).app F.obj) p x₂,
    HomologicalComplex.homologyMap
      ((Stacks.Cech.Refinement.cechRefinement O U₃ hU₃ _ hW (fun j => j.2)
        (fun _ => inf_le_right)).app G.obj) q y₃, ?_, ?_, ?_⟩
  · exact (ConcreteCategory.comp_apply _ _ _).symm.trans
      (congrArg (fun φ => φ x₁) (cechClass_refinement O U₁ hU₁ _ hW _ _ F p))
  · exact (ConcreteCategory.comp_apply _ _ _).symm.trans
      (congrArg (fun φ => φ x₂) (cechClass_refinement O U₂ hU₂ _ hW _ _ F p))
  · exact (ConcreteCategory.comp_apply _ _ _).symm.trans
      (congrArg (fun φ => φ y₃) (cechClass_refinement O U₃ hU₃ _ hW _ _ G q))

/-- **The cup product is additive in the first factor.** -/
theorem cup_add_left {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) (a a' : hypercohomology O F p) (b : hypercohomology O G q) :
    cup O hF hG γ p q t ht (a + a') b =
      cup O hF hG γ p q t ht a b + cup O hF hG γ p q t ht a' b := by
  obtain ⟨J, W, hW, x, x', y, rfl, rfl, rfl⟩ := exists_common_cechClass O hF hG p q a a' b
  rw [← map_add, cup_eq O _ hW hF hG, cup_eq O _ hW hF hG, cup_eq O _ hW hF hG,
    cechCupClass_add_left, Preadditive.add_comp]
  rfl

/-- **The cup product is additive in the second factor.** -/
theorem cup_add_right {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) (a : hypercohomology O F p) (b b' : hypercohomology O G q) :
    cup O hF hG γ p q t ht a (b + b') =
      cup O hF hG γ p q t ht a b + cup O hF hG γ p q t ht a b' := by
  obtain ⟨J, W, hW, y, y', x, rfl, rfl, rfl⟩ := exists_common_cechClass O hG hF q p b b' a
  rw [← map_add, cup_eq O _ hW hF hG, cup_eq O _ hW hF hG, cup_eq O _ hW hF hG,
    cechCupClass_add_right, Preadditive.add_comp]
  rfl

/-- **The cup product of Cohomology, Section 01FP as a bilinear map** over the global sections of
`𝒪_X`, `Hᵖ(X, F) × H^q(X, G) ⟶ Hᵗ(X, H)` for `p + q = t`. -/
def cupBilin {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) :
    hypercohomology O F p →ₗ[SectionRing (ringSheaf O) ⊤] hypercohomology O G q →ₗ[SectionRing
      (ringSheaf O) ⊤] hypercohomology O H t :=
  LinearMap.mk₂ _ (cup O hF hG γ p q t ht) (cup_add_left O hF hG γ p q t ht)
    (fun r a b => cup_smul_left O hF hG γ p q t ht a b r) (cup_add_right O hF hG γ p q t ht)
    (fun r a b => cup_smul_right O hF hG γ p q t ht a b r)

/-- The bilinear map `cupBilin` evaluated at `a` and `b` is the cup product of `a` and `b`. -/
theorem cupBilin_apply {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) (a : hypercohomology O F p) (b : hypercohomology O G q) :
    cupBilin O hF hG γ p q t ht a b = cup O hF hG γ p q t ht a b :=
  rfl

end Stacks.Cech.Hypercohomology

end
