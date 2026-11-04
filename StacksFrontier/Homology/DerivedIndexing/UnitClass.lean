module

public import StacksFrontier.Homology.DerivedIndexing.StandardComparisonUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.ShortExactCyclesBoundary

/-!
# The class of a degree-zero cocycle in the derived functor

Let `F : 𝒜 ⥤ ℬ` be an additive functor, `𝒜` with enough injectives, and `K` a bounded below
complex of `𝒜`. A degree-zero cocycle of `F(K)` has a class in `H⁰(F(K))`, and the derived-functor
unit `F(K) ⟶ RF(K)` carries it to a class in `H⁰(RF(K))`. For `F` the global sections of sheaves
this is the class in hypercohomology of a global cocycle.

## Main definitions

* `Stacks.DerivedIndexing.unitClassHom`: the class map
  `Z⁰(F(K)) ⟶ H⁰(RF(K))`.
* `Stacks.DerivedIndexing.imageCycleClass`, `Stacks.DerivedIndexing.cyclesRightDerivedOneMap`:
  for a short exact sequence of complexes, the class of a section of the image of the cycles,
  and the map induced on `R¹F` by the inclusion of the cycles.

## Main results

* `Stacks.DerivedIndexing.unitClassHom_naturality`: the class map is natural in `K`.
* `Stacks.DerivedIndexing.toRightDerivedZero_comp_derivedPlusToStandard_inv_eq_unitClassHom`:
  for an object placed in degree zero, the class map is Mathlib's
  `CategoryTheory.Functor.toRightDerivedZero`, read in the `ℤ`-indexing.
* `Stacks.DerivedIndexing.imageCycleClass_comp_shortExactBoundary`: the boundary map of a short
  exact sequence of complexes on those classes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.DerivedIndexing

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type*} {B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- **The class in `H⁰(RF(K))` of a degree-zero cocycle of `F(K)`**: its class in `H⁰(F(K))`,
followed by the derived-functor unit `F(K) ⟶ RF(K)`. -/
def unitClassHom (K : CochainComplex.Plus A) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj).cycles 0 ⟶
      (DerivedCategory.Plus.homologyFunctor B 0).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) :=
  HomologicalComplex.homologyπ _ 0 ≫ (DerivedCategory.homologyFunctorFactors B 0).inv.app _ ≫
    (DerivedCategory.Plus.homologyFunctor B 0).map
      ((Functor.mapCochainComplexPlusDerivedUnit F).app K)

/-- Three commutative squares pasted, with every object and morphism a variable. -/
private theorem paste_three {C : Type*} [Category* C] {p q r s p' q' r' s' : C}
    (a : p ⟶ q) (b : q ⟶ r) (c : r ⟶ s) (a' : p' ⟶ q') (b' : q' ⟶ r') (c' : r' ⟶ s')
    (x : p ⟶ p') (y : q ⟶ q') (z : r ⟶ r') (w : s ⟶ s')
    (h₁ : a ≫ y = x ≫ a') (h₂ : b ≫ z = y ≫ b') (h₃ : c ≫ w = z ≫ c') :
    (a ≫ b ≫ c) ≫ w = x ≫ a' ≫ b' ≫ c' := by
  simp only [Category.assoc]
  rw [h₃, reassoc_of% h₂, reassoc_of% h₁]

/-- **The class of a cocycle is natural in the complex.** -/
theorem unitClassHom_naturality {K L : CochainComplex.Plus A} (φ : K ⟶ L) :
    unitClassHom F K ≫ (DerivedCategory.Plus.homologyFunctor B 0).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ)) =
      HomologicalComplex.cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom) 0 ≫
        unitClassHom F L := by
  have hu := (Functor.mapCochainComplexPlusDerivedUnit F).naturality φ
  simp only [Functor.comp_map] at hu
  have h₃ : (DerivedCategory.Plus.homologyFunctor B 0).map
        ((Functor.mapCochainComplexPlusDerivedUnit F).app K) ≫
      (DerivedCategory.Plus.homologyFunctor B 0).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ)) =
      (DerivedCategory.Plus.homologyFunctor B 0).map
          (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ)) ≫
        (DerivedCategory.Plus.homologyFunctor B 0).map
          ((Functor.mapCochainComplexPlusDerivedUnit F).app L) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hu]
  have h₂ := ((DerivedCategory.homologyFunctorFactors B 0).inv.naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom)).symm
  have h₁ := HomologicalComplex.homologyπ_naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom) 0
  exact paste_three _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃

/-- **For an object placed in degree zero the class map is `toRightDerivedZero`**, read in the
`ℤ`-indexing through `derivedPlusToStandard`. -/
theorem toRightDerivedZero_comp_derivedPlusToStandard_inv_eq_unitClassHom (M : A) :
    F.toRightDerivedZero.app M ≫ (derivedPlusToStandard F 0).inv.app M =
      singleCyclesHom F M ≫ unitClassHom F (singleCochainPlusFunctor.obj M) :=
  toRightDerivedZero_comp_derivedPlusToStandard_inv F M

end Stacks.DerivedIndexing

namespace Stacks.DerivedIndexing

section Cycles

open Stacks.Cohomology.RightDerivedBoundary

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type*} {B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
  (S : ShortComplex (CochainComplex.Plus A)) (hS : (toSC S).ShortExact)

/-- **The class in `H⁰(RF(K₃))` of a section of the image `I` of `Z⁰K₂ ⟶ Z⁰K₃`**, through the
inclusion of `I` in the cycles of `K₃`. -/
def imageCycleClass :
    F.obj (HomologicalComplex.shortExactCycles (toSC S) 0).X₃ ⟶
      (DerivedCategory.Plus.homologyFunctor B 0).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj S.X₃)) :=
  singleCyclesHom F (HomologicalComplex.shortExactCycles (toSC S) 0).X₃ ≫
    HomologicalComplex.cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (cyclesImageSingleHom S).hom) 0 ≫ unitClassHom F S.X₃

/-- The map `R¹F(Z⁰K₁) ⟶ H¹(RF(K₁))` induced by the inclusion of the cycles, read from Mathlib's
`ℕ`-indexed right derived functor. -/
def cyclesRightDerivedOneMap :
    (F.rightDerived 1).obj (HomologicalComplex.shortExactCycles (toSC S) 0).X₁ ⟶
      (DerivedCategory.Plus.homologyFunctor B 1).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj S.X₁)) :=
  (derivedPlusToStandard F 1).inv.app _ ≫ (DerivedCategory.Plus.homologyFunctor B 1).map
    (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (cyclesSingleHom S.X₁)))

/-- The algebra of `imageCycleClass_comp_shortExactBoundary`, with every object and morphism a
variable. -/
private theorem boundary_paste {C : Type*} [Category* C] {p z₃ z k₃ k₁ s₃ s₁ h : C}
    (sc : p ⟶ z₃) (cm : z₃ ⟶ z) (u : z ⟶ k₃) (δ : k₃ ⟶ k₁) (u' : z₃ ⟶ s₃) (m₃ : s₃ ⟶ k₃)
    (dl : s₃ ⟶ s₁) (m₁ : s₁ ⟶ k₁) (r : p ⟶ h) (d : h ⟶ s₃)
    (hn : u' ≫ m₃ = cm ≫ u) (hb : m₃ ≫ δ = dl ≫ m₁) (h₀ : r ≫ d = sc ≫ u') :
    (sc ≫ cm ≫ u) ≫ δ = r ≫ d ≫ dl ≫ m₁ := by
  rw [Category.assoc, Category.assoc, ← reassoc_of% hn, hb, reassoc_of% h₀]

/-- **The boundary map of a short exact sequence of complexes on the classes of the image of the
cycles**: the class of a section of `I` followed by the boundary map `H⁰(RF K₃) ⟶ H¹(RF K₁)` is
`toRightDerivedZero` of `I`, the connecting morphism of the sequence of cycles, and the map induced
by the inclusion of the cycles `Z⁰K₁[0] ⟶ K₁`. -/
theorem imageCycleClass_comp_shortExactBoundary :
    imageCycleClass F S ≫ shortExactBoundary F S hS 0 1 rfl =
      F.toRightDerivedZero.app _ ≫ (derivedPlusToStandard F 0).inv.app _ ≫
        Stacks.Cohomology.CechDelta.rightDerivedPlusδ F
          (HomologicalComplex.shortExactCycles_shortExact 0 hS) 0 ≫
        (DerivedCategory.Plus.homologyFunctor B 1).map
          (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (cyclesSingleHom S.X₁))) :=
  boundary_paste _ _ _ _ _ _ _ _ _ _ (unitClassHom_naturality F (cyclesImageSingleHom S))
    (homology_map_cyclesSingleMap_comp_shortExactBoundary F hS)
    (toRightDerivedZero_comp_derivedPlusToStandard_inv_eq_unitClassHom F _)

/-- Inserting an identity, with every object and morphism a variable. -/
private theorem insert_id {C : Type*} [Category* C] {p q r s t u : C} (x : p ⟶ q) (y : q ⟶ r)
    (z : r ⟶ s) (h : s ⟶ t) (h' : t ⟶ s) (w : s ⟶ u) (hh : h ≫ h' = 𝟙 _) :
    x ≫ y ≫ z ≫ w = x ≫ y ≫ z ≫ h ≫ h' ≫ w := by
  rw [reassoc_of% hh]

/-- `imageCycleClass_comp_shortExactBoundary`, through Mathlib's `ℕ`-indexed `R¹F`. -/
theorem imageCycleClass_comp_shortExactBoundary_eq :
    imageCycleClass F S ≫ shortExactBoundary F S hS 0 1 rfl =
      F.toRightDerivedZero.app _ ≫ (derivedPlusToStandard F 0).inv.app _ ≫
        Stacks.Cohomology.CechDelta.rightDerivedPlusδ F
          (HomologicalComplex.shortExactCycles_shortExact 0 hS) 0 ≫
        (derivedPlusToStandard F 1).hom.app _ ≫ cyclesRightDerivedOneMap F S := by
  rw [imageCycleClass_comp_shortExactBoundary, cyclesRightDerivedOneMap]
  exact insert_id _ _ _ _ _ _ (Iso.hom_inv_id_app _ _)

end Cycles

end Stacks.DerivedIndexing

end
