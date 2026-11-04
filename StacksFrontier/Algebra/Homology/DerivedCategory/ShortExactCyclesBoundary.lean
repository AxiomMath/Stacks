module

public import StacksFrontier.Algebra.Homology.ShortExactCycles
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusShortExactBoundary

/-!
# The boundary map of a short exact sequence of complexes on cycles

Let `F : 𝒜 ⥤ ℬ` be an additive functor, `𝒜` with enough injectives, and let
`0 → K₁ → K₂ → K₃ → 0` be a short exact sequence of bounded below complexes. The degree-zero
cycles form a short exact sequence of objects `0 → Z⁰K₁ → Z⁰K₂ → I → 0`, with `I` the image of
`Z⁰K₂` in `Z⁰K₃` (`HomologicalComplex.shortExactCycles`), and the inclusions of the cycles are a
morphism from that sequence, placed in degree zero, to the sequence of complexes. Hence the
boundary map `H⁰(RF K₃) ⟶ H¹(RF K₁)` of the complexes is computed, on the classes coming from `I`,
by the connecting morphism `R⁰F(I) ⟶ R¹F(Z⁰K₁)` of the higher right derived functors.

This is how a boundary map of complexes is evaluated on a global cocycle which lifts locally to
cocycles of the middle term, as in the proof of [Stacks, Tag 0FUG].

## Main definitions

* `Stacks.Cohomology.RightDerivedBoundary.cyclesSingleMap`: the morphism from the sequence of
  degree-zero cycles, placed in degree zero, to the sequence of complexes.

## Main results

* `Stacks.Cohomology.RightDerivedBoundary.homology_map_cyclesSingleMap_comp_shortExactBoundary`:
  the boundary map of the complexes on the classes coming from the cycles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.RightDerivedBoundary

open Stacks.Cohomology.HigherDirectImagePresheaf (singleCochainPlusFunctor)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]

/-- A commutative square through an identification, with every object a variable. -/
private theorem comm_aux {C : Type*} [Category* C] {a b c d e f : C} (x : a ⟶ b) (y : b ⟶ c)
    (z : c ⟶ d) (m : b ⟶ e) (i : e ⟶ f) (i' : f ⟶ e) (w : e ⟶ d) (hi : i ≫ i' = 𝟙 _)
    (h : y ≫ z = m ≫ w) : (x ≫ y) ≫ z = (x ≫ m ≫ i) ≫ i' ≫ w := by
  simp only [Category.assoc, reassoc_of% hi, h]

section Map

variable (S : ShortComplex (CochainComplex.Plus A))

omit [EnoughInjectives A] in
/-- The inclusion of the degree-zero cycles is killed by the differential. -/
theorem iCycles_d_zero (K : CochainComplex.Plus A) :
    ∀ k, (ComplexShape.up ℤ).Rel 0 k → K.obj.iCycles 0 ≫ K.obj.d 0 k = 0 :=
  fun k _ => by simp

/-- The inclusion of the degree-zero cycles of a complex, as a morphism from the cycles placed in
degree zero. -/
def cyclesSingleHom (K : CochainComplex.Plus A) :
    singleCochainPlusFunctor.obj (K.obj.cycles 0) ⟶ K :=
  ObjectProperty.homMk (HomologicalComplex.mkHomFromSingle (K.obj.iCycles 0) (iCycles_d_zero K))

omit [EnoughInjectives A] in
/-- The inclusion of the image of the cycles is killed by the differential. -/
theorem cyclesImageι_iCycles_d_zero :
    ∀ k, (ComplexShape.up ℤ).Rel 0 k →
      (HomologicalComplex.cyclesImageι (toSC S) 0 ≫ S.X₃.obj.iCycles 0) ≫ S.X₃.obj.d 0 k = 0 :=
  fun k _ => by rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]

/-- The inclusion of the image of the cycles of `K₂` in the cycles of `K₃`, followed by the
inclusion of the cycles, as a morphism from that image placed in degree zero. -/
def cyclesImageSingleHom :
    singleCochainPlusFunctor.obj (HomologicalComplex.shortExactCycles (toSC S) 0).X₃ ⟶ S.X₃ :=
  ObjectProperty.homMk (HomologicalComplex.mkHomFromSingle
    (HomologicalComplex.cyclesImageι (toSC S) 0 ≫ S.X₃.obj.iCycles 0)
    (cyclesImageι_iCycles_d_zero S))

omit [EnoughInjectives A] in
/-- The degree-zero component of `cyclesSingleHom`. -/
theorem cyclesSingleHom_f (K : CochainComplex.Plus A) :
    (cyclesSingleHom K).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.obj.cycles 0)).hom ≫
        K.obj.iCycles 0 :=
  HomologicalComplex.mkHomFromSingle_f (K.obj.iCycles 0) (iCycles_d_zero K)

omit [EnoughInjectives A] in
/-- The degree-zero component of `cyclesImageSingleHom`. -/
theorem cyclesImageSingleHom_f :
    (cyclesImageSingleHom S).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (HomologicalComplex.shortExactCycles (toSC S) 0).X₃).hom ≫
        HomologicalComplex.cyclesImageι (toSC S) 0 ≫ S.X₃.obj.iCycles 0 :=
  HomologicalComplex.mkHomFromSingle_f _ (cyclesImageι_iCycles_d_zero S)

omit [EnoughInjectives A] in
/-- The degree-zero component of a morphism of objects placed in degree zero. -/
theorem singleCochainPlusFunctor_map_f {M N : A} (f : M ⟶ N) :
    (singleCochainPlusFunctor.map f).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv :=
  HomologicalComplex.single_map_f_self _ _ _

/-- **The morphism from the sequence of degree-zero cycles, placed in degree zero, to the sequence
of complexes**, given by the inclusions of the cycles. -/
def cyclesSingleMap :
    singlePlusShortComplex (HomologicalComplex.shortExactCycles (toSC S) 0) ⟶ S where
  τ₁ := cyclesSingleHom S.X₁
  τ₂ := cyclesSingleHom S.X₂
  τ₃ := cyclesImageSingleHom S
  comm₁₂ := ObjectProperty.hom_ext _ (HomologicalComplex.from_single_hom_ext (by
    simp only [ObjectProperty.FullSubcategory.comp_hom, HomologicalComplex.comp_f]
    rw [cyclesSingleHom_f, cyclesSingleHom_f, singleCochainPlusFunctor_map_f]
    exact comm_aux _ _ _ _ _ _ _ (Iso.inv_hom_id _)
      (HomologicalComplex.cyclesMap_i (toSC S).f 0).symm))
  comm₂₃ := ObjectProperty.hom_ext _ (HomologicalComplex.from_single_hom_ext (by
    simp only [ObjectProperty.FullSubcategory.comp_hom, HomologicalComplex.comp_f]
    rw [cyclesSingleHom_f, cyclesImageSingleHom_f, singleCochainPlusFunctor_map_f]
    exact comm_aux _ _ _ _ _ _ _ (Iso.inv_hom_id _)
      ((HomologicalComplex.cyclesMap_i (toSC S).g 0).symm.trans
        (HomologicalComplex.shortExactCycles_g_cyclesImageι_assoc (toSC S) 0 _).symm)))

end Map

variable {S : ShortComplex (CochainComplex.Plus A)} (hS : (toSC S).ShortExact)

/-- **The boundary map of a short exact sequence of complexes on the classes coming from the
cycles**: on `R⁰F` of the image `I` of `Z⁰K₂` in `Z⁰K₃`, the boundary map
`H⁰(RF K₃) ⟶ H¹(RF K₁)` is the connecting morphism `R⁰F(I) ⟶ R¹F(Z⁰K₁)` of the sequence of
cycles, followed by the map induced by the inclusion of the cycles. -/
theorem homology_map_cyclesSingleMap_comp_shortExactBoundary :
    (DerivedCategory.Plus.homologyFunctor B 0).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (cyclesImageSingleHom S))) ≫
      shortExactBoundary F S hS 0 1 rfl =
    CechDelta.rightDerivedPlusδ F (HomologicalComplex.shortExactCycles_shortExact 0 hS) 0 ≫
      (DerivedCategory.Plus.homologyFunctor B 1).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (cyclesSingleHom S.X₁))) :=
  (shortExactBoundary_naturality F
    (singlePlusShortComplex_shortExact (HomologicalComplex.shortExactCycles_shortExact 0 hS)) hS
    (cyclesSingleMap S) 0 1 rfl).symm

end Stacks.Cohomology.RightDerivedBoundary

end
