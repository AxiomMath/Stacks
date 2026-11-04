module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBoundary
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor

/-!
# The boundary maps of a right derived functor on a short exact sequence of complexes

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, `𝒜` with enough injectives,
and let `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` be its right derived functor. A short exact sequence
`0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` of bounded below complexes gives a distinguished triangle of `D⁺(𝒜)`
(`Stacks.Cohomology.RightDerivedBoundary.plusδ`), and hence boundary maps
`Hⁿ(RF K₃) ⟶ Hⁿ⁺¹(RF K₁)`. This file defines them for an arbitrary `F`, proves that they are
natural in the short exact sequence, and identifies them, for a short exact sequence of objects
placed in degree zero, with the connecting morphisms
`Stacks.Cohomology.CechDelta.rightDerivedPlusδ` of the higher right derived functors.

## Main definitions

* `Stacks.Cohomology.RightDerivedBoundary.shortExactBoundary`: the boundary map
  `Hⁿ(RF K₃) ⟶ Hⁿ⁺¹(RF K₁)`.

## Main results

* `Stacks.Cohomology.RightDerivedBoundary.shortExactBoundary_naturality`: naturality in the short
  exact sequence.
* `Stacks.Cohomology.RightDerivedBoundary.shortExactBoundary_single`: for objects placed in degree
  zero it is the connecting morphism of the higher right derived functors.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.RightDerivedBoundary

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]

/-- **The boundary map `Hⁿ(RF K₃) ⟶ Hⁿ⁺¹(RF K₁)`** of a short exact sequence
`0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` of bounded below complexes: the connecting morphism of the long exact
cohomology sequence of the image under `RF` of the distinguished triangle of the sequence. -/
def shortExactBoundary (S : ShortComplex (CochainComplex.Plus A)) (hS : (toSC S).ShortExact)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (DerivedCategory.Plus.homologyFunctor B n₀).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj S.X₃)) ⟶
      (DerivedCategory.Plus.homologyFunctor B n₁).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj S.X₁)) :=
  (DerivedCategory.Plus.homologyFunctor B 0).shiftMap
    (F.rightDerivedFunctorPlus.map (plusδ S hS) ≫
      (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app _) n₀ n₁ (by omega)

/-- **The boundary maps are natural in the short exact sequence.** -/
theorem shortExactBoundary_naturality {S S' : ShortComplex (CochainComplex.Plus A)}
    (hS : (toSC S).ShortExact) (hS' : (toSC S').ShortExact) (φ : S ⟶ S') (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) :
    shortExactBoundary F S hS n₀ n₁ h ≫
        (DerivedCategory.Plus.homologyFunctor B n₁).map
          (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ.τ₁)) =
      (DerivedCategory.Plus.homologyFunctor B n₀).map
          (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ.τ₃)) ≫
        shortExactBoundary F S' hS' n₀ n₁ h := by
  have hnat := Stacks.Cech.Hypercohomology.plusδ_naturality hS hS' φ
  have key : (F.rightDerivedFunctorPlus.map (plusδ S hS) ≫
      (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app _) ≫
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ.τ₁))⟦(1 : ℤ)⟧' =
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ.τ₃) ≫
        F.rightDerivedFunctorPlus.map (plusδ S' hS') ≫
          (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app _ := by
    rw [Category.assoc, ← Functor.commShiftIso_hom_naturality, ← Functor.map_comp_assoc, hnat,
      Functor.map_comp_assoc]
  exact (Functor.shiftMap_comp _ _ _ _ _ _).symm.trans
    ((congrArg (fun g => (DerivedCategory.Plus.homologyFunctor B 0).shiftMap g n₀ n₁ (by omega))
      key).trans (Functor.shiftMap_comp' _ _ _ _ _ _))

section Single

open Stacks.Cohomology.HigherDirectImagePresheaf (singleCochainPlusFunctor)

variable {S : ShortComplex A} (hS : S.ShortExact)

/-- A short complex of objects, placed in degree zero, as a short complex of bounded below
complexes. -/
abbrev singlePlusShortComplex (S : ShortComplex A) : ShortComplex (CochainComplex.Plus A) :=
  ShortComplex.mk (singleCochainPlusFunctor.map S.f) (singleCochainPlusFunctor.map S.g) (by
    rw [← singleCochainPlusFunctor.map_comp, S.zero]
    exact ObjectProperty.hom_ext _ (by
      change (CochainComplex.singleFunctor A 0).map 0 = 0
      exact Functor.map_zero _ _ _))

omit [EnoughInjectives A] in
include hS in
/-- A short exact sequence placed in degree zero is short exact. -/
theorem singlePlusShortComplex_shortExact : (toSC (singlePlusShortComplex S)).ShortExact :=
  hS.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℤ) 0)

/-- **For a short exact sequence of objects placed in degree zero, the boundary map of `RF` is the
connecting morphism of the higher right derived functors**, `rightDerivedPlusδ`. -/
theorem shortExactBoundary_single (i : ℕ) :
    shortExactBoundary F (singlePlusShortComplex S) (singlePlusShortComplex_shortExact hS)
        (i : ℤ) ((i + 1 : ℕ) : ℤ) (by push_cast; ring) =
      CechDelta.rightDerivedPlusδ F hS i :=
  rfl

end Single

end Stacks.Cohomology.RightDerivedBoundary

end
