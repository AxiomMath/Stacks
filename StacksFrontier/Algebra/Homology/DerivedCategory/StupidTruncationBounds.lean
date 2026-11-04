module

public import StacksFrontier.Algebra.Homology.DerivedCategory.StupidTruncationTriangle
public import StacksFrontier.Homology.Tor.ExtremalDegrees

/-!
# Cohomological bounds of an exact functor on a bounded complex, read off its terms

Let `F : D(C) → D(D)` be an exact functor and `K` a bounded complex of objects of `C`. If `F`
carries each term `Kⁱ[0]` into `D^{≥ b - i}`, respectively `D^{≤ b - i}`, then `F(K)` lies in
`D^{≥ b}`, respectively `D^{≤ b}`. This is the induction along the stupid filtration of `K`;
unlike `StacksDraft.ExtremalDegrees.isGE_map_of_homology` it asks for the terms of `K` rather
than its cohomology objects.

## Main results

* `StacksDraft.ExtremalDegrees.isGE_map_Q_of_terms`
* `StacksDraft.ExtremalDegrees.isLE_map_Q_of_terms`
* `StacksDraft.ExtremalDegrees.prop_map_Q_of_terms`: the same for membership in a triangulated
  subcategory.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.ExtremalDegrees

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{w'} D] [Abelian D]

/-- The induction along the stupid filtration for `F (Q K)`, with the property checked only at
the nonzero terms `Kⁱ[-i]`. -/
private theorem property_map_Q_of_terms (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated] (P : ObjectProperty (DerivedCategory D))
    [P.IsClosedUnderIsomorphisms] (hzero : ∀ X, IsZero X → P X)
    (hext : ∀ T ∈ distTriang (DerivedCategory D), P T.obj₁ → P T.obj₃ → P T.obj₂)
    (K : CochainComplex C ℤ) (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (h : ∀ i : ℤ, ¬ IsZero (K.X i) → P (F.obj ((singleFunctor C i).obj (K.X i)))) :
    P (F.obj (Q.obj K)) := by
  refine Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex_of_distTriang
    (fun A => P (F.obj A)) (fun e => P.prop_of_iso (F.mapIso e))
    (fun A hA => hzero _ (F.map_isZero hA)) (fun T hT => hext _ (F.map_distinguished _ hT)) K hK
    fun i => ?_
  by_cases hi : IsZero (K.X i)
  · exact hzero _ (F.map_isZero ((singleFunctor C i).map_isZero hi))
  · exact h i hi

/-- **The lower bound from the terms.** For a bounded complex `K`, an exact functor carrying
each nonzero `Kⁱ[0]` into `D^{≥ b - i}` carries `K` into `D^{≥ b}`. -/
theorem isGE_map_Q_of_terms (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    [F.IsTriangulated] (K : CochainComplex C ℤ) (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) (b : ℤ)
    (h : ∀ i : ℤ, ¬ IsZero (K.X i) → (F.obj ((singleFunctor C 0).obj (K.X i))).IsGE (b - i)) :
    (F.obj (Q.obj K)).IsGE b := by
  refine ⟨property_map_Q_of_terms F (TStructure.t.ge b)
    (fun A hA => (TStructure.t.isGE_of_isZero hA b).ge)
    (fun T hT h₁ h₃ => (TStructure.t.isGE₂ T hT b ⟨h₁⟩ ⟨h₃⟩).ge) K hK fun i hi => ?_⟩
  have := h i hi
  have := TStructure.t.isGE_shift (F.obj ((singleFunctor C 0).obj (K.X i))) (b - i) (-i) b
    (by omega)
  exact (TStructure.t.isGE_of_iso (mapSingleShiftIso F (K.X i) i).symm b).ge

/-- **The upper bound from the terms.** For a bounded complex `K`, an exact functor carrying
each nonzero `Kⁱ[0]` into `D^{≤ b - i}` carries `K` into `D^{≤ b}`. -/
theorem isLE_map_Q_of_terms (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    [F.IsTriangulated] (K : CochainComplex C ℤ) (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) (b : ℤ)
    (h : ∀ i : ℤ, ¬ IsZero (K.X i) → (F.obj ((singleFunctor C 0).obj (K.X i))).IsLE (b - i)) :
    (F.obj (Q.obj K)).IsLE b := by
  refine ⟨property_map_Q_of_terms F (TStructure.t.le b)
    (fun A hA => (TStructure.t.isLE_of_isZero hA b).le)
    (fun T hT h₁ h₃ => (TStructure.t.isLE₂ T hT b ⟨h₁⟩ ⟨h₃⟩).le) K hK fun i hi => ?_⟩
  have := h i hi
  have := TStructure.t.isLE_shift (F.obj ((singleFunctor C 0).obj (K.X i))) (b - i) (-i) b
    (by omega)
  exact (TStructure.t.isLE_of_iso (mapSingleShiftIso F (K.X i) i).symm b).le

/-- **Membership in a triangulated subcategory from the terms.** For a bounded complex `K`, an
exact functor carrying each nonzero `Kⁱ[0]` into a triangulated subcategory `P` carries `K` into
`P`. -/
theorem prop_map_Q_of_terms (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    [F.IsTriangulated] (P : ObjectProperty (DerivedCategory D)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (K : CochainComplex C ℤ)
    (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (h : ∀ i : ℤ, ¬ IsZero (K.X i) → P (F.obj ((singleFunctor C 0).obj (K.X i)))) :
    P (F.obj (Q.obj K)) :=
  property_map_Q_of_terms F P (fun _ => P.prop_of_isZero)
    (fun T hT => P.ext_of_isTriangulatedClosed₂ T hT) K hK fun i hi =>
    P.prop_of_iso (mapSingleShiftIso F (K.X i) i).symm (P.le_shift (-i) _ (h i hi))

end StacksDraft.ExtremalDegrees

end
