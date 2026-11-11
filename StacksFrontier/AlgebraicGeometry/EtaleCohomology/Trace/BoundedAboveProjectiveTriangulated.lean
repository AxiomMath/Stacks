module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TotalDerivedFunctors
import StacksCore.Tactic.StacksAttribute

/-!
# `D⁻(A) ≅ K⁻(P)` as triangulated categories

Let `A` be an abelian category and let `K⁻(P)` be the full subcategory of the homotopy
category `K(A)` on the bounded above complexes of projective objects. This file shows that
`K⁻(P)` is a triangulated subcategory of `K(A)`, that the canonical functor
`K⁻(P) ⥤ D⁻(A)` is a triangulated functor, and, when `A` has enough projectives, that the
equivalence it defines is an equivalence of triangulated categories. This completes part (4)
of [Stacks, Tag 03T6], whose underlying equivalence of categories is
`CategoryTheory.HomotopyCategory.MinusProjective.isEquivalence_toDerivedMinus`.

## Main definitions

* `CategoryTheory.HomotopyCategory.MinusProjective.toDerivedMinusEquivalence`: the
  equivalence `K⁻(P) ≌ D⁻(A)` defined by the canonical functor when `A` has enough
  projectives.

## Main results

* `CategoryTheory.HomotopyCategory.MinusProjective.isEquivalence_toDerivedMinus_and_isTriangulated`:
  the canonical functor `K⁻(P) ⥤ D⁻(A)` is an equivalence and a triangulated functor.
* `CategoryTheory.HomotopyCategory.MinusProjective.isTriangulated_toDerivedMinusEquivalence`:
  the equivalence `K⁻(P) ≌ D⁻(A)` is triangulated: its functor and its quasi-inverse are
  triangulated functors.

## Implementation notes

As in the injective case,
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BoundedBelowInjectiveTriangulated`, the
property `minusProjective` is a triangulated subcategory: it contains zero, is stable under
shifts, and the mapping cone of a map between bounded above complexes of projectives is again
one, its terms being biproducts of projectives. The canonical functor is a lift of the
triangulated functor `DerivedCategory.Qh`, and the shift compatibility of the quasi-inverse
is the one induced by `Equivalence.commShiftInverse`.

## References

* [Stacks Project, Tag 03T6](https://stacks.math.columbia.edu/tag/03T6)
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe w v u

namespace HomotopyCategory

variable (A : Type u) [Category.{v} A] [Abelian A]

open Limits ZeroObject Pretriangulated in
instance : (minusProjective A).ContainsZero where
  exists_zero :=
    ⟨(HomotopyCategory.quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _),
      ⟨0, (inferInstance : (0 : CochainComplex A ℤ).IsStrictlyLE 0)⟩, fun i ↦
        ((HomologicalComplex.eval A (ComplexShape.up ℤ) i).map_isZero (isZero_zero _)).projective⟩

instance : (minusProjective A).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        obtain ⟨⟨q, hq⟩, hproj⟩ := hK
        have : K.IsStrictlyLE q := hq
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj]
        exact ⟨⟨q - n, K.isStrictlyLE_shift q n (q - n) (by lia)⟩, fun i ↦ hproj (i + n)⟩ }

open Pretriangulated in
instance : (minusProjective A).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨⟨n₁, _⟩, h₁⟩ := h₁
    obtain ⟨⟨n₂, _⟩, h₂⟩ := h₂
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ :=
      (HomotopyCategory.quotient _ _).map_surjective T.mor₁
    refine ⟨_, ⟨⟨max (n₁ - 1) n₂, ?_⟩, fun i ↦ ?_⟩,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
        (HomotopyCategory.mappingCone_triangleh_distinguished f) (Iso.refl _) (Iso.refl _)
        ((Category.comp_id _).trans (hf.symm.trans (Category.id_comp _).symm)))⟩⟩
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact (CochainComplex.mappingCone.isZero_X_iff f i).2
        ⟨CochainComplex.isZero_of_isStrictlyLE T.obj₁.as n₁ _ (by lia),
          CochainComplex.isZero_of_isStrictlyLE T.obj₂.as n₂ _ (by lia)⟩
    · have := h₁ (i + 1)
      have := h₂ i
      exact Projective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl).symm
        inferInstance

/-- The bounded above complexes of projective objects form a triangulated subcategory of the
homotopy category: they contain zero, are stable under shifts, and are closed under mapping
cones. -/
instance : (minusProjective A).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

namespace MinusProjective

variable [HasDerivedCategory.{w} A]

/-- The canonical functor `K⁻(Proj A) ⥤ D⁻(A)` commutes with the shift functors. -/
noncomputable instance : (toDerivedMinus A).CommShift ℤ := by
  dsimp only [toDerivedMinus]
  infer_instance

/-- The canonical functor `K⁻(Proj A) ⥤ D⁻(A)` is a triangulated functor. -/
instance : (toDerivedMinus A).IsTriangulated := by
  dsimp only [toDerivedMinus]
  infer_instance

/-- **Stacks 03T6, part (4), with its triangulated structure.** If `A` has enough projectives
and `P ⊆ A` is the additive subcategory of projectives, then `D⁻(A) ≅ K⁻(P)` as triangulated
categories: the canonical functor `K⁻(P) ⥤ D⁻(A)` is an equivalence of categories and a
triangulated functor. -/
@[stacks 03T6 "(4) in full: D⁻(A) ≅ K⁻(P) as triangulated categories"]
theorem isEquivalence_toDerivedMinus_and_isTriangulated [EnoughProjectives A] :
    (toDerivedMinus A).IsEquivalence ∧ (toDerivedMinus A).IsTriangulated :=
  ⟨isEquivalence_toDerivedMinus A, inferInstance⟩

variable [EnoughProjectives A]

/-- The equivalence `K⁻(Proj A) ≌ D⁻(A)` whose functor is the canonical functor
`toDerivedMinus`. -/
def toDerivedMinusEquivalence : MinusProjective A ≌ DerivedCategory.Minus A :=
  have := isEquivalence_toDerivedMinus A
  (toDerivedMinus A).asEquivalence

@[simp]
lemma toDerivedMinusEquivalence_functor :
    (toDerivedMinusEquivalence A).functor = toDerivedMinus A := rfl

/-- The shift compatibility of the functor of `toDerivedMinusEquivalence`, that of
`toDerivedMinus`. -/
noncomputable instance : (toDerivedMinusEquivalence A).functor.CommShift ℤ :=
  inferInstanceAs ((toDerivedMinus A).CommShift ℤ)

/-- The shift compatibility of the quasi-inverse of `toDerivedMinusEquivalence`, induced from
that of its functor. -/
noncomputable instance : (toDerivedMinusEquivalence A).inverse.CommShift ℤ :=
  (toDerivedMinusEquivalence A).commShiftInverse ℤ

instance : (toDerivedMinusEquivalence A).CommShift ℤ :=
  (toDerivedMinusEquivalence A).commShift_of_functor ℤ

/-- **Stacks 03T6, part (4), as an equivalence of triangulated categories.** If `A` has enough
projectives, the equivalence `K⁻(Proj A) ≌ D⁻(A)` given by the canonical functor, with the
shift compatibility on its quasi-inverse induced from that of the functor, is a triangulated
equivalence: both it and its quasi-inverse are triangulated functors. -/
@[stacks 03T6 "(4): K⁻(P) ≌ D⁻(A) is an equivalence of triangulated categories"]
theorem isTriangulated_toDerivedMinusEquivalence :
    (toDerivedMinusEquivalence A).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (inferInstanceAs (toDerivedMinus A).IsTriangulated)

end MinusProjective

end HomotopyCategory

end CategoryTheory
