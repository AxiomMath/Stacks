module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BoundedBelowInjectiveEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# `D⁺(A) ≅ K⁺(I)` as triangulated categories

Let `A` be an abelian category and let `K⁺(I)` be the full subcategory of the homotopy
category `K(A)` on the bounded below complexes of injective objects. This file shows that
`K⁺(I)` is a triangulated subcategory of `K(A)`, that the canonical functor
`K⁺(I) ⥤ D⁺(A)` is a triangulated functor, and, when `A` has enough injectives, that the
equivalence it defines is an equivalence of triangulated categories. This completes part (3)
of [Stacks, Tag 03T6], whose underlying equivalence of categories is
`CategoryTheory.HomotopyCategory.PlusInjective.isEquivalence_toDerivedPlus`.

## Main definitions

* `CategoryTheory.HomotopyCategory.PlusInjective.toDerivedPlusEquivalence`: the equivalence
  `K⁺(I) ≌ D⁺(A)` defined by the canonical functor when `A` has enough injectives.

## Main results

* `CategoryTheory.HomotopyCategory.PlusInjective.isEquivalence_toDerivedPlus_and_isTriangulated`:
  the canonical functor `K⁺(I) ⥤ D⁺(A)` is an equivalence and a triangulated functor.
* `CategoryTheory.HomotopyCategory.PlusInjective.isTriangulated_toDerivedPlusEquivalence`:
  the equivalence `K⁺(I) ≌ D⁺(A)` is triangulated: its functor and its quasi-inverse are
  triangulated functors.

## Implementation notes

The property `plusInjective` is a triangulated subcategory (`ObjectProperty.IsTriangulated`):
it contains zero, is stable under shifts, and the mapping cone of a map between bounded below
complexes of injectives is again one, its terms being biproducts of injectives. So `K⁺(I)`
carries Mathlib's induced pretriangulated structure, in which a triangle is distinguished
when its image in `K(A)` is. The canonical functor is a lift of the triangulated functor
`DerivedCategory.Qh`, hence commutes with shifts and preserves distinguished triangles. The
shift compatibility of the quasi-inverse is the one induced by `Equivalence.commShiftInverse`.

## References

* [Stacks Project, Tag 03T6](https://stacks.math.columbia.edu/tag/03T6)
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe w v u

namespace HomotopyCategory

variable (A : Type u) [Category.{v} A] [Abelian A]

open Limits ZeroObject Pretriangulated

instance : (plusInjective A).ContainsZero where
  exists_zero :=
    ⟨(HomotopyCategory.quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _),
      ⟨0, (inferInstance : (0 : CochainComplex A ℤ).IsStrictlyGE 0)⟩, fun i ↦
        ((HomologicalComplex.eval A (ComplexShape.up ℤ) i).map_isZero (isZero_zero _)).injective⟩

instance : (plusInjective A).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        obtain ⟨⟨q, hq⟩, hinj⟩ := hK
        have : K.IsStrictlyGE q := hq
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj]
        exact ⟨⟨q - n, K.isStrictlyGE_shift q n (q - n) (by lia)⟩, fun i ↦ hinj (i + n)⟩ }

instance : (plusInjective A).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨⟨n₁, _⟩, h₁⟩ := h₁
    obtain ⟨⟨n₂, _⟩, h₂⟩ := h₂
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ := (HomotopyCategory.quotient _ _).map_surjective T.mor₁
    refine ⟨_, ⟨⟨min (n₁ - 1) n₂, CochainComplex.isStrictlyGE_mappingCone f n₁ n₂ _
        (by simp) (by simp)⟩, fun i ↦ ?_⟩,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
        (HomotopyCategory.mappingCone_triangleh_distinguished f) (Iso.refl _) (Iso.refl _) ?_)⟩⟩
    · have := h₁ (i + 1)
      have := h₂ i
      exact Injective.of_iso
        (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl).symm inferInstance
    · exact (Category.comp_id _).trans (hf.symm.trans (Category.id_comp _).symm)

/-- The bounded below complexes of injective objects form a triangulated subcategory of the
homotopy category: they contain zero, are stable under shifts, and are closed under mapping
cones. -/
instance : (plusInjective A).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

namespace PlusInjective

variable [HasDerivedCategory.{w} A]

/-- The canonical functor `K⁺(I) ⥤ D⁺(A)` commutes with the shift functors. -/
noncomputable instance : (toDerivedPlus A).CommShift ℤ := by
  dsimp only [toDerivedPlus]
  infer_instance

/-- The canonical functor `K⁺(I) ⥤ D⁺(A)` is a triangulated functor. -/
instance : (toDerivedPlus A).IsTriangulated := by
  dsimp only [toDerivedPlus]
  infer_instance

/-- **Stacks 03T6, part (3), with its triangulated structure.** If `A` has enough injectives
and `I ⊆ A` is the additive subcategory of injectives, then `D⁺(A) ≅ K⁺(I)` as triangulated
categories: the canonical functor `K⁺(I) ⥤ D⁺(A)` is an equivalence of categories and a
triangulated functor. -/
@[stacks 03T6 "(3) in full: D⁺(A) ≅ K⁺(I) as triangulated categories"]
theorem isEquivalence_toDerivedPlus_and_isTriangulated [EnoughInjectives A] :
    (toDerivedPlus A).IsEquivalence ∧ (toDerivedPlus A).IsTriangulated :=
  ⟨isEquivalence_toDerivedPlus A, inferInstance⟩

variable [EnoughInjectives A]

/-- The equivalence `K⁺(I) ≌ D⁺(A)` whose functor is the canonical functor `toDerivedPlus`. -/
def toDerivedPlusEquivalence : PlusInjective A ≌ DerivedCategory.Plus A :=
  have := isEquivalence_toDerivedPlus A
  (toDerivedPlus A).asEquivalence

@[simp]
lemma toDerivedPlusEquivalence_functor :
    (toDerivedPlusEquivalence A).functor = toDerivedPlus A := rfl

/-- The shift compatibility of the functor of `toDerivedPlusEquivalence`, that of
`toDerivedPlus`. -/
noncomputable instance : (toDerivedPlusEquivalence A).functor.CommShift ℤ :=
  inferInstanceAs ((toDerivedPlus A).CommShift ℤ)

/-- The shift compatibility of the quasi-inverse of `toDerivedPlusEquivalence`, induced from
that of its functor. -/
noncomputable instance : (toDerivedPlusEquivalence A).inverse.CommShift ℤ :=
  (toDerivedPlusEquivalence A).commShiftInverse ℤ

instance : (toDerivedPlusEquivalence A).CommShift ℤ :=
  (toDerivedPlusEquivalence A).commShift_of_functor ℤ

/-- **Stacks 03T6, part (3), as an equivalence of triangulated categories.** If `A` has enough
injectives, the equivalence `K⁺(I) ≌ D⁺(A)` given by the canonical functor, with the shift
compatibility on its quasi-inverse induced from that of the functor, is a triangulated
equivalence: both it and its quasi-inverse are triangulated functors. -/
@[stacks 03T6 "(3): K⁺(I) ≌ D⁺(A) is an equivalence of triangulated categories"]
theorem isTriangulated_toDerivedPlusEquivalence :
    (toDerivedPlusEquivalence A).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (inferInstanceAs (toDerivedPlus A).IsTriangulated)

end PlusInjective

end HomotopyCategory

end CategoryTheory
