module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFullyFaithful

/-!
# A weak triangulated generator detects invertibility

A morphism `b : K ⟶ X` of a pretriangulated category is invertible as soon as postcomposition
with `b` is bijective on morphisms out of every shift of every object of a weak triangulated
generator `G`. `CategoryTheory.ObjectProperty.IsWeakTriangulatedGenerator.isIso_of_bijective_comp`
is the case of a generator consisting of one object.

## Main results

* `CategoryTheory.ObjectProperty.IsWeakTriangulatedGenerator.isIso_of_bijective_comp_shiftClosure`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

namespace CategoryTheory

universe v₂ u₂

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A weak generator detects invertibility.** Let `E` be a weak generator of a pretriangulated
category `D` and let `b : K ⟶ X` be a morphism such that postcomposition with `b` is bijective
from `P ⟶ K` onto `P ⟶ X` for every object `P` isomorphic to a translate of `E`. Then `b` is an
isomorphism.

Complete `b` to a distinguished triangle `K → X → Z → K[1]`. A morphism `ξ : P ⟶ Z` out of a
translate of `E` is annihilated by `Z ⟶ K[1]`, because the composite `P ⟶ K[1] ⟶ X[1]` vanishes
and postcomposition with `b[1]` is injective on morphisms out of `P` — being, after translating
by `-1`, postcomposition with `b` on morphisms out of `P[-1]`, again a translate of `E`. So `ξ`
factors through `X`, hence through `b`, hence through the zero composite `K ⟶ X ⟶ Z`. Thus `Z`
receives only zero morphisms from the translates of `E`, so it vanishes and `b` is invertible. -/
theorem ObjectProperty.IsWeakTriangulatedGenerator.isIso_of_bijective_comp_shiftClosure
    {G : ObjectProperty D}
    (hE : G.IsWeakTriangulatedGenerator) {K X : D} (b : K ⟶ X)
    (h : ∀ ⦃P : D⦄, (G.shiftClosure ℤ) P →
      Function.Bijective (fun f : P ⟶ K => f ≫ b)) :
    IsIso b := by
  obtain ⟨Z, g, k, hT⟩ := distinguished_cocone_triangle b
  have h₁₂ : b ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have h₃₁ : k ≫ b⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have hinj : ∀ ⦃P : D⦄, (G.shiftClosure ℤ) P →
      ∀ ζ : P ⟶ K⟦(1 : ℤ)⟧, ζ ≫ b⟦(1 : ℤ)⟧' = 0 → ζ = 0 := by
    intro P hP ζ hζ
    have e : (P⟦(-1 : ℤ)⟧ : D)⟦(1 : ℤ)⟧ ≅ P :=
      (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by simp)).app P
    obtain ⟨u, hu⟩ : ∃ u : (P⟦(-1 : ℤ)⟧ : D) ⟶ K, u⟦(1 : ℤ)⟧' = e.hom ≫ ζ :=
      ⟨(shiftFunctor D (1 : ℤ)).preimage _, (shiftFunctor D (1 : ℤ)).map_preimage _⟩
    have hub : u ≫ b = 0 := by
      refine (shiftFunctor D (1 : ℤ)).map_injective ?_
      rw [Functor.map_comp, hu, Category.assoc, hζ, Limits.comp_zero,
        (shiftFunctor D (1 : ℤ)).map_zero]
    have hu0 : u = 0 :=
      (h ((G.shiftClosure ℤ).le_shift (-1 : ℤ) _ hP)).1
        (by simpa using hub)
    rw [← cancel_epi e.hom, Limits.comp_zero, ← hu, hu0,
      (shiftFunctor D (1 : ℤ)).map_zero]
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hE Z fun {P} ξ hP => ?_)
  have hξk : ξ ≫ k = 0 := by
    refine hinj hP _ ?_
    rw [Category.assoc, h₃₁, Limits.comp_zero]
  obtain ⟨η, hη⟩ := Triangle.coyoneda_exact₃ _ hT ξ hξk
  obtain ⟨μ, hμ⟩ := (h hP).2 η
  have hηg : η ≫ g = 0 := by rw [← hμ]; exact (Category.assoc μ b g).trans (by rw [h₁₂, comp_zero])
  exact hη.trans hηg

end CategoryTheory

end
