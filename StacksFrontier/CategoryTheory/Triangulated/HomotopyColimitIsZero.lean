module

public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit

/-!
# A derived colimit of zero objects is zero

If every term `Kₙ` of a system in a pre-triangulated category is zero, so is every derived
colimit `K = hocolim Kₙ`: the direct sum `⊕ Kₙ` is zero, and the defining triangle
`⊕ Kₙ ⟶ ⊕ Kₙ ⟶ K ⟶ (⊕ Kₙ)⟦1⟧` then has its first map an isomorphism.

## Main results

* `CategoryTheory.Pretriangulated.IsHomotopyColimit.isZero_of_forall_isZero`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Pretriangulated

open Limits

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A derived colimit of a system of zero objects is zero.** -/
theorem IsHomotopyColimit.isZero_of_forall_isZero {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    (h : IsHomotopyColimit F K) (hF : ∀ n, IsZero (F.obj n)) : IsZero K := by
  obtain ⟨p, q, hT⟩ := h
  have hS : IsZero (∐ F.obj) :=
    (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun n => (hF n).eq_of_src _ _)
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).2 ⟨0, hS.eq_of_src _ _, hS.eq_of_src _ _⟩

end CategoryTheory.Pretriangulated
