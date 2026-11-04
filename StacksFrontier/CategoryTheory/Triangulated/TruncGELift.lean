module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Lifting a morphism into a truncation back to the object

Let `t` be a t-structure on a pretriangulated category `C`, let `n` be an integer and let `E` be
an object of `C`. A morphism `A ⟶ τ^{≥n}E` lifts along the canonical `E ⟶ τ^{≥n}E` as soon as
the group `A ⟶ (τ^{<n}E)⟦1⟧` is trivial: the truncation triangle
`τ^{<n}E ⟶ E ⟶ τ^{≥n}E ⟶ (τ^{<n}E)⟦1⟧` is distinguished, and the only obstruction to the lift is
the composite of the morphism with its connecting map.

## Main results

* `CategoryTheory.Triangulated.TStructure.exists_lift_truncGEπ_of_subsingleton`: the lift, from
  the triviality of the obstruction group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ p : ℤ, (shiftFunctor C p).Additive] [Pretriangulated C] (t : TStructure C)

/-- **A morphism into `τ^{≥n}E` lifts to `E` once the obstruction group is trivial.** If every
morphism `A ⟶ (τ^{<n}E)⟦1⟧` is zero, then every morphism `g : A ⟶ τ^{≥n}E` is `f ≫ π` for some
`f : A ⟶ E`, `π` being the canonical map `E ⟶ τ^{≥n}E`. -/
theorem exists_lift_truncGEπ_of_subsingleton (n : ℤ) (E A : C)
    (g : A ⟶ (t.truncGE n).obj E)
    (h : Subsingleton (A ⟶ ((t.truncLT n).obj E)⟦(1 : ℤ)⟧)) :
    ∃ f : A ⟶ E, f ≫ (t.truncGEπ n).app E = g := by
  obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₃ ((t.triangleLTGE n).obj E)
    (t.triangleLTGE_distinguished n E) g (@Subsingleton.elim _ h _ 0)
  exact ⟨f, hf.symm⟩

end CategoryTheory.Triangulated.TStructure

end
