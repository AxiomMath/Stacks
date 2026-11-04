module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective

/-!
# Uniqueness of the reduction of an fppf sheaf

## Main results

* `AlgebraicGeometry.FormalSpace.IsReduction.nonempty_iso`: two reductions of the same fppf
  sheaf on the big fppf site of `S` are isomorphic.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace IsReduction

variable {B S hS}
variable {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}

/-- Two reductions of the same fppf sheaf on the big fppf site of `S` are isomorphic. -/
theorem nonempty_iso {Xred' : FppfSheaf B S hS} {i' : Xred' ⟶ X}
    (h : IsReduction B S hS X Xred i) (h' : IsReduction B S hS X Xred' i') :
    Nonempty (Xred ≅ Xred') := by
  obtain ⟨g, hg, -⟩ := h'.universal Xred h.algebraic h.reduced i
  obtain ⟨g', hg', -⟩ := h.universal Xred' h'.algebraic h'.reduced i'
  obtain ⟨k, -, hu⟩ := h.universal Xred h.algebraic h.reduced i
  obtain ⟨k', -, hu'⟩ := h'.universal Xred' h'.algebraic h'.reduced i'
  refine ⟨⟨g, g', ?_, ?_⟩⟩
  · exact (hu (g ≫ g') (by simp only [Category.assoc, hg', hg])).trans
      (hu (𝟙 Xred) (Category.id_comp i)).symm
  · exact (hu' (g' ≫ g) (by simp only [Category.assoc, hg, hg'])).trans
      (hu' (𝟙 Xred') (Category.id_comp i')).symm

end IsReduction

variable {B S hS}

end AlgebraicGeometry.FormalSpace

end
