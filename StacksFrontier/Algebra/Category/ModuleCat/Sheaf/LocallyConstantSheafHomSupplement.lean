module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSheafHom

/-!
# Supplement to `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyConstantSheafHom`

Declarations used by the pro-étale comparison of Stacks 09B1 and 09A6, kept in their own module
so that `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSheafHom` is unchanged.
-/


@[expose] public section
open CategoryTheory Opposite
universe u v w x

namespace Stacks.ConstantSheaf
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type w) [CommRing Λ]

section FinitePresentation

/-- Local constancy of finite presentation is invariant under isomorphism: a local trivialization
of `F` is carried to one of `F'` by the restriction functor. -/
instance isClosedUnderIsomorphisms_isFinitePresentationLocallyConstantModuleSheaf :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsFinitePresentationLocallyConstantModuleSheaf.{u, v, w, x} J Λ) where
  of_iso {F F'} e hF U := by
    obtain ⟨I, V, f, hcov, h⟩ := hF U
    refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
    obtain ⟨E, hE, ⟨φ⟩⟩ := h i
    exact ⟨E, hE, ⟨φ ≪≫ (J.overPullback (ModuleCat.{max u v x} Λ) (V i)).mapIso e⟩⟩


end FinitePresentation
end Stacks.ConstantSheaf
end
