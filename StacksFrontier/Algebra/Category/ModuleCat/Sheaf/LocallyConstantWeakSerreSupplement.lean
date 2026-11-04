module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre

/-!
# Supplement to `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyConstantWeakSerre`

Declarations used by the pro-étale comparison of Stacks 09B1 and 09A6, kept in their own module
so that `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre` is unchanged.
-/


@[expose] public section
open CategoryTheory Limits

namespace Stacks.ConstantSheaf
universe v u w r
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type r) [Ring Λ]

/-- A zero sheaf of `Λ`-modules is locally constant of finite type: on every object it is the
constant sheaf attached to the zero module. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_of_isZero
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    {F : Sheaf J (ModuleCat.{max u v w} Λ)} (hF : IsZero F) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ F := by
  intro U
  refine ⟨PUnit, fun _ ↦ U, fun _ ↦ 𝟙 U, ?_, fun _ ↦ ?_⟩
  · rw [Sieve.ofArrows, Presieve.ofArrows_pUnit,
      Sieve.generate_of_contains_isSplitEpi (𝟙 U) (Presieve.singleton_self _)]
    exact J.top_mem U
  · refine ⟨ModuleCat.of Λ PUnit, ⟨⊥, ?_⟩, ⟨IsZero.iso ?_ ?_⟩⟩
    · exact Subsingleton.elim _ _
    · exact Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton _)
    · exact Functor.map_isZero _ hF


end Stacks.ConstantSheaf
end
