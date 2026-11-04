module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import StacksCore.Tactic.StacksAttribute

/-!
# Adjoints of monomorphisms in the Gabriel--Popescu adjunction

Let `C` be a Grothendieck abelian category, let `G` be a separator of `C`, and consider the
Gabriel--Popescu adjunction `- ⊗ G ⊣ Hom(G, -)` between modules over `(End G)ᵐᵒᵖ` and `C`. If a
module map `f : M ⟶ Hom(G, A)` is injective, then its adjoint `M ⊗ G ⟶ A` is a monomorphism:
the left adjoint preserves monomorphisms and the counit of the adjunction is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian

universe v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

/-- Let `G` be a separator of a Grothendieck abelian category. If a map of
`(End G)ᵐᵒᵖ`-modules `f : M ⟶ Hom(G, A)` is a monomorphism, equivalently injective, then the
map `M ⊗ G ⟶ A` adjoint to it is a monomorphism as well. -/
@[stacks 0F5T]
theorem mono_homEquiv_symm_of_mono (G : C) (hG : IsSeparator G)
    {M : ModuleCat (End G)ᵐᵒᵖ} {A : C} (f : M ⟶ (preadditiveCoyonedaObj G).obj A) (hf : Mono f) :
    Mono (((tensorObjPreadditiveCoyonedaObjAdjunction G).homEquiv M A).symm f) := by
  have : (preadditiveCoyonedaObj G).Full := GabrielPopescu.full G hG
  have : (preadditiveCoyonedaObj G).Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj G).1 hG
  have := GabrielPopescu.preservesInjectiveObjects G hG
  have : (tensorObj G).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
      (tensorObjPreadditiveCoyonedaObjAdjunction G)
  rw [Adjunction.homEquiv_counit]
  exact mono_comp _ _

end Stacks.Injectives
