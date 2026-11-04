module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import StacksCore.Tactic.StacksAttribute

/-!
# The Gabriel--Popescu theorem

Let `C` be a Grothendieck abelian category and let `G` be a separator of `C`. Writing
`R = End G`, the functor `Hom(G, -) : C ⥤ Mod R` to right `R`-modules is fully faithful and
its left adjoint `- ⊗ G` is exact. Consequently every Grothendieck abelian category admits a
fully faithful embedding, with an exact left adjoint, into the category of modules over a
possibly noncommutative ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian

universe v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

add_to_stacks 0F5U "(1) for the constructed functors: `- ⊗ G` is left adjoint to `Hom(G, -)`"
  CategoryTheory.IsGrothendieckAbelian.tensorObjPreadditiveCoyonedaObjAdjunction

/-- Let `G` be a separator of a Grothendieck abelian category `C`. The embedding
`Hom(G, -) : C ⥤ Mod (End G)ᵐᵒᵖ` is fully faithful. -/
@[stacks 0F5U "(2) for the constructed functor `Hom(G, -)`"]
noncomputable def preadditiveCoyonedaObjFullyFaithful (G : C) (hG : IsSeparator G) :
    (preadditiveCoyonedaObj G).FullyFaithful :=
  letI : (preadditiveCoyonedaObj G).Full := GabrielPopescu.full G hG
  letI : (preadditiveCoyonedaObj G).Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj G).1 hG
  .ofFullyFaithful _

/-- Let `G` be a separator of a Grothendieck abelian category `C`. The left adjoint
`- ⊗ G : Mod (End G)ᵐᵒᵖ ⥤ C` of the embedding `Hom(G, -)` is exact: it preserves finite
limits, and it preserves finite colimits because it is a left adjoint. -/
@[stacks 0F5U "(3) for the constructed functor `- ⊗ G`"]
theorem preservesFiniteLimits_and_preservesFiniteColimits_tensorObj (G : C)
    (hG : IsSeparator G) :
    PreservesFiniteLimits (tensorObj G) ∧ PreservesFiniteColimits (tensorObj G) :=
  ⟨GabrielPopescu.preservesFiniteLimits G hG, inferInstance⟩

/-- **The Gabriel--Popescu theorem.** For a Grothendieck abelian category `C` there is a
possibly noncommutative ring `R` together with functors `G : C ⥤ Mod R` and `F : Mod R ⥤ C`
such that `F` is left adjoint to `G`, `G` is fully faithful, and `F` is exact. -/
@[stacks 0F5U]
theorem gabriel_popescu (C : Type u) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] :
    ∃ (R : Type v) (_ : Ring R) (G : C ⥤ ModuleCat.{v} R) (F : ModuleCat.{v} R ⥤ C),
      Nonempty (F ⊣ G) ∧ G.Full ∧ G.Faithful ∧
        PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
  ⟨(End (separator C))ᵐᵒᵖ, inferInstance, preadditiveCoyonedaObj (separator C),
    tensorObj (separator C), ⟨tensorObjPreadditiveCoyonedaObjAdjunction _⟩,
    GabrielPopescu.full _ (isSeparator_separator C),
    (isSeparator_iff_faithful_preadditiveCoyonedaObj _).1 (isSeparator_separator C),
    GabrielPopescu.preservesFiniteLimits _ (isSeparator_separator C), inferInstance⟩

end Stacks.Injectives
