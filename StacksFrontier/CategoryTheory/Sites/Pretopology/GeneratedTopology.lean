module

public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence

/-!
# Comparing separatedness conditions along a morphism of families

Stacks tag 0G1K: if a family `{V_j ⟶ U}` refines a family `{U_i ⟶ U}` and the map
`F(U) ⟶ ∏_j F(V_j)` is injective, then so is `F(U) ⟶ ∏_i F(U_i)`.

## The refinement is Mathlib's `PreZeroHypercover.Hom`

0G1K's hypothesis is a morphism of families with fixed target over the identity of `U` —
a map `α : J → I` together with morphisms `f_j : V_j ⟶ U_{α j}` commuting over `U`. That is
exactly `PreZeroHypercover.Hom`, which `ZeroOver` records as Stacks 00VT (2); the three pieces
of data are its `s₀`, `h₀` and `w₀`. Taking the refinement as a single argument is what makes
the proof one rewrite: `w₀` *is* the factorisation the argument needs.
-/

@[expose] public section

namespace CategoryTheory.PreZeroHypercover

universe w w' t v u

variable {C : Type u} [Category.{v} C] {U : C}

/-- **Stacks 0G1K.** Let `𝒰 = {U_i ⟶ U}` and `𝒱 = {V_j ⟶ U}` be families of morphisms with
fixed target `U`, and let `φ` exhibit `𝒱` as a refinement of `𝒰`. If `F(U) ⟶ ∏_j F(V_j)` is
injective, then so is `F(U) ⟶ ∏_i F(U_i)`: each `U_i` is reached from some `V_j` through `φ`,
so agreeing on all the `V_j` already forces agreement on all the `U_i`. -/
@[stacks 0G1K]
theorem injective_of_hom (𝒰 : PreZeroHypercover.{w} U) (𝒱 : PreZeroHypercover.{w'} U)
    (φ : 𝒱.Hom 𝒰) (F : Cᵒᵖ ⥤ Type t)
    (hinj : Function.Injective
      fun (x : F.obj (Opposite.op U)) (j : 𝒱.I₀) => F.map (𝒱.f j).op x) :
    Function.Injective
      fun (x : F.obj (Opposite.op U)) (i : 𝒰.I₀) => F.map (𝒰.f i).op x := by
  intro x y hxy
  refine hinj (funext fun j => ?_)
  -- Rewrite `F.map (𝒱.f j).op` using the factorisation `𝒱.f j = φ.h₀ j ≫ 𝒰.f (φ.s₀ j)`.
  simp only [← φ.w₀, op_comp, F.map_comp, types_comp_apply]
  exact congrArg (F.map (φ.h₀ j).op) (congrFun hxy (φ.s₀ j))

end CategoryTheory.PreZeroHypercover
