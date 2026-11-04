module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of chapter 14 (Simplicial Methods) covered by Mathlib

Each tag registered here is stated in Mathlib; this file only records the correspondence.

Mathlib indexes the face and degeneracy maps by their source: `SimplexCategory.δ j : ⦋n⦌ ⟶ ⦋n + 1⦌`
is the Stacks `δⁿ⁺¹ⱼ`, and `SimplexCategory.σ j : ⦋n + 1⦌ ⟶ ⦋n⦌` is the Stacks `σⁿⱼ`. Mathlib
also writes composition in diagrammatic order (`f ≫ g` is `g ∘ f`). The simplicial identities
below are the Stacks ones after this reindexing.

* Tag 0198: the morphism of complexes `N(U) → s(U)` of a simplicial object of an abelian category.
* Tag 019G: the normalized complex functor `N : Simp(A) ⥤ Ch_{≥0}(A)` is an equivalence.
-/

add_to_stacks 08N9 "the situation: V : A ⥤ S with a left adjoint U : S ⥤ A, as the adjunction U ⊣ V"
  CategoryTheory.Adjunction

add_to_stacks 0165 "δⁿⱼ : [n-1] → [n], the injection skipping j" SimplexCategory.δ
add_to_stacks 0165 "σⁿⱼ : [n+1] → [n], the surjection hitting j twice" SimplexCategory.σ

add_to_stacks 0166 SimplexCategory.morphismProperty_eq_top

add_to_stacks 0167 "(1)" SimplexCategory.δ_comp_δ
add_to_stacks 0167 "(2)" SimplexCategory.δ_comp_σ_of_le
add_to_stacks 0167 "(3), σⱼ ∘ δⱼ = id" SimplexCategory.δ_comp_σ_self
add_to_stacks 0167 "(3), σⱼ ∘ δⱼ₊₁ = id" SimplexCategory.δ_comp_σ_succ
add_to_stacks 0167 "(4)" SimplexCategory.δ_comp_σ_of_gt
add_to_stacks 0167 "(5)" SimplexCategory.σ_comp_σ

add_to_stacks 016A "(1), (3), (4), (5): simplicial objects of C, the functor category Δᵒᵖ ⥤ C \
  (morphisms are natural transformations); (3) is C = abelian groups"
  CategoryTheory.SimplicialObject
add_to_stacks 016A "(2)" SSet

add_to_stacks 016C "(1)" CategoryTheory.SimplicialObject.δ_comp_δ
add_to_stacks 016C "(2)" CategoryTheory.SimplicialObject.δ_comp_σ_of_le
add_to_stacks 016C "(3), dⱼ ∘ sⱼ = id" CategoryTheory.SimplicialObject.δ_comp_σ_self
add_to_stacks 016C "(3), dⱼ₊₁ ∘ sⱼ = id" CategoryTheory.SimplicialObject.δ_comp_σ_succ
add_to_stacks 016C "(4)" CategoryTheory.SimplicialObject.δ_comp_σ_of_gt
add_to_stacks 016C "(5)" CategoryTheory.SimplicialObject.σ_comp_σ

add_to_stacks 016D CategoryTheory.SimplicialObject.const

add_to_stacks 016E CategoryTheory.Arrow.cechNerve

/-! ### Tags 0198 019G

For a simplicial object `U` of an abelian category `A`, the canonical maps `N(U_n) → U_n` give a
morphism of complexes `N(U) → s(U)` (Tag 0198): Mathlib's `AlgebraicTopology.inclusionOfMooreComplexMap`,
whose components are the subobject inclusions. The normalized complex functor is an equivalence
(Tag 019G): Mathlib's Dold–Kan equivalence `CategoryTheory.Abelian.DoldKan.equivalence`, whose
functor is `CategoryTheory.Abelian.DoldKan.N = AlgebraicTopology.normalizedMooreComplex A`.

As for Tags 0195–0197, 0199, 019A and 019E elsewhere in this library, the Stacks complex `N(U)`
is taken to be Mathlib's `AlgebraicTopology.normalizedMooreComplex`. Mathlib intersects the
kernels of the face maps `d_1, …, d_n` and uses `d_0` as the differential, the mirror image of the
Stacks convention; both are complements of the degenerate part of `s(U)` and give isomorphic
functors.
-/

add_to_stacks 0198 "the morphism of complexes N(U) -> s(U)"
  AlgebraicTopology.inclusionOfMooreComplexMap
add_to_stacks 0198 "its components are the inclusions N(U_n) -> U_n"
  AlgebraicTopology.inclusionOfMooreComplexMap_f
add_to_stacks 019G "the equivalence Simp(A) ≌ Ch_{≥0}(A)"
  CategoryTheory.Abelian.DoldKan.equivalence
add_to_stacks 019G "the functor of the equivalence is N"
  CategoryTheory.Abelian.DoldKan.equivalence_functor

add_to_stacks 016J "cosimplicial objects of C, the functor category Δ ⥤ C (morphisms are natural \
  transformations); cosimplicial sets and abelian groups are C = sets, abelian groups"
  CategoryTheory.CosimplicialObject

add_to_stacks 016M CategoryTheory.CosimplicialObject.const

add_to_stacks 016N CategoryTheory.Arrow.cechConerve

add_to_stacks 016Q "(1)–(3), for J = the pair and K = Δᵒᵖ: the termwise product U_n × V_n with \
  induced d_i, s_i" CategoryTheory.Limits.combineCones

add_to_stacks 016R "the termwise product is the product in Simp(C)"
  CategoryTheory.Limits.combinedIsLimit

add_to_stacks 0175 "j-th face d_j" CategoryTheory.SimplicialObject.δ
add_to_stacks 0175 "j-th degeneracy s_j" CategoryTheory.SimplicialObject.σ
add_to_stacks 0175 "degenerate simplices" SSet.degenerate
add_to_stacks 0175 "degenerate = a degeneracy s_j y of another simplex"
  SSet.degenerate_eq_iUnion_range_σ

add_to_stacks 0176 "Δ[n] = Mor_Δ(-, [n])" SSet.stdSimplex
add_to_stacks 0176 "every m-simplex of Δ[n] with m > n is degenerate"
  SSet.stdSimplex.instHasDimensionLEObjSimplexCategoryMk
add_to_stacks 0176 "the unique nondegenerate n-simplex is id_[n]"
  SSet.stdSimplex.nonDegenerate_top_dim

add_to_stacks 0177 SSet.yonedaEquiv

add_to_stacks 0179 SSet.hasDimensionLE_prod

add_to_stacks 0180 "Simp_n(C), functors Δ_{≤n}ᵒᵖ ⥤ C (morphisms are natural transformations)"
  CategoryTheory.SimplicialObject.Truncated
add_to_stacks 0180 "Δ_{≤n}" SimplexCategory.Truncated

add_to_stacks 018G CategoryTheory.SimplicialObject.Augmented

-- The two triangle identities of an adjunction `U ⊣ V` (Situation 08N9).
add_to_stacks 08NB
  "V → VUV → V is the identity (for `adj : U ⊣ V`, Mathlib's `F = U`, `G = V`; up to unitors)"
  CategoryTheory.Adjunction.right_triangle
add_to_stacks 08NB "U → UVU → U is the identity (same conventions)"
  CategoryTheory.Adjunction.left_triangle

-- Kan fibrations and Kan complexes (the fibrations of `SSet` are scoped to
-- `SSet.modelCategoryQuillen`).
add_to_stacks 08NU "Kan fibration: right lifting property against the horn inclusions `J`"
  SSet.modelCategoryQuillen.fibration_iff
add_to_stacks 08NU "Kan fibration: `J`, the horn inclusions `Λ[n+1, i] ⟶ Δ[n+1]`"
  SSet.modelCategoryQuillen.J
add_to_stacks 08NU "Kan complex: `S ⟶ ⊤_ SSet` is a Kan fibration" SSet.KanComplex
