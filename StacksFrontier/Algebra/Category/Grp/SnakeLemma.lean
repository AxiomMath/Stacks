module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-! # The snake lemma for abelian groups

The snake lemma for abelian groups, together with the injectivity of its first map and the
surjectivity of its last map under the corresponding hypotheses on the rows.

## Main results

* `CategoryTheory.ShortComplex.SnakeInput.snake_lemma_addCommGrpCat`: the snake lemma for abelian
  groups, with both of its "moreover" clauses.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.ShortComplex

namespace SnakeInput

/-- The snake lemma for abelian groups, with both of its "moreover" clauses. Given a commutative
diagram of abelian groups with exact rows `L₁ = (X ⟶ Y ⟶ Z ⟶ 0)` and `L₂ = (0 ⟶ U ⟶ V ⟶ W)`,
encoded as `S : SnakeInput AddCommGrpCat` (with `L₀` the kernels and `L₃` the cokernels of the
vertical maps), the sequence
`Ker α ⟶ Ker β ⟶ Ker γ ⟶ Coker α ⟶ Coker β ⟶ Coker γ` (with the connecting map `S.δ`) is
exact; moreover, if `X ⟶ Y` is injective then `Ker α ⟶ Ker β` is injective, and if `V ⟶ W` is
surjective then `Coker β ⟶ Coker γ` is surjective. -/
@[stacks 07JW "the full statement for abelian groups, including both \"moreover\" clauses \
(Ker α → Ker β injective if X → Y is, Coker β → Coker γ surjective if V → W is); the exactness \
part alone is Mathlib's `SnakeInput.snake_lemma`, for any abelian category"]
theorem snake_lemma_addCommGrpCat (S : SnakeInput AddCommGrpCat.{u}) :
    S.composableArrows.Exact ∧
      (Function.Injective S.L₁.f → Function.Injective S.L₀.f) ∧
      (Function.Surjective S.L₂.g → Function.Surjective S.L₃.g) := by
  refine ⟨S.snake_lemma, fun h ↦ ?_, fun h ↦ ?_⟩
  · have : Mono S.L₁.f := (AddCommGrpCat.mono_iff_injective _).2 h
    exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  · have : Epi S.L₂.g := (AddCommGrpCat.epi_iff_surjective _).2 h
    exact (AddCommGrpCat.epi_iff_surjective _).1 inferInstance

end SnakeInput

end CategoryTheory.ShortComplex
