module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import StacksCore.Tactic.StacksAttribute

/-!
# The morphism of limits induced by a functor of index categories

Let `M : I ⥤ C` and `N : J ⥤ C` be diagrams, and `H : I ⥤ J` a functor. A natural transformation
`t : H ⋙ N ⟶ M` induces a unique morphism `θ : limit N ⟶ limit M` compatible with the
projections, and dually a natural transformation `t : M ⟶ H ⋙ N` induces a unique morphism
`θ : colimit M ⟶ colimit N` compatible with the coprojections.

Mathlib's `limit.pre N H ≫ limMap t` and `colimMap t ≫ colimit.pre N H` construct these morphisms
only when the composite diagram `H ⋙ N` has a limit (resp. colimit); the statements here assume
only that `M` and `N` do.

## Main statements

* `CategoryTheory.Limits.limit.existsUnique_comp_π_eq`: the morphism of limits.
* `CategoryTheory.Limits.colimit.existsUnique_ι_comp_eq`: the morphism of colimits.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {I J C : Type*} [Category* I] [Category* J] [Category* C]

/-- Given diagrams `M : I ⥤ C` and `N : J ⥤ C` with limits, a functor `H : I ⥤ J` and a
natural transformation `t : H ⋙ N ⟶ M`, there is a unique morphism
`θ : limit N ⟶ limit M` such that `limit.π N (H.obj i) ≫ t.app i = θ ≫ limit.π M i` for
every `i`. -/
@[stacks 002L]
lemma limit.existsUnique_comp_π_eq (M : I ⥤ C) (N : J ⥤ C) [HasLimit M] [HasLimit N]
    (H : I ⥤ J) (t : H ⋙ N ⟶ M) :
    ∃! θ : limit N ⟶ limit M, ∀ i, limit.π N (H.obj i) ≫ t.app i = θ ≫ limit.π M i :=
  ⟨limit.lift M
      { pt := limit N
        π :=
          { app i := limit.π N (H.obj i) ≫ t.app i
            naturality i i' f := by simp [← t.naturality f] } },
    fun i ↦ by rw [limit.lift_π], fun θ hθ ↦ limit.hom_ext fun i ↦ by rw [← hθ i, limit.lift_π]⟩

/-- Given diagrams `M : I ⥤ C` and `N : J ⥤ C` with colimits, a functor `H : I ⥤ J` and a
natural transformation `t : M ⟶ H ⋙ N`, there is a unique morphism
`θ : colimit M ⟶ colimit N` such that `colimit.ι M i ≫ θ = t.app i ≫ colimit.ι N (H.obj i)` for
every `i`. -/
@[stacks 002K]
lemma colimit.existsUnique_ι_comp_eq (M : I ⥤ C) (N : J ⥤ C) [HasColimit M] [HasColimit N]
    (H : I ⥤ J) (t : M ⟶ H ⋙ N) :
    ∃! θ : colimit M ⟶ colimit N, ∀ i, colimit.ι M i ≫ θ = t.app i ≫ colimit.ι N (H.obj i) :=
  ⟨colimit.desc M
      { pt := colimit N
        ι :=
          { app i := t.app i ≫ colimit.ι N (H.obj i)
            naturality i i' f := by rw [← Category.assoc, t.naturality f]; simp } },
    fun i ↦ colimit.ι_desc _ i, fun θ hθ ↦ colimit.hom_ext fun i ↦ by rw [hθ i, colimit.ι_desc]⟩

end CategoryTheory.Limits
