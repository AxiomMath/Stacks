module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Order.Directed

/-!
# The tail of a directed preorder is cofinal

Let `Λ` be a directed preorder and `lam : Λ`. The *tail* of `Λ` above `lam` is the upper set
`{μ : Λ // lam ≤ μ}`, a directed preorder in its own right, and its inclusion into `Λ` is a
final functor. Consequently a colimit over `Λ` may be computed over the tail:
`colimit (directedTailInclusion lam ⋙ G) ≅ colimit G`.

This is what lets a construction which needs a *base point* of the index — one stage of a
directed system to start from, as the proof of **Stacks 0GVN** needs when it transports an
affine étale atlas of one stage to all later stages — be carried out on the tail above that
stage without changing the colimit.

## Main definitions

* `CategoryTheory.directedTailInclusion`: the inclusion of the tail into the preorder.

## Main results

* `CategoryTheory.isDirectedOrder_directedTail`: the tail of a directed preorder is directed.
* `CategoryTheory.final_directedTailInclusion`: the inclusion of the tail is final.
* `CategoryTheory.colimitDirectedTailIso`: the colimit over the tail is the colimit.

## Implementation notes

Finality is `Monotone.final_functor_iff`, which for a monotone map out of a directed preorder
reduces finality to the cofinality condition `∀ μ, ∃ ν ≥ lam, μ ≤ ν` — one application of
directedness, the upper bound being repaired to lie in the tail by transitivity. The colimit
comparison is then Mathlib's `CategoryTheory.Functor.Final.colimitIso`, whose underlying
morphism is `colimit.pre`.

The index universe is left free: the diagrams of this project are indexed by preorders in
`Type (u + 1)`, the universe in which the values of an fppf sheaf live, so no smallness
assumption is made on `Λ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v w

variable {Λ : Type w} [Preorder Λ]

/-- The inclusion of the tail `{μ // lam ≤ μ}` of a preorder above `lam` into the preorder. -/
def directedTailInclusion (lam : Λ) : {μ : Λ // lam ≤ μ} ⥤ Λ :=
  Monotone.functor (f := (Subtype.val : {μ : Λ // lam ≤ μ} → Λ)) (Subtype.mono_coe _)

/-- The tail of a directed preorder above an element is itself directed: an upper bound of the
two underlying elements lies in the tail, since it dominates one of them and that one
dominates `lam`. -/
instance isDirectedOrder_directedTail [IsDirected Λ (· ≤ ·)] (lam : Λ) :
    IsDirectedOrder {μ : Λ // lam ≤ μ} :=
  ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩⟩

/-- **The inclusion of the tail of a directed preorder is final.** For a monotone map out of a
directed preorder finality is the cofinality condition of `Monotone.final_functor_iff`, and
here it is one application of directedness: an upper bound of `μ` and `lam` lies in the tail
and dominates `μ`. -/
instance final_directedTailInclusion [IsDirected Λ (· ≤ ·)] (lam : Λ) :
    (directedTailInclusion lam).Final := by
  refine (Monotone.final_functor_iff (Subtype.mono_coe _)).mpr fun μ ↦ ?_
  obtain ⟨ν, hμν, hlamν⟩ := exists_ge_ge μ lam
  exact ⟨⟨ν, hlamν⟩, hμν⟩

/-- **A colimit over a directed preorder is a colimit over any of its tails.** This is
`CategoryTheory.Functor.Final.colimitIso` at the inclusion of the tail. -/
noncomputable def colimitDirectedTailIso [IsDirected Λ (· ≤ ·)] (lam : Λ)
    {C : Type*} [Category.{v} C] (G : Λ ⥤ C) [HasColimit G] :
    colimit (directedTailInclusion lam ⋙ G) ≅ colimit G :=
  Functor.Final.colimitIso (directedTailInclusion lam) G

/-- The colimit insertion at `μ` in the tail, followed by `colimitDirectedTailIso`, is the colimit
insertion at `μ` over the whole preorder. -/
@[reassoc (attr := simp)]
theorem ι_colimitDirectedTailIso_hom [IsDirected Λ (· ≤ ·)] (lam : Λ)
    {C : Type*} [Category.{v} C] (G : Λ ⥤ C) [HasColimit G] (μ : {μ : Λ // lam ≤ μ}) :
    colimit.ι (directedTailInclusion lam ⋙ G) μ ≫ (colimitDirectedTailIso lam G).hom
      = colimit.ι G μ.1 :=
  Functor.Final.ι_colimitIso_hom (directedTailInclusion lam) G μ

end CategoryTheory

end
