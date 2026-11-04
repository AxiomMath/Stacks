module

public import Mathlib.CategoryTheory.Filtered.Final

/-!
# The up-set of a point of a directed preorder is cofinal

In a directed preorder `Λ`, the set `{j // o ≤ j}` of points above a given `o` is again a
directed preorder, and its inclusion into `Λ` is a **final** functor. So a diagram on `Λ` and its
restriction to the up-set have the same colimit.

## Main results

* `CategoryTheory.isDirected_upSet`: the up-set is directed.
* `CategoryTheory.final_upSetInclusion`: its inclusion is final.
* `CategoryTheory.nonempty_isColimit_whiskerLeft_upSetInclusion`: the restriction of a colimit
  cocone to the up-set is a colimit cocone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w

namespace CategoryTheory

variable {Λ : Type w} [Preorder Λ]

/-- The up-set `{j // o ≤ j}` of a point `o` of a preorder is nonempty. -/
instance nonempty_upSet {o : Λ} : Nonempty {j : Λ // o ≤ j} := ⟨⟨o, le_refl o⟩⟩

/-- The up-set of a point of a directed preorder is directed. -/
instance isDirected_upSet [IsDirected Λ (· ≤ ·)] {o : Λ} :
    IsDirected {j : Λ // o ≤ j} (· ≤ ·) where
  directed a b := by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩

/-- The inclusion of the up-set of a point into the ambient preorder is monotone. -/
theorem monotone_upSetVal (o : Λ) : Monotone (Subtype.val : {j : Λ // o ≤ j} → Λ) :=
  fun _ _ h ↦ h

/-- The inclusion of the up-set of a point into the ambient preorder, as a functor. -/
abbrev upSetInclusion (o : Λ) : {j : Λ // o ≤ j} ⥤ Λ :=
  (monotone_upSetVal o).functor

/-- The inclusion of the up-set of a point of a directed preorder is final. -/
theorem final_upSetInclusion [IsDirected Λ (· ≤ ·)] (o : Λ) :
    (upSetInclusion o).Final :=
  (Monotone.final_functor_iff (monotone_upSetVal o)).mpr fun j ↦ by
    obtain ⟨c, hoc, hjc⟩ := directed_of (· ≤ ·) o j
    exact ⟨⟨c, hoc⟩, hjc⟩

/-- If `c` is a colimit cocone of a diagram `F` on a directed preorder, then its restriction to
the up-set of any point is a colimit cocone of the restricted diagram. -/
theorem nonempty_isColimit_whiskerLeft_upSetInclusion [IsDirected Λ (· ≤ ·)] (o : Λ)
    {C : Type*} [Category.{v} C] {F : Λ ⥤ C} {c : Cocone F} (hc : IsColimit c) :
    Nonempty (IsColimit (c.whisker (upSetInclusion o))) :=
  have := final_upSetInclusion o
  ⟨(Functor.Final.isColimitWhiskerEquiv (upSetInclusion o) c).symm hc⟩

end CategoryTheory

end
