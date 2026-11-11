module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.FibreHomologyDeltaFunctor

/-!
# Postcomposition with an exact functor preserves coeffaceability

Let `H = (Hₙ, δ)` be a homological δ-functor from `A` to `B` and `P : B ⥤ B'` an exact functor
of abelian categories, and let `H.postcomp P` be the postcomposed δ-functor
(`Stacks.CategoryHomology.HomologicalDeltaFunctor.postcomp`). A coeffacement for `H` is one for
the postcomposition, since `P` sends zero morphisms to zero morphisms.

## Main results

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.coeffaceable_postcomp`: postcomposition
  preserves coeffaceability.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u' v'' u''

namespace Stacks.CategoryHomology.HomologicalDeltaFunctor

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  {B' : Type u''} [Category.{v''} B'] [Abelian B']
  (H : HomologicalDeltaFunctor A B) (P : B ⥤ B') [P.Additive] [PreservesFiniteLimits P]
  [PreservesFiniteColimits P]

/-- **Postcomposition with an exact functor preserves coeffaceability.** -/
theorem coeffaceable_postcomp [H.Coeffaceable] : (H.postcomp P).Coeffaceable where
  nonempty X n := by
    obtain ⟨c⟩ := Coeffaceable.nonempty (H := H) X n
    have hπ : ((H.postcomp P).functor (n + 1)).map c.π = 0 := by
      rw [postcomp_functor, Functor.comp_map, c.map_π, P.map_zero]
    exact ⟨⟨c.P, c.π, hπ⟩⟩

end Stacks.CategoryHomology.HomologicalDeltaFunctor

end
