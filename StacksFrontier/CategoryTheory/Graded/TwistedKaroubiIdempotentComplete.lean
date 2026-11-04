module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubi
public import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# The twisted Karoubi envelope is idempotent complete

Let `M = (X, p, m)` be an object of the twisted Karoubi envelope of a graded category and let
`a : M ⟶ M` be an idempotent. Then `a` is a degree-zero idempotent of `X` fixed by `p`, so
`N = (X, a, m)` is again an object, and `a` read as a morphism `N ⟶ M` and as a morphism
`M ⟶ N` splits the idempotent `a`. Hence the twisted Karoubi envelope is idempotent complete.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.imageOfIdem`: the triple `(X, a, m)` cut out of
  `(X, p, m)` by an idempotent `a`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.imageOfIdemι` and
  `CategoryTheory.GradedCategory.TwistedKaroubi.imageOfIdemπ`: the inclusion and the projection
  splitting `a`.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.instIsIdempotentComplete`: the twisted Karoubi
  envelope is idempotent complete.

## References

* [Stacks Project, Tag 0FGB](https://stacks.math.columbia.edu/tag/0FGB)
-/

@[expose] public section

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]

/-- An idempotent of the twisted Karoubi envelope is an idempotent of the underlying object. -/
theorem val_comp_val_of_idem (M : TwistedKaroubi R C) (a : M ⟶ M) (ha : a ≫ a = a) :
    a.val ≫ a.val = a.val := by
  rw [← comp_val, ha]

/-- The triple `(X, a, m)` cut out of `M = (X, p, m)` by an idempotent `a : M ⟶ M`. -/
@[simps]
def imageOfIdem (M : TwistedKaroubi R C) (a : M ⟶ M) (ha : a ≫ a = a) : TwistedKaroubi R C where
  X := M.X
  p := a.val
  p_mem := by simpa only [sub_self] using a.2.1
  idem := val_comp_val_of_idem M a ha
  twist := M.twist

variable (M : TwistedKaroubi R C) (a : M ⟶ M) (ha : a ≫ a = a)

/-- The inclusion `(X, a, m) ⟶ (X, p, m)`, given by `a`. -/
def imageOfIdemι : imageOfIdem M a ha ⟶ M :=
  Hom.mk a.val ⟨a.2.1, val_comp_val_of_idem M a ha, a.2.2.2⟩

/-- The projection `(X, p, m) ⟶ (X, a, m)`, given by `a`. -/
def imageOfIdemπ : M ⟶ imageOfIdem M a ha :=
  Hom.mk a.val ⟨a.2.1, a.2.2.1, val_comp_val_of_idem M a ha⟩

/-- The underlying morphism of the inclusion `imageOfIdemι M a ha` is `a.val`. -/
@[simp]
theorem imageOfIdemι_val : (imageOfIdemι M a ha).val = a.val :=
  rfl

/-- The underlying morphism of the projection `imageOfIdemπ M a ha` is `a.val`. -/
@[simp]
theorem imageOfIdemπ_val : (imageOfIdemπ M a ha).val = a.val :=
  rfl

/-- The inclusion followed by the projection is the identity of `imageOfIdem M a ha`. -/
@[reassoc (attr := simp)]
theorem imageOfIdemι_π : imageOfIdemι M a ha ≫ imageOfIdemπ M a ha = 𝟙 _ :=
  TwistedKaroubi.hom_ext (val_comp_val_of_idem M a ha)

/-- The projection followed by the inclusion is the idempotent `a`. -/
@[reassoc (attr := simp)]
theorem imageOfIdemπ_ι : imageOfIdemπ M a ha ≫ imageOfIdemι M a ha = a :=
  TwistedKaroubi.hom_ext (val_comp_val_of_idem M a ha)

/-- The twisted Karoubi envelope of a graded category is idempotent complete: an idempotent `a`
of `(X, p, m)` splits through `(X, a, m)`. -/
instance instIsIdempotentComplete : IsIdempotentComplete (TwistedKaroubi R C) where
  idempotents_split M a ha :=
    ⟨imageOfIdem M a ha, imageOfIdemι M a ha, imageOfIdemπ M a ha,
      imageOfIdemι_π M a ha, imageOfIdemπ_ι M a ha⟩

end CategoryTheory.GradedCategory.TwistedKaroubi
