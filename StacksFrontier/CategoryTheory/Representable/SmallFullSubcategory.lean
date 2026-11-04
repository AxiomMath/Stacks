module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Logic.Small.Set

/-!
# A functor to sets lands in a small full subcategory

Stacks 001E observes that a functor `F` from a category `𝒜` to the category of sets is an
honest mathematical object, even though the category of sets is "big": the values of `F` on
objects form a *set* `F(Ob 𝒜)`, and `F` may be regarded as a functor from `𝒜` to the full
subcategory of sets spanned by the elements of `F(Ob 𝒜)`.

## Main results

* `CategoryTheory.Functor.toObjRange` and `CategoryTheory.Functor.toObjRange_comp_ι`: the
  factorization of `F : 𝒜 ⥤ Type v` through the full subcategory of `Type v` spanned by the image
  of `F.obj`.
* `CategoryTheory.Functor.surjective_toObjRange_obj` and
  `CategoryTheory.Functor.small_objRange_fullSubcategory`: that full subcategory has exactly the
  values of `F` as its objects, and they are indexed by `Ob 𝒜`, so they form a set of the same
  size as `Ob 𝒜`.

## Implementation notes

In Lean's type theory the first half of the source's remark — that a functor into a big category
is a set and not a class or a formula of set theory — is automatic: a functor is a term of the
type `𝒜 ⥤ Type v`, so there is nothing to prove and nothing to be careful about. What remains, and
is formalized here, is the factorization the source uses to see it, together with the smallness of
the resulting subcategory, which is the formal counterpart of "`F(Ob 𝒜)` is a set".
-/

@[expose] public section

universe v u₁ v₁

namespace CategoryTheory.Functor

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] (F : 𝒜 ⥤ Type v)

/-- The property of a set of being a value of `F` on objects, i.e. of lying in `F(Ob 𝒜)`. -/
def objRange : ObjectProperty (Type v) := fun X => X ∈ Set.range F.obj

/-- **Stacks 001E.** A functor `F : 𝒜 ⥤ Type v` factors through the full subcategory of `Type v`
spanned by the values of `F` on objects; `toObjRange_comp_ι` says the factorization is on the
nose. -/
@[stacks 001E]
def toObjRange : 𝒜 ⥤ (objRange F).FullSubcategory :=
  (objRange F).lift F Set.mem_range_self

/-- The factorization of Stacks 001E is on the nose: composing `F.toObjRange` with the
inclusion `(objRange F).ι` of the full subcategory of values of `F` returns `F` itself, not
merely a functor isomorphic to it. -/
@[simp]
lemma toObjRange_comp_ι : toObjRange F ⋙ (objRange F).ι = F := rfl

/-- The full subcategory of `Type v` spanned by the values of `F` has no objects beyond those
values. -/
lemma surjective_toObjRange_obj : Function.Surjective (toObjRange F).obj := by
  rintro ⟨-, A, rfl⟩
  exact ⟨A, rfl⟩

/-- **Stacks 001E.** The full subcategory of `Type v` spanned by the values of `F` on objects is
small: its objects are indexed by `Ob 𝒜`. This is the formal counterpart of the source's
observation that `F(Ob 𝒜)` is a set even though the category of sets is big. -/
@[stacks 001E]
instance small_objRange_fullSubcategory : Small.{u₁} (objRange F).FullSubcategory :=
  small_of_surjective (surjective_toObjRange_obj F)

end CategoryTheory.Functor
