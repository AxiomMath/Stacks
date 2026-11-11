module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic

/-!
# A Serre subcategory is abelian, with exact inclusion

**Stacks 02MP** says that a subcategory `C` of an abelian category `A` is a Serre subcategory
exactly when it is nonempty, strictly full, and contains the middle term of every exact sequence
whose outer terms lie in `C` (together with the equivalent conditions on subobjects, quotients and
extensions); and that moreover a Serre subcategory is abelian and its inclusion functor is exact.

The equivalence is `CategoryTheory.ObjectProperty.isSerreClass_iff_prop_X₂_of_exact`, and the
left exactness of the inclusion is `CategoryTheory.ObjectProperty.preservesFiniteLimits_ι`, both
in `StacksCore.CategoryTheory.Abelian.SerreClass.Basic`. This file adds the right exactness and states
the whole tag as one theorem.

## Main results

* `CategoryTheory.ObjectProperty.preservesFiniteLimits_ι_and_preservesFiniteColimits_ι`: the
  inclusion of a Serre subcategory preserves finite limits and finite colimits.
* `CategoryTheory.ObjectProperty.isSerreClass_iff_and_abelian_and_exact`: the full statement of
  Stacks 02MP.

## References

* [Stacks Project, Tag 02MP](https://stacks.math.columbia.edu/tag/02MP)
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

/-- **Stacks 02MP**, "moreover": the inclusion of a Serre subcategory is exact, that is, it
preserves finite limits (it preserves kernels) and finite colimits (it preserves cokernels). -/
@[stacks 02MP "inclusion functor is exact (left and right exact)"]
lemma preservesFiniteLimits_ι_and_preservesFiniteColimits_ι [P.IsSerreClass] :
    PreservesFiniteLimits P.ι ∧ PreservesFiniteColimits P.ι :=
  have {X Y : P.FullSubcategory} (f : X ⟶ Y) := P.preservesCokernels_ι f
  ⟨P.preservesFiniteLimits_ι, P.ι.preservesFiniteColimits_of_preservesCokernels⟩

/-- **Stacks 02MP**, in full. A full subcategory of an abelian category closed under isomorphisms
is a Serre subcategory (Mathlib's `IsSerreClass`: zero, subobjects, quotients, extensions) exactly
when it is nonempty and contains the middle term of every exact sequence whose outer terms belong
to it; and a Serre subcategory is abelian, with inclusion functor preserving finite limits and
finite colimits, that is, exact.

Strict fullness is not a hypothesis: an `ObjectProperty` is a predicate on objects, and a Serre
class is closed under isomorphism, so it holds by construction. -/
@[stacks 02MP "the equivalence, and moreover: abelian with exact inclusion functor"]
theorem isSerreClass_iff_and_abelian_and_exact :
    (P.IsSerreClass ↔ (∃ X, P X) ∧
        ∀ S : ShortComplex C, S.Exact → P S.X₁ → P S.X₃ → P S.X₂) ∧
      (P.IsSerreClass → Nonempty (Abelian P.FullSubcategory) ∧
        PreservesFiniteLimits P.ι ∧ PreservesFiniteColimits P.ι) :=
  ⟨P.isSerreClass_iff_prop_X₂_of_exact,
    fun _ ↦ ⟨⟨inferInstance⟩, P.preservesFiniteLimits_ι_and_preservesFiniteColimits_ι⟩⟩

end CategoryTheory.ObjectProperty
