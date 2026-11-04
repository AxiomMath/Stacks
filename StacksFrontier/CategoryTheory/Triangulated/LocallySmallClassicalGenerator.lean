module

public import StacksFrontier.CategoryTheory.Triangulated.ShrinkHomsTriangulated

/-!
# A compact generator classically generates the compact objects, for locally small categories

Let `T` be a triangulated category which has direct sums indexed by `Type w` and whose morphism
types are `w`-small. If a compact object `E` of `T` is a weak generator of `T`, then `E` is a
classical generator of the compact objects: the triangulated envelope `⟨E⟩` of `E`, the smallest
strictly full saturated triangulated subcategory of `T` containing `E`, is exactly the property
of being compact. This is the implication (2) ⇒ (1) of [Stacks, Tag 09SR]
(`isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated`)
for a category whose morphisms do not live in the universe of its direct sums, which is the
situation of a derived category of the standard model.

## Main results

* `triangEnvelope_singleton_le_isCompactObject`: the envelope of a compact object consists of
  compact objects.
* `triangEnvelope_singleton_eq_isCompactObject_of_locallySmall`: the envelope of a compact weak
  generator is the property of being compact.
* `triangEnvelope_singleton_eq_of_isCompactObject_iff_of_locallySmall`: the same, for any
  property of objects which characterizes the compact objects. This is the form in which the
  geometric remarks [Stacks, Tag 0GFC] and [Stacks, Tag 0GFD] use it, the property being
  perfectness.

## Implementation notes

The inclusion `⟨E⟩ ≤ D_c` is the universal property of the envelope, because the compact objects
form a triangulated subcategory closed under retracts ([Stacks, Tag 09QH]) at every universe of
direct sums. The reverse inclusion is transported along the triangulated equivalence of `T` with
a model whose morphisms lie in `Type w`
(`CategoryTheory.Pretriangulated.exists_triangulatedEquivalence_of_locallySmall`): there the base
form of [Stacks, Tag 09SR] applies, and the inverse image of `⟨E⟩` under the inverse equivalence
is a triangulated subcategory closed under retracts containing the image of `E`, so it contains
the envelope of that image.

## References

* [Stacks Project, Tag 09SR](https://stacks.math.columbia.edu/tag/09SR)
* [Stacks Project, Tag 09QH](https://stacks.math.columbia.edu/tag/09QH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace CategoryTheory.ObjectProperty

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]

omit [IsTriangulated T] in
/-- The triangulated envelope of a compact object consists of compact objects: the compact
objects form a triangulated subcategory closed under retracts ([Stacks, Tag 09QH]). -/
theorem triangEnvelope_singleton_le_isCompactObject [HasCoproducts.{w} T] (E : T)
    [IsCompactObject.{w} E] :
    (ObjectProperty.singleton E).triangEnvelope ≤ IsCompactObject.{w, _, _} (C := T) := by
  obtain ⟨hiso, htri, -, -⟩ :
      ObjectProperty.IsClosedUnderIsomorphisms (IsCompactObject.{w, _, _} (C := T)) ∧ _ :=
    isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := T)
  have : ObjectProperty.IsStableUnderRetracts (IsCompactObject.{w, _, _} (C := T)) :=
    ⟨fun r hB => isCompactObject_of_retract hB r.i r.r r.retract⟩
  rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
  exact ‹IsCompactObject.{w} E›

/-- **A compact weak generator classically generates the compact objects** ([Stacks, Tag 09SR],
(2) ⇒ (1)), for a triangulated category `T` which is `LocallySmall.{w}` and has direct sums
indexed by `Type w`. If the compact object `E` is a weak generator of `T`, then the triangulated
envelope of `E` is exactly the property of being a compact object. -/
theorem triangEnvelope_singleton_eq_isCompactObject_of_locallySmall [LocallySmall.{w} T]
    [HasCoproducts.{w} T] (E : T) [IsCompactObject.{w} E]
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton E).triangEnvelope = IsCompactObject.{w, _, _} (C := T) := by
  refine le_antisymm (triangEnvelope_singleton_le_isCompactObject E) (fun X hX => ?_)
  obtain ⟨D, _, _, _, _, _, _, e, _, _, _, _, _, _, hD⟩ :=
    exists_triangulatedEquivalence_of_locallySmall.{w} T
  have := hD inferInstance
  have : HasCoproducts.{w} D := fun _ => Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  have : IsCompactObject.{w} (e.functor.obj E) :=
    (isCompactObject_iff_isCompactObject_obj e.functor E).1 inferInstance
  have henv :=
    ((isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated
      (e.functor.obj E)).1 (isWeakTriangulatedGenerator_obj_of_equivalence e E hE)).1
  -- The image of `X` is compact, hence in the envelope of the image of `E`.
  have hFX : (ObjectProperty.singleton (e.functor.obj E)).triangEnvelope (e.functor.obj X) := by
    rw [henv]
    exact (isCompactObject_iff_isCompactObject_obj e.functor X).1 hX
  -- The inverse image of `⟨E⟩` under the inverse equivalence is thick and contains `e E`.
  let Q := (ObjectProperty.singleton E).triangEnvelope.inverseImage e.inverse
  have : Q.IsStableUnderRetracts :=
    ⟨fun r hB => ObjectProperty.prop_of_retract (ObjectProperty.singleton E).triangEnvelope
      (r.map e.inverse) hB⟩
  have hle : (ObjectProperty.singleton (e.functor.obj E)).triangEnvelope ≤ Q := by
    rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
    exact ObjectProperty.prop_of_iso (ObjectProperty.singleton E).triangEnvelope (e.unitIso.app E)
      (ObjectProperty.le_triangEnvelope _ _ ((ObjectProperty.singleton_iff E E).2 rfl))
  exact ObjectProperty.prop_of_iso (ObjectProperty.singleton E).triangEnvelope
    (e.unitIso.app X).symm (hle _ hFX)

/-- **A compact weak generator classically generates any property characterizing the compact
objects**, for a triangulated category `T` which is `LocallySmall.{w}` and has direct sums
indexed by `Type w`: if `E` is a compact weak generator of `T` and `P` holds exactly on the compact
objects, then the triangulated envelope of `E` is `P`. This is the triangulated-category content
of [Stacks, Tags 0GFC and 0GFD], where `P` is perfectness and its identification with
compactness is [Stacks, Tag 09M8], respectively [Stacks, Tag 0AED]. -/
theorem triangEnvelope_singleton_eq_of_isCompactObject_iff_of_locallySmall [LocallySmall.{w} T]
    [HasCoproducts.{w} T] (E : T) [IsCompactObject.{w} E]
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) (P : ObjectProperty T)
    (hP : ∀ X : T, IsCompactObject.{w} X ↔ P X) :
    (ObjectProperty.singleton E).triangEnvelope = P := by
  rw [triangEnvelope_singleton_eq_isCompactObject_of_locallySmall E hE]
  ext X
  exact hP X

end CategoryTheory.ObjectProperty

end
