module

public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.CategoryTheory.Triangulated.LocallySmallTransport

/-!
# Compact objects of a locally small compactly generated triangulated category

Let `T` be a triangulated category whose morphisms are `w`-small and which has coproducts indexed
by `Type w`, and let `E` be a compact object of `T` which is a weak generator. Then the compact
objects of `T` are exactly the triangulated envelope `⟨E⟩` of `E`: this is the classical-generator
half of Stacks 09SR, transported from a model with small morphisms.

## Main results

* `CategoryTheory.Pretriangulated.triangEnvelope_eq_isCompactObject_of_locallySmall`.

## References

* [Stacks Project, Tag 09SR](https://stacks.math.columbia.edu/tag/09SR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.ObjectProperty

universe w v u

namespace CategoryTheory.Pretriangulated

/-- The inverse image of a property stable under retracts is stable under retracts. -/
theorem isStableUnderRetracts_inverseImage {C D : Type*} [Category C] [Category D]
    (Q : ObjectProperty D) [Q.IsStableUnderRetracts] (F : C ⥤ D) :
    (Q.inverseImage F).IsStableUnderRetracts where
  of_retract r hY := Q.prop_of_retract (r.map F) hY

/-- The one-element family indexed by `PUnit` spans the property `singleton`. -/
private theorem ofObj_punit_eq_singleton_aux {C : Type*} [Category C] (E : C) :
    ObjectProperty.ofObj (fun _ : PUnit.{w + 1} => E) = ObjectProperty.singleton E := by
  ext; simp [ObjectProperty.ofObj_iff]

/-- An object lies in its own triangulated envelope. -/
private theorem prop_triangEnvelope_singleton {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (E : C) : (ObjectProperty.singleton E).triangEnvelope E :=
  ObjectProperty.le_triangEnvelope _ _ ((ObjectProperty.singleton_iff _ _).2 rfl)

/-- The triangulated envelope of an object is carried into the triangulated envelope of its image
by a triangulated functor. -/
theorem triangEnvelope_singleton_le_inverseImage {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] (E : C) :
    (ObjectProperty.singleton E).triangEnvelope ≤
      ((ObjectProperty.singleton (F.obj E)).triangEnvelope).inverseImage F := by
  have := isStableUnderRetracts_inverseImage
    ((ObjectProperty.singleton (F.obj E)).triangEnvelope) F
  rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
  exact prop_triangEnvelope_singleton _

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
  [LocallySmall.{w} T] [HasCoproducts.{w} T]

/-- **Compact objects of a locally small compactly generated triangulated category.** If `E` is
a compact weak generator of `T`, then the triangulated envelope of `E` consists exactly of the
compact objects of `T`. -/
theorem triangEnvelope_eq_isCompactObject_of_locallySmall (E : T)
    (hEc : IsCompactObject.{w} E) (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton E).triangEnvelope = IsCompactObject.{w, _, _} (C := T) := by
  obtain ⟨D, _, _, _, _, _, _, e, _, _, _, _, _, _, hD⟩ :=
    exists_triangulatedEquivalence_of_locallySmall.{w} T
  have := hD inferInstance
  have : HasCoproducts.{w} D := fun _ => Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  have hEs : IsCompactObject.{w} (e.functor.obj E) :=
    (isCompactObject_iff_isCompactObject_obj e.functor E).1 hEc
  have hgen : (ObjectProperty.singleton (e.functor.obj E)).IsWeakTriangulatedGenerator := by
    have h := isWeakTriangulatedGenerator_ofObj_of_equivalence e (fun _ : PUnit.{w + 1} => E)
      (by rwa [ofObj_punit_eq_singleton_aux])
    rwa [ofObj_punit_eq_singleton_aux] at h
  have hD' :=
    (isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated
      (e.functor.obj E)).1 hgen |>.1
  ext X
  constructor
  · intro hX
    have h := triangEnvelope_singleton_le_inverseImage e.functor E X hX
    rw [ObjectProperty.prop_inverseImage_iff, hD'] at h
    exact (isCompactObject_iff_isCompactObject_obj e.functor X).2 h
  · intro hX
    have hX' : IsCompactObject.{w} (e.functor.obj X) :=
      (isCompactObject_iff_isCompactObject_obj e.functor X).1 hX
    rw [← hD'] at hX'
    have h := triangEnvelope_singleton_le_inverseImage e.inverse (e.functor.obj E) _ hX'
    rw [ObjectProperty.prop_inverseImage_iff] at h
    have hle : (ObjectProperty.singleton (e.inverse.obj (e.functor.obj E))).triangEnvelope ≤
        (ObjectProperty.singleton E).triangEnvelope := by
      rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
      exact ObjectProperty.prop_of_iso _ (e.unitIso.app E)
        (prop_triangEnvelope_singleton E)
    exact ObjectProperty.prop_of_iso _ (e.unitIso.app X).symm (hle _ h)

end CategoryTheory.Pretriangulated

end
