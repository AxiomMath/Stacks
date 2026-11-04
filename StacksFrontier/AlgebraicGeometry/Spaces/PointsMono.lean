module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# A monomorphism is injective on points (Stacks 06RV)

A monomorphism of presheaves on the big fppf site of `S` induces an injective map on the sets
of equivalence classes of field-valued points of Tag 03BU. In particular this holds for a
monomorphism of algebraic spaces over `S`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.pointsMap_injective_of_mono`: **Stacks 06RV**.

## Implementation notes

The proof uses only the monomorphism property, not the algebraic-space conditions, so the
statement is for arbitrary presheaves. Two field-valued points of the source whose images have
a common extension already have one: the common extension of the images is a scheme-valued
point of the target over which both images agree, and pulling the first point back along it
gives a field-valued point of the source which, by injectivity of the monomorphism on sections,
also receives the second.

## References

* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- Two field-valued points of the source of a monomorphism whose images have a common
extension have a common extension themselves. -/
private theorem hasCommonExtension_of_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) [Mono f]
    {p q : FieldValuedPoint B S hS F}
    (h : FieldValuedPoint.HasCommonExtension B S hS G
      (FieldValuedPoint.map B S hS F f p)
      (FieldValuedPoint.map B S hS F f q)) :
    FieldValuedPoint.HasCommonExtension B S hS F p q := by
  obtain ⟨r, ⟨i, hi⟩, ⟨j, hj⟩⟩ := h
  change G.map i.op (f.app _ p.value) = r.value at hi
  change G.map j.op (f.app _ q.value) = r.value at hj
  let rF : FieldValuedPoint B S hS F := { r with value := F.map i.op p.value }
  refine ⟨rF, ⟨i, rfl⟩, ⟨j, ?_⟩⟩
  apply Eq.symm
  apply (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app f).mp ‹Mono f› _)
  exact ((f.naturality_apply i.op p.value).trans hi).trans
    ((f.naturality_apply j.op q.value).trans hj).symm

/-- **Stacks 06RV.** A monomorphism induces an injective map on equivalence classes of
field-valued points. -/
@[stacks 06RV]
theorem pointsMap_injective_of_mono
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) [Mono f] :
    Function.Injective (pointsMap B S hS F f) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  obtain ⟨q, rfl⟩ := Quot.exists_rep y
  simp only [pointsMap_class, FieldValuedPoint.class_eq_class_iff] at hxy
  exact FieldValuedPoint.class_eq_class_of_hasCommonExtension
    B S hS F (hasCommonExtension_of_map B S hS f hxy)

end AlgebraicGeometry.Space

end
