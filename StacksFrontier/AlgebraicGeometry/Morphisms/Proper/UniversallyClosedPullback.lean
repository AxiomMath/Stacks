module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# Universal closedness of a map between self-fibre products

Let `f : X ⟶ Y` be a morphism of schemes over `S`. If `f` is universally closed, then the
induced morphism from `X ×_S X` to `Y ×_S Y` is universally closed and quasi-compact.

## Main results

* `AlgebraicGeometry.universallyClosed_map_self_pullback` proves universal closedness of the
  induced morphism.
* `AlgebraicGeometry.quasiCompact_map_self_pullback` proves quasi-compactness of the induced
  morphism.

## Implementation notes

The induced morphism is expressed by `CategoryTheory.Limits.pullback.map`. The commutativity
hypothesis records that `f` is a morphism over `S`.

## References

* [Stacks Project, Section 29.41 (01W0)](https://stacks.math.columbia.edu/tag/01W0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A universally closed morphism over `S` induces a universally closed morphism between its
self-fibre products over `S`. -/
lemma universallyClosed_map_self_pullback {S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    (f : X ⟶ Y) (h : p = f ≫ q) [UniversallyClosed f] :
    UniversallyClosed
      (pullback.map p p q q f f (𝟙 S)
        ((Category.comp_id p).trans h) ((Category.comp_id p).trans h)) :=
  CategoryTheory.MorphismProperty.pullbackMap
    (P := @UniversallyClosed) (f := p) (g := p) (f' := q) (g' := q)
    (i₁ := f) (i₂ := f) inferInstance inferInstance h h

/-- A universally closed morphism over `S` induces a quasi-compact morphism between its
self-fibre products over `S`. -/
lemma quasiCompact_map_self_pullback {S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    (f : X ⟶ Y) (h : p = f ≫ q) [UniversallyClosed f] :
    QuasiCompact
      (pullback.map p p q q f f (𝟙 S)
        ((Category.comp_id p).trans h) ((Category.comp_id p).trans h)) := by
  have := universallyClosed_map_self_pullback p q f h
  infer_instance

end AlgebraicGeometry

end
