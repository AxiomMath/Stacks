module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic

/-!
# The arrow scheme of a restricted groupoid scheme

A groupoid scheme `G` can be restricted along an arbitrary morphism `g` to its scheme of objects.
The arrow scheme of the restriction is the iterated fibre product parametrizing triples
`(u_t, r, u_s)` of an arrow `r` of `G` and points `u_t`, `u_s` such that `g u_t` is the target
of `r` and `g u_s` is its source.

## Main definitions

* `AlgebraicGeometry.restrictionArrows` is the arrow scheme of the restricted groupoid.
* `AlgebraicGeometry.restrictionSource` and `AlgebraicGeometry.restrictionTarget` are its
  source and target maps.
* `AlgebraicGeometry.restrictionArrowsToArrows` is its canonical map to the original arrow
  scheme.

## Main results

* `AlgebraicGeometry.GroupoidScheme.restriction_condition` and
  `AlgebraicGeometry.GroupoidScheme.restriction_condition'` are the two defining compatibilities
  of the three projections.
* `AlgebraicGeometry.GroupoidScheme.restriction_hom_ext` says that a generalized point of the
  arrow scheme of the restriction is determined by its source, its target and its arrow.

## References

* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The scheme of arrows of the restriction of `G` along `g`.  Its points are triples
`(u_t, r, u_s)` such that `g u_t` is the target of `r` and `g u_s` is its source. -/
noncomputable def restrictionArrows {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) : Over S :=
  pullback (pullback.snd g G.target) (pullback.fst G.source g)

/-- The canonical map from the arrow scheme of a restriction to the original arrow scheme. -/
noncomputable def restrictionArrowsToArrows {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) : restrictionArrows G g ⟶ G.arrows :=
  pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) ≫
    pullback.snd g G.target

/-- The source map from the arrow scheme of a restriction. -/
noncomputable def restrictionSource {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) : restrictionArrows G g ⟶ U' :=
  pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) ≫
    pullback.snd G.source g

/-- The target map from the arrow scheme of a restriction. -/
noncomputable def restrictionTarget {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) : restrictionArrows G g ⟶ U' :=
  pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) ≫
    pullback.fst g G.target

namespace GroupoidScheme

/-- The lift of the source of an arrow of a restriction maps to the source of that arrow. -/
@[simp, reassoc]
lemma restriction_condition {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) :
    restrictionSource G g ≫ g = restrictionArrowsToArrows G g ≫ G.source := by
  unfold restrictionSource restrictionArrowsToArrows restrictionArrows
  simp only [Category.assoc]
  rw [← pullback.condition, ← pullback.condition_assoc]

/-- The lift of the target of an arrow of a restriction maps to the target of that arrow. -/
@[simp, reassoc]
lemma restriction_condition' {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) :
    restrictionArrowsToArrows G g ≫ G.target = restrictionTarget G g ≫ g := by
  unfold restrictionTarget restrictionArrowsToArrows restrictionArrows
  simp only [Category.assoc]
  rw [← pullback.condition]

/-- A generalized point of the arrow scheme of a restriction is determined by its source, its
target and its underlying arrow of the original groupoid. -/
lemma restriction_hom_ext {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) {T : Over S} (f h : T ⟶ restrictionArrows G g)
    (hs : f ≫ restrictionSource G g = h ≫ restrictionSource G g)
    (ht : f ≫ restrictionTarget G g = h ≫ restrictionTarget G g)
    (ha : f ≫ restrictionArrowsToArrows G g = h ≫ restrictionArrowsToArrows G g) :
    f = h := by
  have key {X Y Z : Over S} {a b : T ⟶ X} {p : X ⟶ Y} {q : Y ⟶ Z}
      (e : a ≫ p ≫ q = b ≫ p ≫ q) : (a ≫ p) ≫ q = (b ≫ p) ≫ q := by simpa using e
  apply pullback.hom_ext <;> apply pullback.hom_ext
  · exact key ht
  · exact key ha
  · exact key (by rw [← pullback.condition]; exact ha)
  · exact key hs

end GroupoidScheme

end AlgebraicGeometry

end
