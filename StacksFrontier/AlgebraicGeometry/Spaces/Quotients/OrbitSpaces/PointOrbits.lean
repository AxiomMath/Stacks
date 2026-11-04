module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.RelationOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace
public import StacksFrontier.Topology.Separation.KolmogorovQuotient

/-!
# Orbits of a pre-relation on the points of an algebraic space

Fix a scheme `S` in a big fppf site `B` and a presheaf `Z` on the big fppf site of `S`. A
pre-relation `j : R ⟶ U ×_Z U` induces a binary relation on the set `|U|` of points of `U`:
two points are related when one is the source and the other the target of a common point of
`R`. The *orbit* of a point of `|U|` is its class for the equivalence closure of that
relation, that is the set of points joined to it by a finite chain of arrows of `R`,
traversed in either direction and with stationary steps allowed.

A morphism out of `U` which is invariant under `j` is constant on every orbit. If `j` is a
pre-equivalence relation the chains collapse: an orbit is then the set of targets of the
arrows of `j` out of the given point.

## Main definitions

* `AlgebraicGeometry.Space.PreRelation.pointOrbit` is the orbit of a point of `|U|` under a
  pre-relation.

## Main results

* `AlgebraicGeometry.Space.pointsMap_eq_of_mem_pointOrbit`: the map on points induced by a
  morphism invariant under a pre-relation is constant on every orbit.
* `AlgebraicGeometry.Space.PreRelation.pointOrbit_eq_targets_of_source`: for a
  pre-equivalence relation an orbit consists of the targets of the arrows whose source is the
  given point.

## Implementation notes

The relation generating an orbit is `Function.SourceTargetRel` for the two maps `|R| → |U|`
induced by the target and the source, so no further relation has to be introduced; the orbit
is its `Relation.EqvGen` class, and clients use the `Relation.EqvGen` API directly.

The two maps are passed in the order `(target, source)`, which spells out the condition
`∃ r, s(r) = x ∧ t(r) = y`, whereas
`AlgebraicGeometry.Space.PreRelation.isPreEquivalenceRelation_sourceTargetRel` of **Stacks
043F** passes them the other way round. The two are the opposite orientations of one
relation, so they have the same equivalence closure, but they are not the same proposition:
the proof below exchanges them explicitly using the symmetry supplied by 043F, which is also
what makes the closure collapse.

Everything is stated for an arbitrary presheaf `Z` as base and for arbitrary objects of
`CategoryTheory.Over Z`, matching `AlgebraicGeometry.Space.PreRelation` of
`StacksFrontier/AlgebraicGeometry/Spaces/RelationsOverSpace.lean`; nothing here uses the
algebraic-space axioms. The hypothesis of `pointsMap_eq_of_mem_pointOrbit` is
`AlgebraicGeometry.Space.IsInvariant` of **Stacks 048E**, which is stated over an arbitrary
base object of an arbitrary category whose slice has binary products and so applies to the
slice of presheaves used here.

## References

* [Stacks Project, Tag 048N](https://stacks.math.columbia.edu/tag/048N)
* [Stacks Project, Tag 048O](https://stacks.math.columbia.edu/tag/048O)
* [Stacks Project, Tag 048P](https://stacks.math.columbia.edu/tag/048P)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}

/-- **Stacks 048N.** The *orbit* of a point of `|U|` under a pre-relation `j : R ⟶ U ×_Z U`:
the set of points joined to it by a finite chain of arrows of `j`, traversed in either
direction, with stationary steps allowed. -/
@[stacks 048N]
noncomputable abbrev PreRelation.pointOrbit (j : PreRelation R U)
    (u : points B S hS U.left) : Set (points B S hS U.left) :=
  {u' | Relation.EqvGen
    (Function.SourceTargetRel (pointsMap B S hS R.left j.target.left)
      (pointsMap B S hS R.left j.source.left)) u u'}

/-- **Stacks 048O.** For a pre-equivalence relation an orbit is cut out by a single arrow: it
consists of the targets of the arrows of the pre-relation whose source is the given point. -/
@[stacks 048O]
theorem PreRelation.pointOrbit_eq_targets_of_source (j : PreRelation R U)
    (hj : IsPreEquivalenceRelation j) (u : points B S hS U.left) :
    j.pointOrbit u =
      {u' | ∃ r : points B S hS R.left,
        pointsMap B S hS R.left j.source.left r = u ∧
          pointsMap B S hS R.left j.target.left r = u'} := by
  have hst := j.isPreEquivalenceRelation_sourceTargetRel hj
  have heq : Function.SourceTargetRel (pointsMap B S hS R.left j.target.left)
        (pointsMap B S hS R.left j.source.left) =
      Function.SourceTargetRel (pointsMap B S hS R.left j.source.left)
        (pointsMap B S hS R.left j.target.left) := by
    funext x y
    refine propext ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨r, hx, hy⟩ := h
      exact hst.symm ⟨r, hy, hx⟩
    · obtain ⟨r, hx, hy⟩ := h
      obtain ⟨r', hy', hx'⟩ := hst.symm ⟨r, hx, hy⟩
      exact ⟨r', hx', hy'⟩
  have hts : Equivalence (Function.SourceTargetRel
      (pointsMap B S hS R.left j.target.left)
      (pointsMap B S hS R.left j.source.left)) := by
    rw [heq]
    exact hst
  ext u'
  exact hts.eqvGen_iff

/-- **Stacks 048P.** A morphism out of `U` which is invariant under a pre-relation takes the
same value at any two points in one orbit. -/
@[stacks 048P]
theorem pointsMap_eq_of_mem_pointOrbit (j : PreRelation R U)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : U.left ⟶ X)
    (hφ : IsInvariant j φ)
    {x y : points B S hS U.left} (hy : y ∈ j.pointOrbit x) :
    pointsMap B S hS U.left φ x = pointsMap B S hS U.left φ y := by
  induction hy with
  | rel a b hab =>
      obtain ⟨r, hra, hrb⟩ := hab
      have key (f : R.left ⟶ U.left) : pointsMap B S hS U.left φ (pointsMap B S hS R.left f r) =
          pointsMap B S hS R.left (f ≫ φ) r := by
        rw [pointsMap_comp]; rfl
      rw [← hra, ← hrb, key, key, hφ]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end AlgebraicGeometry.Space

end
