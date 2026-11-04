module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Order.Preorder.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Fiber
public import StacksFrontier.Topology.Specialization.Defs

/-!
# Distinct points in a finite groupoid orbit do not specialize

Let a groupoid scheme have finite source and target morphisms. Two distinct points of its
object scheme which are joined by an arrow cannot be related by specialization.

## Main results

* `AlgebraicGeometry.not_specialization_of_exists_arrow`: distinct endpoints of an arrow in a
  groupoid scheme with finite source and target are not specializations of one another.

## Implementation notes

Lying in a common orbit is expressed directly by the existence of an arrow with the two given
endpoints, which is the form the source proof uses and which avoids introducing a separate
orbit predicate.

The argument picks a point of the orbit of `u` that is minimal for the specialization order --
the orbit is finite because the source morphism has finite fibres -- and then translates a
hypothetical specialization `u ⤳ u'` along the groupoid to contradict minimality.

## References

* [Stacks Project, Tag 0ABG](https://stacks.math.columbia.edu/tag/0ABG)
-/

@[expose] public section

open CategoryTheory Stacks.Groupoids

namespace AlgebraicGeometry

universe u

/-- Two points of the source of an integral morphism that lie in the same fibre and are related
by specialization are equal, because the fibres of an integral morphism are discrete. -/
private lemma eq_of_specializes_same_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] {x y : X} (hxy : x ⤳ y) (hfy : f x = f y) : x = y := by
  let yF : f.fiber (f x) := (f.fiberHomeo (f x)).symm ⟨y, hfy.symm⟩
  have hF : f.asFiber x ⤳ yF := by
    show (f.fiberHomeo (f x)).symm ⟨x, rfl⟩ ⤳ yF
    exact ((subtype_specializes_iff ..).2 hxy).map
      (f.fiberHomeo (f x)).symm.continuous
  have := congrArg (f.fiberι (f x)) (Set.mem_singleton_iff.mp
    (specializes_iff_forall_closed.mp hF _
      (isClosed_singleton_asFiber_of_isIntegral f x) (Set.mem_singleton _)))
  simpa [yF] using this.symm

/-- Distinct points joined by an arrow of a groupoid scheme with finite source and target cannot
be related by specialization. -/
@[stacks 0ABG]
theorem not_specialization_of_exists_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    {u u' : G.objects.left} (hne : u ≠ u')
    (horbit : ∃ r : G.arrows.left, G.source.left r = u ∧ G.target.left r = u') :
    ¬ (u ⤳ u') := by
  intro hspec
  obtain ⟨r₀, hr₀s, hr₀t⟩ := horbit
  let s : G.arrows.left → G.objects.left := G.source.left
  let t : G.arrows.left → G.objects.left := G.target.left
  let orbit : Set G.objects.left := t '' (s ⁻¹' {u})
  have horbit_finite : orbit.Finite := (G.source.left.finite_preimage_singleton u).image t
  let : PartialOrder G.objects.left := specializationOrder _
  obtain ⟨v, hv, hvmin⟩ :=
    horbit_finite.exists_minimal ⟨u', r₀, by simpa [s] using hr₀s, hr₀t⟩
  obtain ⟨r, hrs, hrt⟩ := hv
  obtain ⟨r', hrr', hrs'⟩ := G.source.left.isClosedMap.specializingMap
    (show s r ⤳ u' by rwa [show s r = u from hrs])
  let w : G.objects.left := t r'
  have hvw : v ⤳ w := by
    simpa [w, t, hrt] using hrr'.map G.target.left.continuous
  have hvw_ne : v ≠ w := by
    intro heq
    have hrr : r = r' := eq_of_specializes_same_fiber G.target.left hrr' (by
      simpa [w, t, hrt] using heq)
    rw [← hrr] at hrs'
    exact hne (hrs.symm.trans hrs')
  have hw : w ∈ orbit := by
    have hrel := PreRelation.equivalence_sourceTargetRel
      (groupoidPreRelation G)
      (groupoidPreRelation_isPreEquivalenceRelation G)
    simp only [PreRelation.source, groupoidPreRelation, Limits.limit.lift_π,
      Limits.BinaryFan.mk_pt, Limits.BinaryFan.mk_snd, PreRelation.target,
      Limits.BinaryFan.mk_fst] at hrel
    have huv : Function.SourceTargetRel s t u' u := ⟨r₀, hr₀t, hr₀s⟩
    have hwu : Function.SourceTargetRel s t w u' := ⟨r', rfl, hrs'⟩
    obtain ⟨q, hqt, hqs⟩ := hrel.trans hwu huv
    exact ⟨q, by simpa [s] using hqs, hqt⟩
  exact hvw_ne (le_antisymm (hvmin hw hvw) hvw)

end AlgebraicGeometry
