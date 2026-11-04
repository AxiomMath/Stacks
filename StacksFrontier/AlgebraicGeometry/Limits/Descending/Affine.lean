module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Perfect.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Affineness at a finite stage of a limit

In the descent situation for a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, affineness of the limit descends to all sufficiently
large stages.

"For all sufficiently large indices" is expressed by an index `i₀` together with the assertion
for every `i` satisfying `i₀ ≤ i`. The index preorder is assumed essentially small relative to
the scheme universe: the conclusion fails for an index type of a larger universe, since a limit
computed in a smaller category of schemes need not remain a limit after enlarging it.

## Main results

* `AlgebraicGeometry.eventually_isAffine`: the schemes in the system are affine beyond some
  index when their limit is affine.

## Implementation notes

The geometric content is the cofiltered statement that an affine limit forces one stage to be
affine, which is available as `AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit`. What is
added here is the passage from a directed preorder to its small model, through which the chosen
limit cone is whiskered, and the propagation of affineness from one stage to all later ones:
a transition morphism into an affine stage is affine, so its source is affine too.

## References

* [Stacks Project, Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
* [Stacks Project, Tag 086P](https://stacks.math.columbia.edu/tag/086P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- Affineness of one stage of the inverse system propagates to all later stages, because the
transition morphisms are affine and the source of an affine morphism with affine target is
affine. -/
private theorem isAffine_of_later_of_stage_isAffine
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (d : DescentSituation.{v, u} I) {i₀ : I}
    (hi₀ : IsAffine (d.system.obj (op i₀))) :
    ∀ i : I, i₀ ≤ i → IsAffine (d.system.obj (op i)) := by
  intro i h
  have := d.transition_affine (homOfLE h).op
  exact isAffine_of_isAffineHom (d.system.map (homOfLE h).op)

/-- **Stacks Project, Tag 01Z6.** In a directed inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms, if the limit is affine then every
sufficiently late stage is affine. -/
@[stacks 01Z6 "for an index preorder essentially small in the scheme universe",
  sga "4 VII 5.4" "partial"]
theorem eventually_isAffine
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    [EssentiallySmall.{u} I]
    (d : DescentSituation.{v, u} I)
    [IsAffine d.limitCone.pt] :
    ∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsAffine (d.system.obj (op i)) := by
  classical
  have : Nonempty I := ⟨d.base⟩
  let e := equivSmallModel.{u} Iᵒᵖ
  have : IsCofiltered (SmallModel.{u} Iᵒᵖ) := IsCofiltered.of_equivalence e
  let D := e.inverse ⋙ d.system
  let c := d.limitCone.whisker e.inverse
  have hc : IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv e.inverse d.limitCone).symm d.isLimit
  have : IsAffine c.pt := ‹IsAffine d.limitCone.pt›
  have (j : SmallModel.{u} Iᵒᵖ) : CompactSpace (D.obj j) :=
    d.quasiCompact (e.inverse.obj j).unop
  have (j : SmallModel.{u} Iᵒᵖ) : QuasiSeparatedSpace (D.obj j) :=
    d.quasiSeparated (e.inverse.obj j).unop
  have {j k : SmallModel.{u} Iᵒᵖ} (f : j ⟶ k) : IsAffineHom (D.map f) :=
    d.transition_affine (e.inverse.map f)
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit D c hc
  exact ⟨(e.inverse.obj j).unop, isAffine_of_later_of_stage_isAffine d hj⟩

end AlgebraicGeometry

end
