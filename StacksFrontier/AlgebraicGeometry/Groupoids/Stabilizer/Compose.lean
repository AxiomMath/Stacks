module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback

/-!
# The calculus of composition of generalized arrows of a groupoid scheme

`Stacks.Groupoids.GroupoidScheme.compose` composes two composable generalized arrows of a
groupoid scheme. Collected here are the basic rules it obeys: its source and target, its
compatibility with precomposition in the test object, associativity, and the congruence rule
replacing the two arrows of a composite by equal ones.

## Main results

* `AlgebraicGeometry.groupoidCompose_source` and `AlgebraicGeometry.groupoidCompose_target`
  compute the source and target of a composite.
* `AlgebraicGeometry.groupoidCompose_pre` and `AlgebraicGeometry.groupoidCompose_precomp`
  are the two orientations of compatibility with precomposition.
* `AlgebraicGeometry.groupoidCompose_assoc` is associativity.
* `AlgebraicGeometry.groupoidCompose_arrow_eq` is the congruence rule.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The source of a composite is the source of its second arrow. -/
lemma groupoidCompose_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} (f g : T ⟶ G.arrows) (w : f ≫ G.source = g ≫ G.target) :
    G.compose f g w ≫ G.source = g ≫ G.source := by
  rw [GroupoidScheme.compose, Category.assoc, G.source_comp, pullback.lift_snd_assoc]

/-- The target of a composite is the target of its first arrow. -/
lemma groupoidCompose_target {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} (f g : T ⟶ G.arrows) (w : f ≫ G.source = g ≫ G.target) :
    G.compose f g w ≫ G.target = f ≫ G.target := by
  rw [GroupoidScheme.compose, Category.assoc, G.target_comp, pullback.lift_fst_assoc]

/-- Composition of generalized arrows commutes with precomposition in the test object. -/
lemma groupoidCompose_pre {S : Scheme.{u}} (G : GroupoidScheme S)
    {T U : Over S} (k : T ⟶ U) (f g : U ⟶ G.arrows)
    (w : f ≫ G.source = g ≫ G.target) :
    k ≫ G.compose f g w =
      G.compose (k ≫ f) (k ≫ g)
        (by simpa only [Category.assoc] using congrArg (fun z => k ≫ z) w) := by
  simp only [GroupoidScheme.compose, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
  · simp only [Category.assoc, pullback.lift_snd]

/-- Compatibility with precomposition, with the composability witness of the precomposed pair
supplied by the caller. -/
lemma groupoidCompose_precomp {S : Scheme.{u}} (G : GroupoidScheme S)
    {T W : Over S} (k : W ⟶ T) (f g : T ⟶ G.arrows)
    (w : f ≫ G.source = g ≫ G.target)
    (w' : (k ≫ f) ≫ G.source = (k ≫ g) ≫ G.target) :
    G.compose (k ≫ f) (k ≫ g) w' = k ≫ G.compose f g w := by
  exact (groupoidCompose_pre G k f g w).symm

/-- Associativity of composition of generalized arrows. -/
lemma groupoidCompose_assoc {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} (f g h : T ⟶ G.arrows)
    (wfg : f ≫ G.source = g ≫ G.target)
    (wgh : g ≫ G.source = h ≫ G.target)
    (w₁ : G.compose f g wfg ≫ G.source = h ≫ G.target)
    (w₂ : f ≫ G.source = G.compose g h wgh ≫ G.target) :
    G.compose (G.compose f g wfg) h w₁ = G.compose f (G.compose g h wgh) w₂ :=
  G.assoc T f g h wfg wgh w₁ w₂

/-- Two composites of equal pairs of generalized arrows agree. -/
lemma groupoidCompose_arrow_eq {S : Scheme.{u}} {G : GroupoidScheme S}
    {T : Over S} (f f' g g' : T ⟶ G.arrows)
    (wf : f ≫ G.source = g ≫ G.target) (wf' : f' ≫ G.source = g' ≫ G.target)
    (hf : f = f') (hg : g = g') : G.compose f g wf = G.compose f' g' wf' := by
  subst hf hg
  rfl

end AlgebraicGeometry

end
