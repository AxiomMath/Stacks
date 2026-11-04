module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules

/-!
# Arrows of a kernel-pair groupoid, as lifts of pairs of morphisms

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and let `φ : U ⟶ X` be a morphism with
`R = U ×_X U` and `t`, `s` the two projections — the situation of Stacks 03M3.  Then a pair of
morphisms `a, b : P ⟶ U` with `a ≫ φ = b ≫ φ` has a *unique* lift to a morphism `P ⟶ R` whose
composites with the target and the source are `a` and `b`.  This file defines that lift and
proves its unit, naturality and composition identities.

## Main definitions

* `AlgebraicGeometry.Space.arrowLift`: the unique arrow of the groupoid with prescribed target
  and source.
* `AlgebraicGeometry.Space.composablePairLift`: two consecutive lifts, as a morphism into the
  space of composable pairs of arrows.

## Main results

* `AlgebraicGeometry.Space.arrowLift_comp_target` and
  `AlgebraicGeometry.Space.arrowLift_comp_source`: the two composites of the lift.
* `AlgebraicGeometry.Space.arrowLift_unique`: **the lift is unique**.
* `AlgebraicGeometry.Space.arrowLift_self`: **the lift of a pair of equal morphisms is the unit
  arrow** along them.
* `AlgebraicGeometry.Space.comp_arrowLift`: **the lift is natural in the test space.**
* `AlgebraicGeometry.Space.composablePairLift_comp_comp`: **the composite of two consecutive
  lifts is the lift of the outer pair.**

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
  (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
  {P Q : AlgebraicSpaces B S hS}

/-- **The arrow of a kernel-pair groupoid with prescribed target and source.**  At `R = U ×_X U`
a pair of morphisms `a, b : P ⟶ U` with equal composites to `X` is the pair of composites of a
morphism `P ⟶ R` with the target and the source projections, and of exactly one such. -/
def arrowLift (a b : P ⟶ G.objects) (hab : a ≫ φ = b ≫ φ) : P ⟶ G.arrows :=
  ObjectProperty.homMk (hpb.lift a.hom b.hom (congrArg (fun f : P ⟶ X => f.hom) hab))

/-- The composite of the lift with the target projection is the first of the two morphisms. -/
@[simp]
theorem arrowLift_comp_target (a b : P ⟶ G.objects) (hab : a ≫ φ = b ≫ φ) :
    arrowLift B S hS G φ hpb a b hab ≫ G.target = a := by
  apply ObjectProperty.hom_ext
  exact hpb.lift_fst _ _ _

/-- The composite of the lift with the source projection is the second of the two morphisms. -/
@[simp]
theorem arrowLift_comp_source (a b : P ⟶ G.objects) (hab : a ≫ φ = b ≫ φ) :
    arrowLift B S hS G φ hpb a b hab ≫ G.source = b := by
  apply ObjectProperty.hom_ext
  exact hpb.lift_snd _ _ _

/-- **The lift is unique**: a morphism into the arrow space is determined by its composites with
the target and the source projections. -/
theorem arrowLift_unique {a b : P ⟶ G.objects} (hab : a ≫ φ = b ≫ φ) (v : P ⟶ G.arrows)
    (ha : v ≫ G.target = a) (hb : v ≫ G.source = b) :
    v = arrowLift B S hS G φ hpb a b hab := by
  apply ObjectProperty.hom_ext
  refine hpb.hom_ext ?_ ?_
  · exact (congrArg (fun f : P ⟶ G.objects => f.hom) ha).trans (hpb.lift_fst _ _ _).symm
  · exact (congrArg (fun f : P ⟶ G.objects => f.hom) hb).trans (hpb.lift_snd _ _ _).symm

/-- **The lift of a pair of equal morphisms is the unit arrow** along that morphism: the lift of
`(a, a)` is `a ≫ e`, for `e` the unit of the groupoid. -/
theorem arrowLift_self (a : P ⟶ G.objects) :
    arrowLift B S hS G φ hpb a a rfl = a ≫ GroupoidInAlgebraicSpaces.identityArrow G :=
  (arrowLift_unique B S hS G φ hpb rfl _
    (by rw [Category.assoc, GroupoidInAlgebraicSpaces.identityArrow_comp_target,
      Category.comp_id])
    (by rw [Category.assoc, GroupoidInAlgebraicSpaces.identityArrow_comp_source,
      Category.comp_id])).symm

/-- **The lift is natural in the test space**: precomposing the lift of a pair is the lift of the
precomposed pair. -/
theorem comp_arrowLift (q : Q ⟶ P) (a b : P ⟶ G.objects) (hab : a ≫ φ = b ≫ φ)
    (hab' : (q ≫ a) ≫ φ = (q ≫ b) ≫ φ) :
    q ≫ arrowLift B S hS G φ hpb a b hab = arrowLift B S hS G φ hpb (q ≫ a) (q ≫ b) hab' :=
  arrowLift_unique B S hS G φ hpb hab' _
    (by rw [Category.assoc, arrowLift_comp_target]) (by rw [Category.assoc, arrowLift_comp_source])

/-- **Two consecutive lifts, as a morphism into the space of composable pairs of arrows**: the
pair formed by the lift of `(a, b)` and the lift of `(b, c)`, as a morphism into the fibre product
of the source and target projections. -/
def composablePairLift (a b c : P ⟶ G.objects) (hab : a ≫ φ = b ≫ φ) (hbc : b ≫ φ = c ≫ φ) :
    P ⟶ AlgebraicSpaces.fiberProduct B S hS G.source G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift
    (arrowLift B S hS G φ hpb a b hab) (arrowLift B S hS G φ hpb b c hbc)
    (by rw [arrowLift_comp_source, arrowLift_comp_target])

/-- The first projection of the composable pair of two consecutive lifts is the first lift. -/
@[simp]
theorem composablePairLift_comp_firstArrow (a b c : P ⟶ G.objects) (hab : a ≫ φ = b ≫ φ)
    (hbc : b ≫ φ = c ≫ φ) :
    composablePairLift B S hS G φ hpb a b c hab hbc ≫
        GroupoidInAlgebraicSpaces.firstArrow G =
      arrowLift B S hS G φ hpb a b hab :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift_fst _ _ _

/-- The second projection of the composable pair of two consecutive lifts is the second lift. -/
@[simp]
theorem composablePairLift_comp_secondArrow (a b c : P ⟶ G.objects) (hab : a ≫ φ = b ≫ φ)
    (hbc : b ≫ φ = c ≫ φ) :
    composablePairLift B S hS G φ hpb a b c hab hbc ≫
        GroupoidInAlgebraicSpaces.secondArrow G =
      arrowLift B S hS G φ hpb b c hbc :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift_snd _ _ _

/-- **The composite of two consecutive lifts is the lift of the outer pair**: composing the lifts
of `(a, b)` and `(b, c)` gives the lift of `(a, c)`. -/
theorem composablePairLift_comp_comp (a b c : P ⟶ G.objects) (hab : a ≫ φ = b ≫ φ)
    (hbc : b ≫ φ = c ≫ φ) (hac : a ≫ φ = c ≫ φ) :
    composablePairLift B S hS G φ hpb a b c hab hbc ≫ G.comp =
      arrowLift B S hS G φ hpb a c hac :=
  arrowLift_unique B S hS G φ hpb hac _
    (by rw [Category.assoc, GroupoidInAlgebraicSpaces.comp_comp_target,
      ← Category.assoc, composablePairLift_comp_firstArrow, arrowLift_comp_target])
    (by rw [Category.assoc, GroupoidInAlgebraicSpaces.comp_comp_source,
      ← Category.assoc, composablePairLift_comp_secondArrow, arrowLift_comp_source])

end AlgebraicGeometry.Space

end
