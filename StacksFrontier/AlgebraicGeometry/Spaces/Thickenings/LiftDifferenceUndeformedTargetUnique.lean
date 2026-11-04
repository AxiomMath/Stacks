module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceUndeformedTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpFaithful

/-!
# A lift into an undeformed target is determined by its difference from a given one

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, let `b : W ⟶ V`
be a morphism and let `a : Z ⟶ W` be a morphism.  Two lifts `c, c' : X ⟶ W` of `a` over `V`
whose difference `AlgebraicGeometry.Space.undeformedLiftDiff` vanishes are equal.

This is the uniqueness half of [Stacks Project, Tag 04D0] for the lifting problem of
[Stacks Project, Tag 061A] with an undeformed target, and it is unconditional: it needs neither
Properties of Spaces, Theorem 04KL nor the identification of the small étale topoi of a
thickening.  Two steps, both already in the library:

* the descent of the difference is injective — Equation [Stacks Project, Tag 0619] is a
  bijection and the conormal module sits in the ambient sheaf of rings injectively
  (`AlgebraicGeometry.Space.eq_of_liftDifferenceDifferentialsHom_eq_zero`), so a vanishing
  difference means the two comorphisms read through the thickening agree;
* two morphisms agreeing on a first order thickening with equal comorphisms read through it are
  equal (`AlgebraicGeometry.Space.eq_of_structureSharpThroughThickeningAt_eq`).

## Main results

* `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_eq_of_undeformedLiftDiff_eq_zero`:
  a vanishing difference means the two comorphisms agree.
* `AlgebraicGeometry.Space.undeformedLiftDiff_eq_zero_iff`: the difference vanishes exactly when
  the two comorphisms agree.
* `AlgebraicGeometry.Space.eq_of_undeformedLiftDiff_eq_zero`: **two lifts with vanishing
  difference are equal.**
* `AlgebraicGeometry.Space.undeformedLiftDiff_injective`: **the difference from a fixed lift is
  injective on lifts**, which is the uniqueness half of [Stacks Project, Tag 04D0].

## References

* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W V : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (hZ : IsFirstOrderThickening B S hS X Z.1)
  (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W) (b : W ⟶ V)

/-- **Two lifts with vanishing difference have one and the same comorphism read through the
thickening.**  The difference is the descent of the difference of the two comorphisms, and that
descent is injective. -/
theorem structureSharpThroughThickeningAt_eq_of_undeformedLiftDiff_eq_zero (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a)
    (h' : subspaceInclusion B S hS X Z ≫ c' = a) (hb : c ≫ b = c' ≫ b)
    (hzero : undeformedLiftDiff B S hS Z hZ a b c c' h h' hb = 0) :
    structureSharpThroughThickeningAt B S hS Z c a h =
      structureSharpThroughThickeningAt B S hS Z c' a h' := by
  let := isLocallySurjective_sheafHom_id_structureRingSheaf B S hS (W := W)
  refine (undeformedLiftDifferenceData_f B S hS Z hZ a c c' h h').symm.trans
    (Eq.trans ?_ (undeformedLiftDifferenceData_g B S hS Z hZ a c c' h h'))
  exact eq_of_liftDifferenceDifferentialsHom_eq_zero B S hS b a (conormalModule B S hS X Z)
    (undeformedLiftDifferenceData B S hS Z hZ a c c' h h')
    (undeformedLiftDifferenceData_descend_eq_zero B S hS Z hZ a b c c' h h' hb)
    ((undeformedLiftDiff_eq B S hS Z hZ a b c c' h h' hb).symm.trans hzero)

/-- **The difference of two lifts vanishes exactly when their comorphisms read through the
thickening agree.** -/
theorem undeformedLiftDiff_eq_zero_iff (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a)
    (h' : subspaceInclusion B S hS X Z ≫ c' = a) (hb : c ≫ b = c' ≫ b) :
    undeformedLiftDiff B S hS Z hZ a b c c' h h' hb = 0 ↔
      structureSharpThroughThickeningAt B S hS Z c a h =
        structureSharpThroughThickeningAt B S hS Z c' a h' := by
  refine ⟨structureSharpThroughThickeningAt_eq_of_undeformedLiftDiff_eq_zero
    B S hS Z hZ a b c c' h h' hb, fun heq => ?_⟩
  rw [undeformedLiftDiff_eq B S hS Z hZ a b c c' h h' hb]
  let := isLocallySurjective_sheafHom_id_structureRingSheaf B S hS (W := W)
  exact liftDifferenceDifferentialsHom_eq_zero B S hS b a (conormalModule B S hS X Z)
    (undeformedLiftDifferenceData B S hS Z hZ a c c' h h')
    (undeformedLiftDifferenceData_descend_eq_zero B S hS Z hZ a b c c' h h' hb)
    ((undeformedLiftDifferenceData_f B S hS Z hZ a c c' h h').trans
      (heq.trans (undeformedLiftDifferenceData_g B S hS Z hZ a c c' h h').symm))

/-- **The uniqueness half of [Stacks Project, Tag 04D0] for an undeformed target.**  Two lifts
of `a` over `V` along the first order thickening `Z ⊂ X` whose difference vanishes are equal. -/
@[stacks 04D0 "the uniqueness half: a lift is determined by its difference from a given lift, \
for an UNDEFORMED target"]
theorem eq_of_undeformedLiftDiff_eq_zero (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a)
    (h' : subspaceInclusion B S hS X Z ≫ c' = a) (hb : c ≫ b = c' ≫ b)
    (hzero : undeformedLiftDiff B S hS Z hZ a b c c' h h' hb = 0) :
    c = c' :=
  eq_of_structureSharpThroughThickeningAt_eq B S hS Z hZ c c' a h h'
    (structureSharpThroughThickeningAt_eq_of_undeformedLiftDiff_eq_zero
      B S hS Z hZ a b c c' h h' hb hzero)

/-- **The difference from a fixed lift is injective on lifts.**  If two lifts have the same
difference from a third then they are equal: the difference of the two is the difference of the
two differences, by
`AlgebraicGeometry.Space.undeformedLiftDiff_add_undeformedLiftDiff`, hence zero.

This is the uniqueness half of [Stacks Project, Tag 04D0] in the form the torsor statement of
[Stacks Project, Tag 061C] consumes. -/
theorem undeformedLiftDiff_injective (c c₁ c₂ : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a)
    (h₁ : subspaceInclusion B S hS X Z ≫ c₁ = a)
    (h₂ : subspaceInclusion B S hS X Z ≫ c₂ = a)
    (hb₁ : c ≫ b = c₁ ≫ b) (hb₂ : c ≫ b = c₂ ≫ b) (hb₁₂ : c₁ ≫ b = c₂ ≫ b)
    (heq : undeformedLiftDiff B S hS Z hZ a b c c₁ h h₁ hb₁ =
      undeformedLiftDiff B S hS Z hZ a b c c₂ h h₂ hb₂) :
    c₁ = c₂ :=
  eq_of_undeformedLiftDiff_eq_zero B S hS Z hZ a b c₁ c₂ h₁ h₂ hb₁₂ <| add_eq_left.mp <|
    (undeformedLiftDiff_add_undeformedLiftDiff B S hS Z hZ a b c c₁ c₂
      h h₁ h₂ hb₁ hb₁₂ hb₂).trans heq.symm

end AlgebraicGeometry.Space

end
