module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent

/-!
# The descended difference of two lifts vanishes only when the two lifts agree

Let `a : X ⟶ Y` and `b : Y ⟶ T` be morphisms of algebraic spaces over a scheme `S`, let `C` be
a sheaf of `𝒪_X`-modules and let `f, g : A ⟶ 𝒜` be two lifts in the sense of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDescent.lean`: two morphisms of sheaves of
rings on the small étale site of `Y` whose sectionwise difference takes its values in a
square-zero ideal identified with `a_*C`.  Their difference descends to an `𝒪_X`-linear map

`θ : a^*Ω_{Y/T} ⟶ C`,

and `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_eq_zero` says that `θ = 0` when
`f = g`.  This file proves the converse: `θ = 0` forces `f = g`.

So the correspondence of [Stacks Project, Tag 0618] is *injective* on the pairs of lifts
sharing their first member — the half of that tag's content which says that a lift is
determined by its difference from a given one, at the level of comorphisms.

## Main results

* `AlgebraicGeometry.Space.diff_eq_zero_of_liftDifferenceDifferentialsHom_eq_zero`: if the
  descended map is zero then the sectionwise difference of the two lifts is zero.
* `AlgebraicGeometry.Space.eq_of_liftDifferenceDifferentialsHom_eq_zero`: if the descended map
  is zero then the two lifts are equal.
* `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_eq_zero_iff`: the two together, as an
  equivalence.

## Implementation notes

The argument runs backwards along the two steps of the descent, and each step is already a
bijection or an injection in the library.

The transposition of Equation [Stacks Project, Tag 0619] is additive — that is
`AlgebraicGeometry.Space.additive_modulePullback` and
`AlgebraicGeometry.Space.additive_modulePushforward` — so it carries the zero map to the zero
map, and the characterizing equation
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_spec` then reads the value of the
descended derivation at a section in the image of `q` as a value of the zero morphism.  That is
the first step: the sectionwise difference `L.diff` vanishes.  Note that no surjectivity of `q`
on sections is needed for it: the equation is stated at `q x`, and every section of `A` is of
that form on the nose.

The second step is the injectivity of the inclusion `ι` of the ideal of values, the field
`ι_injective` of `Stacks.Sites.SquareZeroValues`: from `L.diff x = 0` and the defining equation
`ι (L.diff x) = f x - g x` the two lifts agree on every section, and two morphisms of sheaves
of rings agreeing on every section are equal.

## What this does not give

This is a statement about the two *comorphisms*, not about two morphisms of algebraic spaces
inducing them.  Recovering a morphism of algebraic spaces from its comorphism is the
faithfulness half of Properties of Spaces, Theorem [Stacks Project, Tag 04KL], which this
development proves unconditionally, as
`AlgebraicGeometry.Space.eq_of_inducesSmallEtaleRingedToposHom`; nothing here uses or weakens
that.  What is removed is the other half of the uniqueness: that two lifts with equal
descended differences have equal comorphisms to begin with.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.Sites

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y T : AlgebraicSpaces B S hS} (b : Y ⟶ T)
  {A : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}}
  {q : A ⟶ structureRingSheaf B S hS Y} [Sheaf.IsLocallySurjective q]
  {X : AlgebraicSpaces B S hS} (a : X ⟶ Y) (C : Modules B S hS X.1 X.2)
  {E : SquareZeroValues ((modulePushforward B S hS a).obj C)}
  (L : LiftDifferenceData q E)
  (hz : ∀ (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : (inverseImageStructureSheaf B S hS b).obj.obj V),
    L.toQuotientDerivation.descend ((structureSharpInverseImage B S hS b).hom.app V s) = 0)

/-- **The sectionwise difference of two lifts whose descended map is zero vanishes.**  The
transposition of Equation [Stacks Project, Tag 0619] is additive, so it carries the zero map to
the zero morphism, and the characterizing equation of the descended map then reads the
difference at an arbitrary section as a value of that zero morphism. -/
theorem diff_eq_zero_of_liftDifferenceDifferentialsHom_eq_zero
    (h : liftDifferenceDifferentialsHom B S hS b a C L hz = 0)
    {V : (SmallEtale B S hS Y.1)ᵒᵖ} (x : A.obj.obj V) :
    L.diff x = 0 := by
  have hspec := liftDifferenceDifferentialsHom_spec B S hS b a C L hz x
  rw [h] at hspec
  have hzero : (modulePullbackAdjunction B S hS a).homEquiv
      (sheafOfDifferentials B S hS b) C 0 = 0 :=
    map_zero ((modulePullbackAdjunction B S hS a).homAddEquiv
      (sheafOfDifferentials B S hS b) C)
  rw [hzero] at hspec
  exact hspec.symm.trans rfl

/-- **Two lifts whose descended difference is zero are equal.**  The sectionwise difference
vanishes, and the inclusion of the ideal of values is injective, so the two morphisms of
sheaves of rings agree on every section. -/
theorem eq_of_liftDifferenceDifferentialsHom_eq_zero
    (h : liftDifferenceDifferentialsHom B S hS b a C L hz = 0) :
    L.f = L.g :=
  Sheaf.hom_ext (NatTrans.ext (funext fun V => RingCat.hom_ext (RingHom.ext fun x => by
    have hi := L.ι_diff x
    rw [diff_eq_zero_of_liftDifferenceDifferentialsHom_eq_zero B S hS b a C L hz h x,
      map_zero] at hi
    exact sub_eq_zero.1 hi.symm)))

/-- **The descended difference of two lifts is zero exactly when the two lifts agree.**  This is
the injectivity of the correspondence of [Stacks Project, Tag 0618] at the level of
comorphisms, together with the statement that a lift does not differ from itself. -/
theorem liftDifferenceDifferentialsHom_eq_zero_iff :
    liftDifferenceDifferentialsHom B S hS b a C L hz = 0 ↔ L.f = L.g :=
  ⟨eq_of_liftDifferenceDifferentialsHom_eq_zero B S hS b a C L hz,
    liftDifferenceDifferentialsHom_eq_zero B S hS b a C L hz⟩

end AlgebraicGeometry.Space

end
