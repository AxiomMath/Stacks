module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistFinitePresentation
public import StacksFrontier.AlgebraicGeometry.RelativeProjFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjFinitePresentation.Twists

/-!
# Finite presentation of a relative homogeneous spectrum and of its twists

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra whose structure map is of finite
presentation over every affine open of the base. Stacks tag 0D4D asserts two things about the
relative homogeneous spectrum `X = Proj_S(A)`: its structure morphism `X ⟶ S` is of finite
presentation, and every twist `𝒪_X(t)` is a module of finite presentation. The first assertion is
`Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.finitePresentation_toBase`; this file
proves the second, by discharging the absolute hypothesis of
`Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.isFinitePresentation_twist_of_charts` on
each affine chart.

On an affine open `U` of the base the graded ring of sections `A(U)` is a finitely presented
algebra over `Γ(S, U)`, whose structure map lands in degree zero, so every twist on the absolute
`Proj A(U)` is a module of finite presentation by
`Stacks.ProjTwistFinitePresentation.isFinitePresentation_twistingSheaf`. That is exactly the
hypothesis the reduction consumes.

## Main results

* `isFinitePresentation_twistingSheaf_grading`, in this file's namespace: every twist on the
  absolute homogeneous spectrum of the graded ring of sections over an open on which the structure
  map is of finite presentation is a module of finite presentation.
* `Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.isFinitePresentation_twist`: every
  twist on a relative homogeneous spectrum of a graded algebra of finite presentation is a module
  of finite presentation. This is the second assertion of Stacks tag 0D4D.

## Implementation notes

The twist data is a parameter, because no canonical term of
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is constructed in this development; this
is therefore the general form of the assertion, of which the statement for any particular glued
family of twists is an instance. That is the convention of every other result about the twists
here, and nothing is lost: tag 01NR need not be proved first.

The base ring of the absolute statement is `Γ(S, U)` rather than the degree-zero part of `A(U)`,
which is in general larger; the absolute statement is phrased for an arbitrary base ring mapping
into degree zero precisely so that it can be applied in this form.

## References

* [Stacks Project, Tag 0D4D](https://stacks.math.columbia.edu/tag/0D4D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjFinitePresentation

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

include A in
/-- **Every twist on the absolute homogeneous spectrum of the graded ring of sections is a module
of finite presentation**, over an open of the base on which the structure map of the graded
algebra is of finite presentation.

The graded ring of sections is then a finitely presented algebra over the ring of functions on the
open, and the structure map lands in degree zero, which is the hypothesis of
`Stacks.ProjTwistFinitePresentation.isFinitePresentation_twistingSheaf`. -/
public theorem isFinitePresentation_twistingSheaf_grading (U : S.Opens)
    (hA : (A.strHom U).FinitePresentation) (t : ℤ) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (twistingSheaf (A.grading U) t) := by
  let _ := A.sectionRingAlgebra U
  let _ : Algebra.FinitePresentation Γ(S, U) (A.sectionRing U) :=
    RingHom.finitePresentation_algebraMap.mp hA
  exact Stacks.ProjTwistFinitePresentation.isFinitePresentation_twistingSheaf
    (A.grading U) (A.strHom_mem U) t

include A in
/-- **Stacks 0D4D, second assertion.** Every twist on the relative homogeneous spectrum of a
quasi-coherent graded algebra whose structure map is of finite presentation over every affine open
of the base is a module of finite presentation.

The relative `Proj` is covered by the images under the charts of the standard opens of the
absolute `Proj`s of the graded rings of sections, on each of which the glued twist is an absolute
twist; that reduction is
`Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.isFinitePresentation_twist_of_charts`,
and the absolute statement it consumes is
`isFinitePresentation_twistingSheaf_grading`.

The twist data is a parameter, for the reason given in the implementation notes of this file. -/
@[stacks 0D4D "twists_finite_presentation"]
public theorem isFinitePresentation_twist (D : TwistData A)
    (hA : ∀ U : S.Opens, IsAffineOpen U → (A.strHom U).FinitePresentation) (t : ℤ) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (D.algebra.piece t) :=
  isFinitePresentation_twist_of_charts A D t fun U hU =>
    isFinitePresentation_twistingSheaf_grading A U (hA U hU) t

add_to_stacks 0D4D "relative_proj_finite_presentation"
  Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.finitePresentation_toBase

end Stacks.AlgebraicGeometry.RelativeProjFinitePresentation

end
