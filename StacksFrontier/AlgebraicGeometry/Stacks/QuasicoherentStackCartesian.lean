module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StronglyCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentStack

/-!
# Strongly cartesian morphisms of quasi-coherent modules: `AlgebraicGeometry` spellings

That an arrow of quasi-coherent modules over the big fppf site is strongly cartesian exactly
when its canonical pullback comparison map is an isomorphism is
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StronglyCartesian`, in the namespace
`Stacks.QCoh`; Stacks 04U3 is registered there. This file carries the `AlgebraicGeometry.*`
spelling of that criterion.

## Main results

* `AlgebraicGeometry.qcohHom_isStronglyCartesian_iff`: the criterion.

## References

* [Stacks Project, Tag 04U3](https://stacks.math.columbia.edu/tag/04U3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {A C : QCohObject B S hS} (m : A ⟶ C)

/-- An arrow of quasi-coherent modules is strongly cartesian if and only if its canonical
pullback comparison map is an isomorphism; this is `Stacks.QCoh.isStronglyCartesian_iff`. -/
theorem qcohHom_isStronglyCartesian_iff :
    (qcohProjection (B := B) (S := S) (hS := hS)).IsStronglyCartesian
      ((qcohProjection (B := B) (S := S) (hS := hS)).map m) m ↔
      IsIso ((qcohHomEquivPullbackHom A C m).2) :=
  Stacks.QCoh.isStronglyCartesian_iff m

end AlgebraicGeometry

end
