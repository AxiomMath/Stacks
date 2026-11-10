module

public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentLiftingObstruction
public import StacksFrontier.Deformation.ToposThickening.LiftingObstructionSufficiency
import StacksCore.Tactic.StacksAttribute

/-!
# Clause (1) of Stacks 08U8, unconditionally

`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentLiftingObstruction.lean` states
clause (1) of [Stacks Project, Tag 08U8] for an abstract two-term complex, with the content of
Steps 1 to 3 of the source's proof — the bijection between the morphisms `X'₂ ⟶ X'₁` fitting
into the source's diagram and the factorizations of the difference homomorphism `ξ` through the
degree `0` term — carried as a hypothesis.

Steps 1, 2 and 3 hold for a `Deformation.ToposThickening.FirstOrderLiftDiagram`, which is the
source's diagram with the underlying topoi identified as in its own reduction. This file states
clause (1) with that content discharged: no hypothesis standing in for Steps 1 to 3, and no
base-point lift.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.liftDiagramTwoTerm`: the two-term structure of
  `NL(α)` for the presentation of Step 1 — `ℐ/ℐ²`, the degree `0` term, and the differential of
  the conormal sequence — realised in a triangulated category by a distinguished triangle.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff_liftDiagram`:
  **Stacks 08U8, clause (1)**, unconditionally. The class in `Ext¹(NL(α), 𝒢₂)` of the
  difference homomorphism `ξ` of Step 1 vanishes if and only if there is a morphism
  `X'₂ ⟶ X'₁` fitting into the source's diagram compatibly with `ν`.

## Implementation notes

**Why the two-term structure is taken as data rather than produced.**
`NaiveCotangentTwoTerm` bundles the conormal module, the degree `0` term and the differential as
*fields*, and `exists_naiveCotangentTwoTerm` only asserts that some two-term structure has a
given differential — the cone on a morphism is not canonical. So the unconditional statement
cannot be the conditional one with its hypothesis erased: it takes the three remaining pieces of
the triangle (`obj`, `incl`, `proj`) and its distinguishedness over
`single.map (reducedDifferential D)` as hypotheses, and `liftDiagramTwoTerm` assembles them with
the differential fixed to be the one of Step 1. The `Ext` group and the class in it are then the
ones of the source, not of an arbitrary complex.

**What is assumed, and what is not.** The hypotheses are: the instances making sheafification and
the sheaves of modules available on the site (those a `FirstOrderLiftDiagram` already carries, plus
`[J.HasSheafCompose (forget CommRingCat)]`, which the descent of Step 3 needs); a triangulated
category with a full, faithful, additive functor from the sheaves of modules into it; and the
distinguished triangle above. Nothing stands in for a result of the source: the equivalence between
the two sides is `FirstOrderLiftDiagram.nonempty_lift_iff_exists_factorization`, whose forward
direction is Step 2 and whose backward direction is Step 3.

**The set of lifts is the concrete one.** `Deformation.ToposThickening.FirstOrderLiftDiagram.Lift`
is a homomorphism of sheaves of commutative rings `𝒪_{X'₁} ⟶ 𝒪_{X'₂}` together with the three
compatibilities the source displays — over the two reductions, under the two structure maps from
the thickened bases, and inducing `ν` on the two ideals. So the right hand side of the
biconditional is the source's own set of morphisms, not a substitute for it.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Deformation.ToposThickening

universe v u w v' u'

namespace AlgebraicGeometry.RingedSpaceThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  (D : FirstOrderLiftDiagram.{v, u, max u v w} J)
  {T : Type u'} [Category.{v'} T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
  {single : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O) ⥤ T}
  [single.Full] [single.Faithful] [single.Additive]

/-- The two-term structure of the source's `NL(α)` for the presentation of Step 1: the conormal
module `ℐ/ℐ²`, the degree `0` term, and the differential of the conormal sequence, together with
a distinguished triangle realising the complex in a triangulated category.

The triangle is data: the differential is pinned to be the one of Step 1, and the remaining
three pieces are supplied, since the cone on a morphism is not canonical. -/
def liftDiagramTwoTerm (obj : T)
    (incl : single.obj (FirstOrderLiftDiagram.reducedDegreeZero D) ⟶ obj)
    (proj : obj ⟶ (single.obj (FirstOrderLiftDiagram.reducedConormal D))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (single.map (FirstOrderLiftDiagram.reducedDifferential D)) incl proj ∈
      distTriang T) :
    NaiveCotangentTwoTerm single where
  conormal := FirstOrderLiftDiagram.reducedConormal D
  base := FirstOrderLiftDiagram.reducedDegreeZero D
  d := FirstOrderLiftDiagram.reducedDifferential D
  obj := obj
  incl := incl
  proj := proj
  distinguished := hT

omit [J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] [single.Full] [single.Faithful]
  [single.Additive] in
/-- The differential of `liftDiagramTwoTerm` is the differential of the conormal sequence. -/
@[simp] theorem liftDiagramTwoTerm_d (obj : T)
    (incl : single.obj (FirstOrderLiftDiagram.reducedDegreeZero D) ⟶ obj)
    (proj : obj ⟶ (single.obj (FirstOrderLiftDiagram.reducedConormal D))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (single.map (FirstOrderLiftDiagram.reducedDifferential D)) incl proj ∈
      distTriang T) :
    (liftDiagramTwoTerm D obj incl proj hT).d = FirstOrderLiftDiagram.reducedDifferential D := rfl

/-- **Stacks 08U8, clause (1), on one site** (the ringed-space statement is
`DeformationIdealDiagram.obstructionClass_eq_zero_iff`). In the situation of the source's diagram,
reduced as in its proof to sheaves of rings on one site, the class in `Ext¹(NL(α), 𝒢₂)` of the
difference homomorphism `ξ` read off the two deformations in Step 1 vanishes if and only if there
is a morphism `X'₂ ⟶ X'₁` fitting into the diagram compatibly with `ν`.

Here `ξ` is `FirstOrderLiftDiagram.obstructionConormalHom`; a morphism filling the diagram
corresponds to a factorization of `ξ` through the degree `0` term, by
`FirstOrderLiftDiagram.nonempty_lift_iff_exists_factorization`. -/
theorem liftingObstruction_eq_zero_iff_liftDiagram (obj : T)
    (incl : single.obj (FirstOrderLiftDiagram.reducedDegreeZero D) ⟶ obj)
    (proj : obj ⟶ (single.obj (FirstOrderLiftDiagram.reducedConormal D))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (single.map (FirstOrderLiftDiagram.reducedDifferential D)) incl proj ∈
      distTriang T) :
    liftingObstruction (liftDiagramTwoTerm D obj incl proj hT) (FirstOrderLiftDiagram.pushedIdeal D)
        (FirstOrderLiftDiagram.obstructionConormalHom D) = 0 ↔
      Nonempty (FirstOrderLiftDiagram.Lift D) :=
  (NaiveCotangentTwoTerm.conormalExtClass_eq_zero_iff
      (liftDiagramTwoTerm D obj incl proj hT) (FirstOrderLiftDiagram.pushedIdeal D)
      (FirstOrderLiftDiagram.obstructionConormalHom D)).trans
    (FirstOrderLiftDiagram.nonempty_lift_iff_exists_factorization D).symm

end AlgebraicGeometry.RingedSpaceThickening

end
