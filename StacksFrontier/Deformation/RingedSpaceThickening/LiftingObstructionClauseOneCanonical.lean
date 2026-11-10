module

public import StacksFrontier.Deformation.RingedSpaceThickening.LiftingObstructionClauseOne
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTwoTermOfDouble

/-!
# The canonical element of clause (1) of Stacks 08U8

`AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff_liftDiagram` of
`StacksFrontier/Deformation/RingedSpaceThickening/LiftingObstructionClauseOne.lean` states clause
(1) of [Stacks Project, Tag 08U8] for a two-term structure on `NL(α)` *supplied as data*: the
underlying object of the complex, the inclusion of its degree `0` term, the projection onto the
shift of its degree `-1` term, and the distinguishedness of the resulting triangle.  Nothing
produced that datum, so the statement had no instance.

This file produces it, in the derived category of the sheaves of modules on the site, and with it
the canonical element clause (1) names: the class in `Ext¹(NL(α), 𝒢₂)` of the difference
homomorphism `ξ` of Step 1 of the source's proof.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.liftDiagramNaiveCotangentTwoTerm`: the canonical
  two-term structure of `NL(α)` for the presentation of Step 1, in
  `D(𝒪_{X₁})`: the complex `HomologicalComplex.double (ℐ/ℐ² ⟶ Ω)` in degrees `-1` and `0`, with
  the distinguished triangle identifying it with the cone of `(ℐ/ℐ² ⟶ Ω)[0]`.
* `AlgebraicGeometry.RingedSpaceThickening.liftDiagramObstructionClass`: **the canonical element
  of clause (1)** — the class in `Ext¹_{𝒪_{X₁}}(NL(α), g_*𝒢₂)` of `ξ`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.liftDiagramObstructionClass_eq_zero_iff`: that
  element vanishes if and only if there is a morphism `X'₂ ⟶ X'₁` fitting into the source's
  diagram compatibly with `ν`.  It is
  `liftingObstruction_eq_zero_iff_liftDiagram` at the canonical datum, so clause (1) is now a
  statement about a constructed class and not about supplied data.
* `AlgebraicGeometry.RingedSpaceThickening.liftDiagramNaiveCotangentTwoTerm_obj`,
  `..._conormal`, `..._base`, `..._d`: the two-term structure is the one of Step 1 — its
  differential is `FirstOrderLiftDiagram.reducedDifferential D` and its underlying object is the
  image of the complex `HomologicalComplex.double` of that differential in the derived category.

## Implementation notes

**Where the datum comes from.**  `NaiveCotangentTwoTerm.ofDoubleNegOne` of
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentTwoTermOfDouble.lean` turns a
morphism `d : ℐ/ℐ² ⟶ Ω` of an abelian category with a derived category into a
`NaiveCotangentTwoTerm` for `DerivedCategory.singleFunctor _ 0` whose underlying object is
`HomologicalComplex.double d` in degrees `-1` and `0`; its triangle is
`CochainComplex.doubleTriangleQ_distinguished`, the identification of a `double` with the mapping
cone of the induced map of single complexes.  Taking `d` to be
`Deformation.ToposThickening.FirstOrderLiftDiagram.reducedDifferential D` gives exactly the datum
`liftDiagramTwoTerm` asks for, with the three remaining fields determined; the two structures
agree by `rfl`, which is what makes `liftDiagramObstructionClass_eq_zero_iff` an instance of the
clause and not a reproof of it.

**The triangulated category is the derived category, and the embedding is the single functor.**
`liftingObstruction_eq_zero_iff_liftDiagram` asks for an abstract triangulated `T` with a full,
faithful, additive functor from the sheaves of modules; here `T` is
`DerivedCategory (SheafOfModules _)` for the standard model
(`HasDerivedCategory.standard`, a local instance as elsewhere in this directory) and the functor
is `DerivedCategory.singleFunctor _ 0`, which is full and faithful by
`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`.  No hypothesis is added: the instances
are the ones a `FirstOrderLiftDiagram` already carries, since they are what makes the category of
sheaves of modules abelian.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open Deformation.ToposThickening

universe v u w

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local instance] HasDerivedCategory.standard

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

/-- **The canonical two-term structure of `NL(α)` for the presentation of Step 1.**  Its
conormal term is `ℐ/ℐ²`, its degree `0` term is `Ω`, its differential is
`FirstOrderLiftDiagram.reducedDifferential D`, and its underlying object is the image in
`D(𝒪_{X₁})` of the complex `HomologicalComplex.double` of that differential in degrees `-1`
and `0`. -/
def liftDiagramNaiveCotangentTwoTerm :
    NaiveCotangentTwoTerm (DerivedCategory.singleFunctor
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O)) 0) :=
  NaiveCotangentTwoTerm.ofDoubleNegOne (FirstOrderLiftDiagram.reducedDifferential D)

omit [J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})] in
/-- The conormal term of `liftDiagramNaiveCotangentTwoTerm D` is
`FirstOrderLiftDiagram.reducedConormal D`. -/
@[simp] theorem liftDiagramNaiveCotangentTwoTerm_conormal :
    (liftDiagramNaiveCotangentTwoTerm D).conormal = FirstOrderLiftDiagram.reducedConormal D := rfl

omit [J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})] in
/-- The degree `0` term of `liftDiagramNaiveCotangentTwoTerm D` is
`FirstOrderLiftDiagram.reducedDegreeZero D`. -/
@[simp] theorem liftDiagramNaiveCotangentTwoTerm_base :
    (liftDiagramNaiveCotangentTwoTerm D).base = FirstOrderLiftDiagram.reducedDegreeZero D := rfl

omit [J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})] in
/-- The differential of `liftDiagramNaiveCotangentTwoTerm D` is
`FirstOrderLiftDiagram.reducedDifferential D`. -/
@[simp] theorem liftDiagramNaiveCotangentTwoTerm_d :
    (liftDiagramNaiveCotangentTwoTerm D).d = FirstOrderLiftDiagram.reducedDifferential D := rfl

omit [J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})] in
/-- The underlying object of `liftDiagramNaiveCotangentTwoTerm D` is the image in the derived
category of the complex `HomologicalComplex.double` of
`FirstOrderLiftDiagram.reducedDifferential D` in degrees `-1` and `0`. -/
@[simp] theorem liftDiagramNaiveCotangentTwoTerm_obj :
    (liftDiagramNaiveCotangentTwoTerm D).obj =
      DerivedCategory.Q.obj (double (FirstOrderLiftDiagram.reducedDifferential D)
        ComplexShape.upIntRelNegOneZero) := rfl

/-- **The canonical element of clause (1) of [Stacks Project, Tag 08U8].**  The class in
`Ext¹_{𝒪_{X₁}}(NL(α), g_*𝒢₂)` of the difference homomorphism `ξ` of Step 1 of the source's
proof, taken at the canonical two-term structure of `NL(α)`.

`ξ` is `FirstOrderLiftDiagram.obstructionConormalHom D`, built in Step 1 from the two
`𝒪_{S'₁}`-algebra restrictions of the fibre product `𝒪_{X'₁} ×_{𝒪_{X₂}} 𝒪_{X'₂}`; the class is
its image under `NaiveCotangentTwoTerm.conormalExtClass`, that is the projection of `NL(α)` onto
`(ℐ/ℐ²)[1]` followed by the shift of `ξ[0]`. -/
def liftDiagramObstructionClass :
    (liftDiagramNaiveCotangentTwoTerm D).obj ⟶
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O)) 0).obj
          (FirstOrderLiftDiagram.pushedIdeal D))⟦(1 : ℤ)⟧ :=
  liftingObstruction (liftDiagramNaiveCotangentTwoTerm D) (FirstOrderLiftDiagram.pushedIdeal D)
    (FirstOrderLiftDiagram.obstructionConormalHom D)

/-- **Stacks 08U8, clause (1), on one site, at the canonical class.**  The canonical element of
clause (1) vanishes if and only if there is a morphism `X'₂ ⟶ X'₁` fitting into the source's
diagram compatibly with `ν`.

This is `liftingObstruction_eq_zero_iff_liftDiagram` at the canonical two-term datum: the
hypotheses `obj`, `incl`, `proj` and `hT` that it carries are discharged by
`NaiveCotangentTwoTerm.ofDoubleNegOne`, so no data beyond the `FirstOrderLiftDiagram` remains. -/
theorem liftDiagramObstructionClass_eq_zero_iff :
    liftDiagramObstructionClass D = 0 ↔ Nonempty (FirstOrderLiftDiagram.Lift D) :=
  liftingObstruction_eq_zero_iff_liftDiagram D
    (DerivedCategory.Q.obj (double (FirstOrderLiftDiagram.reducedDifferential D)
      ComplexShape.upIntRelNegOneZero))
    (CochainComplex.doubleInclQ (FirstOrderLiftDiagram.reducedDifferential D)
      ComplexShape.upIntRelNegOneZero)
    (CochainComplex.doubleProjQ (FirstOrderLiftDiagram.reducedDifferential D)
      ComplexShape.upIntRelNegOneZero)
    (CochainComplex.doubleTriangleQ_distinguished (FirstOrderLiftDiagram.reducedDifferential D)
      ComplexShape.upIntRelNegOneZero)

end AlgebraicGeometry.RingedSpaceThickening

end
