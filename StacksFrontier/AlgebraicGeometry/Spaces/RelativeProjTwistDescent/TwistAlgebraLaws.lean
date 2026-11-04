module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistMulLaws
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraUnit

/-!
# The laws of the multiplication and the unit of the twists of a relative Proj

In Situation 0849 the multiplication `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` and the unit `𝒪_P ⟶ 𝒪_P(0)` of
the twists of `P = Proj_X(𝒜)` (`AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul`,
`AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraUnit`) are the descents along the
presentation `P = P_U/P_R` of the multiplication and the unit of the twists of Stacks 01NR on the
scheme of `P_U`.  This file records the laws of Stacks 084D for them: the multiplication is
associative and commutative and the unit is a left and a right unit, each up to the
identification of the degrees.  They are the laws of descended multiplications and units of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistMulLaws` at the twists, with
the compatibilities of Stacks 03DX (2) with inverse images supplied by
`AlgebraicGeometry.Space.representedC3TensorCompat` and
`AlgebraicGeometry.Space.representedC3UnitCompat`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul_assoc`: **the multiplication of
  the twists is associative.**
* `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul_comm`: **it is commutative.**
* `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraUnit_mul` and
  `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul_unit`: **the unit is a left and a
  right unit.**

## Implementation notes

As for `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul_spec`, the statements are
spelled through the descended multiplication and unit on the presentation `P = P_U/P_R` that
`twistAlgebraMul` and `twistAlgebraUnit` are by definition, with the twists spelled as the
descended modules they are by definition
(`AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedMul`,
`AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedUnit`,
`AlgebraicGeometry.Space.presentationDescendedModule`): the same equation written with
`twistAlgebraMul` and `twistModule` is definitionally equal, but the kernel exhausts its budget
comparing the two spellings of the category of `𝒪_P`-modules in it.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u m

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

/-- **The multiplication of the twists of the relative Proj is associative** (Stacks 084D): for
the multiplication `μ` of `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul`,
`(μ_{i,j} ▷ 𝒪_P(k)) ≫ μ_{i+j,k} = α ≫ (𝒪_P(i) ◁ μ_{j,k}) ≫ μ_{i,j+k}`, up to the identification of
the degrees `i + (j + k) = (i + j) + k`. -/
theorem twistAlgebraMul_assoc (i j k : ℤ) :
    type_of% (s.relativeProjPoints.spacePresentationDescendedMul_assoc Px
      s.isAlgebraicSpace_relativeProjFunctor (Mn := s.twistPieceQcoh Px.U Px.toSpace)
      (s.twistTransition Px)
      (s.presentationSchemeCocycle_twistTransition Px) (s.presentationSchemeUnit_twistTransition Px)
      (s.twistPieceMul Px.U Px.toSpace)
      (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
      (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
      (s.transitionMulCompat_twistTransition Px)
      (s.twistPieceMul_assoc Px.U Px.toSpace) i j k) :=
  s.relativeProjPoints.spacePresentationDescendedMul_assoc Px
    s.isAlgebraicSpace_relativeProjFunctor _ _ _ _
    (fun _ _ => representedC3TensorCompat ..)
    (fun _ _ => representedC3TensorCompat ..)
    (s.transitionMulCompat_twistTransition Px) (s.twistPieceMul_assoc Px.U Px.toSpace) i j k

/-- **The multiplication of the twists of the relative Proj is commutative** (Stacks 084D): for
the multiplication `μ` of `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul`,
`β ≫ μ_{j,i} = μ_{i,j}`, up to the identification of the degrees `i + j = j + i`. -/
theorem twistAlgebraMul_comm (i j : ℤ) :
    type_of% (s.relativeProjPoints.spacePresentationDescendedMul_comm Px
      s.isAlgebraicSpace_relativeProjFunctor (Mn := s.twistPieceQcoh Px.U Px.toSpace)
      (s.twistTransition Px)
      (s.presentationSchemeCocycle_twistTransition Px) (s.presentationSchemeUnit_twistTransition Px)
      (s.twistPieceMul Px.U Px.toSpace)
      (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
      (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
      (s.transitionMulCompat_twistTransition Px)
      (s.twistPieceMul_comm Px.U Px.toSpace) i j) :=
  s.relativeProjPoints.spacePresentationDescendedMul_comm Px
    s.isAlgebraicSpace_relativeProjFunctor _ _ _ _
    (fun _ _ => representedC3TensorCompat ..)
    (fun _ _ => representedC3TensorCompat ..)
    (s.transitionMulCompat_twistTransition Px) (s.twistPieceMul_comm Px.U Px.toSpace) i j

/-- **The unit of the twists of the relative Proj is a left unit** (Stacks 084D): for the unit
`η` of `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraUnit` and the multiplication `μ`
of `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul`,
`(η ▷ 𝒪_P(n)) ≫ μ_{0,n} = λ`, up to the identification of the degrees `n = 0 + n`. -/
theorem twistAlgebraUnit_mul (n : ℤ) :
    type_of% (s.relativeProjPoints.spacePresentationDescendedUnit_mul Px
      s.isAlgebraicSpace_relativeProjFunctor (Mn := s.twistPieceQcoh Px.U Px.toSpace)
      (s.twistTransition Px)
      (s.presentationSchemeCocycle_twistTransition Px) (s.presentationSchemeUnit_twistTransition Px)
      (s.twistPieceMul Px.U Px.toSpace)
      (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
      (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
      (s.transitionMulCompat_twistTransition Px)
      (s.twistPieceUnit Px.U Px.toSpace) (representedC3UnitCompat s.site s.base s.containsBase _)
      (representedC3UnitCompat s.site s.base s.containsBase _)
      (s.transitionUnitCompat_twistTransition Px) (s.twistPieceUnit_mul Px.U Px.toSpace) n) :=
  s.relativeProjPoints.spacePresentationDescendedUnit_mul Px
    s.isAlgebraicSpace_relativeProjFunctor _ _ _ _
    (fun _ _ => representedC3TensorCompat ..)
    (fun _ _ => representedC3TensorCompat ..) (s.transitionMulCompat_twistTransition Px)
    _ (representedC3UnitCompat ..) (representedC3UnitCompat ..)
    (s.transitionUnitCompat_twistTransition Px)
    (s.twistPieceUnit_mul Px.U Px.toSpace) n

/-- **The unit of the twists of the relative Proj is a right unit** (Stacks 084D): for the unit
`η` of `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraUnit` and the multiplication `μ`
of `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul`,
`(𝒪_P(n) ◁ η) ≫ μ_{n,0} = ρ`, up to the identification of the degrees `n = n + 0`. -/
theorem twistAlgebraMul_unit (n : ℤ) :
    type_of% (s.relativeProjPoints.spacePresentationDescendedMul_unit Px
      s.isAlgebraicSpace_relativeProjFunctor (Mn := s.twistPieceQcoh Px.U Px.toSpace)
      (s.twistTransition Px)
      (s.presentationSchemeCocycle_twistTransition Px) (s.presentationSchemeUnit_twistTransition Px)
      (s.twistPieceMul Px.U Px.toSpace)
      (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
      (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
      (s.transitionMulCompat_twistTransition Px)
      (s.twistPieceUnit Px.U Px.toSpace) (representedC3UnitCompat s.site s.base s.containsBase _)
      (representedC3UnitCompat s.site s.base s.containsBase _)
      (s.transitionUnitCompat_twistTransition Px) (s.twistPieceUnit_mul Px.U Px.toSpace)
      (s.twistPieceMul_comm Px.U Px.toSpace) n) :=
  s.relativeProjPoints.spacePresentationDescendedMul_unit Px
    s.isAlgebraicSpace_relativeProjFunctor _ _ _ _
    (fun _ _ => representedC3TensorCompat ..)
    (fun _ _ => representedC3TensorCompat ..) (s.transitionMulCompat_twistTransition Px)
    _ (representedC3UnitCompat ..) (representedC3UnitCompat ..)
    (s.transitionUnitCompat_twistTransition Px)
    (s.twistPieceUnit_mul Px.U Px.toSpace) (s.twistPieceMul_comm Px.U Px.toSpace) n

end AlgebraicGeometry.Space.RelativeProjSituation

end
