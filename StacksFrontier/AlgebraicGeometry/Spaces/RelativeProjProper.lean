module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProj.FiniteTypeConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjUniversallyClosed

/-!
# Properness of the relative Proj of an algebraic space

In the relative Proj situation of Stacks 0849, if the degree-zero part `𝒜₀` of the graded
algebra is a finite type module over the structure sheaf and `𝒜` is of finite type as an
`𝒜₀`-algebra, the structure morphism `π : Proj_X(𝒜) ⟶ X` is proper.

A proper morphism of algebraic spaces is one which is separated, of finite type and universally
closed, which is `AlgebraicGeometry.Space.IsProper` of Stacks 03ZM, so the conclusion is
assembled from three results already in the library and none of the three needs more than the
two hypotheses above:

* separatedness is Stacks 084E, which has no hypothesis on the algebra at all;
* finite type is Stacks 084G, whose hypothesis is finite type of `𝒜` over the structure sheaf,
  and that is the other condition of Stacks 084I, obtained from the two hypotheses by the
  equivalence `Stacks.RelativeProj.Situation.properFiniteType_tfae`;
* universal closedness is Stacks 084H, whose hypothesis is that `𝒪_X → 𝒜₀` be integral, and a
  finite ring map is integral.

Both translations of the hypotheses are the two scheme-level lemmas
`Stacks.RelativeProj.Situation.isIntegralInDegreeZero_of_isDegreeZeroFiniteType` and
`Stacks.RelativeProj.Situation.isFiniteType_of_isDegreeZeroFiniteType`, proved below from the
equivalence assertion of Stacks 084I in
`StacksFrontier/AlgebraicGeometry/RelativeProj/FiniteTypeConditions.lean`.

## Main results

* `AlgebraicGeometry.Space.isProper_relativeProj` is the properness assertion of Stacks 084I for
  a morphism presented on a chart as the relative Proj of a scheme-level situation `t`.  The tag
  itself, with its hypotheses read on the graded algebra of Situation 0849, is registered on
  `AlgebraicGeometry.Space.RelativeProjSituation.properFiniteType_tfae_and_isProper` in
  `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjFiniteTypeConditions.lean`.

## Implementation notes

As for Stacks 084E, 084F and 084G in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProj.lean` and Stacks 084H in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjUniversallyClosed.lean`, the relative Proj
enters through a surjective étale scheme chart of the base, as a
`AlgebraicGeometry.Space.RelativeProjChart`. That structure is what Stacks 084B supplies, and
`AlgebraicGeometry.Space.exists_relativeProjChart` shows the chart hypothesis is inhabited for
every situation of Stacks 01NN, so the statement is not vacuous.

The two hypotheses are read on the situation living on the chart, which is the restriction
`g^*𝒜` of the algebra on the base, exactly as in Stacks 084F, 084G and 084H. That is not a
weakening: both conditions are affine-local on the base, so for a quasi-coherent graded algebra
on the base they hold exactly when they hold for the restriction to a surjective étale chart.

The source states the properness assertion under either of the two equivalent conditions of
Stacks 084I. It is stated here under the first, that `𝒜₀` be of finite type over the structure
sheaf and `𝒜` of finite type over `𝒜₀`; the second condition gives the first by
`Stacks.RelativeProj.Situation.properFiniteType_tfae`, which is the equivalence assertion of the
same tag, so `AlgebraicGeometry.Space.isProper_relativeProj_of_isFiniteTypeOverBase` records
that reading too.

## References

* [Stacks Project, Tag 084I](https://stacks.math.columbia.edu/tag/084I)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084E](https://stacks.math.columbia.edu/tag/084E)
* [Stacks Project, Tag 084G](https://stacks.math.columbia.edu/tag/084G)
* [Stacks Project, Tag 084H](https://stacks.math.columbia.edu/tag/084H)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### The hypotheses of the properness clause, on a scheme -/

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-- The degree-zero part being a finite type module over the structure sheaf makes it integral
over the structure sheaf, which is the first hypothesis of Stacks 07ZZ: over each affine open of
the base this is Stacks 00GK, a finite ring map is integral. -/
theorem isIntegralInDegreeZero_of_isDegreeZeroFiniteType (h : s.IsDegreeZeroFiniteType) :
    s.IsIntegralInDegreeZero :=
  fun U hU => (h U hU).to_isIntegral

/-- The two conditions in the first form of Stacks 084I give the finite type hypothesis
`Stacks.RelativeProj.Situation.IsFiniteType` of Stacks 07ZY: the equivalence turns finite type
over the degree-zero part into finite type over the structure sheaf, read over every affine open
of the base, and that implies the one-neighbourhood form. -/
theorem isFiniteType_of_isDegreeZeroFiniteType (hzero : s.IsDegreeZeroFiniteType)
    (hft : s.IsFiniteTypeOverDegreeZero) : s.IsFiniteType := by
  have hiff := (properFiniteType_tfae s).out 1 2
  exact isFiniteType_of_isFiniteTypeOverBase s (hiff.mp ⟨hzero, hft⟩).2

end Stacks.RelativeProj.Situation

namespace AlgebraicGeometry.Space

section Main

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a morphism `π : P ⟶ X` of algebraic spaces presented on a surjective étale chart as the
relative Proj of a situation `t`, if the degree-zero part of `t` is a finite type module over the
structure sheaf and `t` is of finite type over its degree-zero part, then `π` is proper. -/
theorem isProper_relativeProj {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hX : IsAlgebraicSpace B S hS X) (π : P ⟶ X)
    {t : Stacks.RelativeProj.Situation.{u}} (d : RelativeProjChart B S hS π t)
    (hzero : t.IsDegreeZeroFiniteType) (hft : t.IsFiniteTypeOverDegreeZero) :
    IsProper B S hS π :=
  ⟨isSeparated_relativeProj B S hS hP π d,
    isFiniteType_relativeProj B S hS hP hX π d
      (t.isFiniteType_of_isDegreeZeroFiniteType hzero hft),
    universallyClosed_relativeProj B S hS hX π d
      (t.isIntegralInDegreeZero_of_isDegreeZeroFiniteType hzero) hft⟩

/-- The properness assertion of Stacks 084I read under the second of its two equivalent
conditions: the degree-zero part is a finite type module over the structure sheaf and the graded
algebra is of finite type over the structure sheaf. The two conditions are interchanged by
`Stacks.RelativeProj.Situation.properFiniteType_tfae`, the equivalence assertion of the same
tag. -/
theorem isProper_relativeProj_of_isFiniteTypeOverBase
    {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hX : IsAlgebraicSpace B S hS X) (π : P ⟶ X)
    {t : Stacks.RelativeProj.Situation.{u}} (d : RelativeProjChart B S hS π t)
    (hzero : t.IsDegreeZeroFiniteType) (hft : t.IsFiniteTypeOverBase) :
    IsProper B S hS π := by
  have hiff := (Stacks.RelativeProj.Situation.properFiniteType_tfae t).out 2 1
  exact isProper_relativeProj B S hS hP hX π d hzero (hiff.mp ⟨hzero, hft⟩).2

end Main

end AlgebraicGeometry.Space

end
