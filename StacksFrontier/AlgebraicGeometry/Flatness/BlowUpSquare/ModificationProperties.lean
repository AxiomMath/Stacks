module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.LocallyFreeLocus
public import StacksCore.Tactic.StacksAttribute

/-!
# The collected properties of the complex-and-divisor modification

Let `(X, D, M)` be a triple as in Situation 0F8S.  Stacks tag 0F9Y collects, in one statement,
everything that Section 0F8R proves about the morphism `b : X' ⟶ X` of tag 0GTY and the object
`Q = Lη_{ℐ'}Lb^*M` of tag 0F8U: that `b` is proper, an isomorphism over `X ∖ D` and over the
locally free locus `W`, that `D' = b⁻¹D` is an effective Cartier divisor, that `Q` is perfect,
that a finitely presented closed subscheme of `D'` carries `Li^*Q` with locally free cohomology
of the original ranks, the affine-chart description of `b` and of `Q`, and the preservation of
having a locally bounded finite locally free representative.

The complete statement of tag 0F9Y is
`AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase_modification` (for the morphism
of tag 0GTY) and `AlgebraicGeometry.ComplexAndDivisorSituation.exists_isProper_modification`
(in existential form).  This file supplies two of its ingredients for any morphism `b` with
properties (1) and (2) of tag 0GTY: **clause (1)**, that `b` is an isomorphism over the
complement of the divisor, and clauses (5) and (9) bundled with it.  The source leaves clause (1)
to the admissibility of the blowing up; here it follows from the universal property alone,
because the inclusion of `X ∖ D` is good for the triple for the cheapest possible reason — the
pulled-back divisor has no points, so there is no point at which a chart with principal
determinantal ideals has to be produced.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.divisorComplement`: the open subscheme
  `X ∖ D` of `X`.

## Main results

* `Stacks.Divisors.isEffectiveCartierDivisor_of_supportSet_eq_empty`: an ideal sheaf with no
  points in its support is an effective Cartier divisor; the affine-local criterion for being
  one is tested only at the points of the support.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_of_forall_notMem_supportSet`: a
  morphism whose image misses `D` is good for the triple; the inclusion of `X ∖ D` and the
  restriction `b⁻¹(X ∖ D) ⟶ X` of any `b` are therefore good for the triple.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isIso_resLE_divisorComplement`:
  clause (1) of Stacks tag 0F9Y, `b` is an isomorphism over `X ∖ D`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isIso_and_isPerfect_and_exists_rep`:
  clauses (1), (5) and (9) of Stacks tag 0F9Y together, for a representable `M`.

## Relation to the complete statement

Clause (1) is proved here from properties (1) and (2) of tag 0GTY.  The bundle
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isIso_and_isPerfect_and_exists_rep`
derives clause (5), perfectness of `Q`, from clause (9), the locally bounded finite locally free
representative of `Q` given by tag 0GU0 when `M` has such a representative.  The morphism of
tag 0GTY itself, `AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase`, its
properness, the remaining clauses (2)--(4) and (6)--(8), and perfectness of `Q` with no
assumption on `M` (tag 0F8U,
`AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_etaDerivedPullbackObject_goodBlowup`)
are proved in `StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupModification` and
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ModificationCollected`, which state tag 0F9Y
in full.

## Implementation notes

"Isomorphism over `V`" is `IsIso (b.resLE V (b ⁻¹ᵁ V) le_rfl)`, the spelling of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.LocallyFreeLocus`, so that clauses (1) and
(2) read the same way and the universal-property argument
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isIso_resLE_of_isGoodOver` applies
to both.

Perfectness of `Q` is obtained from clause (9) rather than from
`AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_etaDerivedPullbackObject`: tag 0GU0
produces the locally bounded finite locally free representative of `Q` from one for `M`,
and such a complex is perfect by
`Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree`.  This way one
hypothesis on `M` serves both clauses.

## References

* [Stacks Project, Tag 0F9Y](https://stacks.math.columbia.edu/tag/0F9Y)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0F8W](https://stacks.math.columbia.edu/tag/0F8W)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0GU0](https://stacks.math.columbia.edu/tag/0GU0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace StrictlyPerfect

universe u d

namespace Stacks.Divisors

/-- An ideal sheaf whose support has no points is an effective Cartier divisor: the
affine-local criterion for being one asks for a regular equation only at the points of the
support. -/
theorem isEffectiveCartierDivisor_of_supportSet_eq_empty {X : Scheme.{u}}
    (I : X.IdealSheafData) (h : ∀ x : X, x ∉ I.supportSet) :
    IsEffectiveCartierDivisor I :=
  (isEffectiveCartierDivisor_iff_affineLocal I).2 fun x hx => absurd hx (h x)

end Stacks.Divisors

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- The open subscheme `X ∖ D` of `X`, the complement of the support of the effective Cartier
divisor. -/
abbrev divisorComplement (S : ComplexAndDivisorSituation.{u, d}) : S.X.Opens :=
  S.D.support.compl

/-- A morphism whose image misses the support of `D` is **good for the triple**: the pulled-back
divisor has no points, so it is an effective Cartier divisor by
`Stacks.Divisors.isEffectiveCartierDivisor_of_supportSet_eq_empty` and the pulled-back triple is
a good triple by
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodTriple_of_isEmpty_supportSet`, both for want
of a point at which anything has to be produced. -/
theorem isGoodOver_of_forall_notMem_supportSet {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hh : ∀ y : Y, h.base y ∉ S.D.supportSet) : S.IsGoodOver h := by
  have hempty : ∀ y : Y, y ∉ (S.D.comap h).supportSet := by
    intro y hy
    refine hh y ?_
    rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
      Scheme.IdealSheafData.support_comap] at hy
    exact Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2 hy
  refine ⟨Stacks.Divisors.isEffectiveCartierDivisor_of_supportSet_eq_empty _ hempty, ?_⟩
  refine isGoodTriple_of_isEmpty_supportSet _ ?_
  exact Set.eq_empty_iff_forall_notMem.2 hempty

/-- The inclusion of `X ∖ D` is good for the triple. -/
theorem isGoodOver_divisorComplement_ι (S : ComplexAndDivisorSituation.{u, d}) :
    S.IsGoodOver S.divisorComplement.ι :=
  isGoodOver_of_forall_notMem_supportSet _ fun y =>
    Scheme.IdealSheafData.mem_supportSet_iff_mem_support.not.2 y.2

/-- The restriction of any `b : X' ⟶ X` to `b⁻¹(X ∖ D) ⟶ X` is good for the triple: its image
misses the support of `D`. -/
theorem isGoodOver_preimage_divisorComplement_ι_comp {X' : Scheme.{u}} (b : X' ⟶ S.X) :
    S.IsGoodOver ((b ⁻¹ᵁ S.divisorComplement).ι ≫ b) :=
  isGoodOver_of_forall_notMem_supportSet _ fun y =>
    Scheme.IdealSheafData.mem_supportSet_iff_mem_support.not.2 y.2

/-- The object `Q = Lη_{ℐ'}Lb^*M` is the derived décalage functor of the pulled-back divisor
applied to `Lb^*M`; this names that unfolding, so that the statements of Stacks tag 0GU0, which
spell out the functor, can be read against statements written in terms of `Q`. -/
theorem etaDerivedPullbackObject_eq_derivedEtaData_obj
    (S : ComplexAndDivisorSituation.{u, d}) {X' : Scheme.{u}} (b : X' ⟶ S.X)
    (hb : Stacks.Divisors.IsPullbackDefined b S.D) :
    S.etaDerivedPullbackObject b hb =
      (@Stacks.Divisors.Eta.derivedEtaData X' (S.D.comap b) hb).functor.obj
        (S.derivedPullbackObject b) :=
  rfl

namespace IsGoodBlowup

variable {X' : Scheme.{u}} {b : X' ⟶ S.X}

/-- Clause (1) of Stacks tag 0F9Y: a morphism `b : X' ⟶ X` with properties (1) and (2) of
Stacks tag 0GTY is an isomorphism over the complement `X ∖ D` of the effective Cartier divisor.

The inclusion of `X ∖ D` and the restriction `b⁻¹(X ∖ D) ⟶ X` of `b` are both good for the
triple, because the divisor pulled back along either has no points at all; so the universal
property of `b` identifies `b⁻¹(X ∖ D)` with `X ∖ D` by
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isIso_resLE_of_isGoodOver`. -/
theorem isIso_resLE_divisorComplement (hb : S.IsGoodBlowup b) :
    IsIso (b.resLE S.divisorComplement (b ⁻¹ᵁ S.divisorComplement) le_rfl) :=
  hb.isIso_resLE_of_isGoodOver _ S.isGoodOver_divisorComplement_ι
    (isGoodOver_preimage_divisorComplement_ι_comp b)

/-- Clauses (1), (5) and (9) of Stacks tag 0F9Y, for a representable `M`.  Let `(X, D, M)` be
a triple as in Situation 0F8S and let `b : X' ⟶ X` have properties (1) and (2) of Stacks tag
0GTY.  Suppose `M` is represented by a locally bounded complex of finite locally free
`𝒪_X`-modules.  Then `b` is an isomorphism over `X ∖ D`, the object `Q = Lη_{ℐ'}Lb^*M` is a
perfect object of `D(𝒪_{X'})`, and `Q` too is represented by a locally bounded complex of
finite locally free `𝒪_{X'}`-modules.

Clause (1) is
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isIso_resLE_divisorComplement`,
clause (9) is tag 0GU0 as
`Stacks.BlowUpComplexes.exists_isLocallyBoundedFiniteLocallyFree_etaDerivedPullback`, and clause
(5) follows from clause (9) because a locally bounded complex of finite locally free modules is
perfect.  The complete statement of tag 0F9Y is
`AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase_modification`. -/
theorem isIso_and_isPerfect_and_exists_rep (hb : S.IsGoodBlowup b)
    (hrep : ∃ ℳ : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ,
      Stacks.Chow.IsLocallyBoundedFiniteLocallyFree ℳ ∧
        Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj ℳ ≅ S.M)) :
    IsIso (b.resLE S.divisorComplement (b ⁻¹ᵁ S.divisorComplement) le_rfl) ∧
      RingedSpace.IsPerfect (X := X'.toRingedSpace)
        (S.etaDerivedPullbackObject b hb.isGoodOver.pullbackDefined) ∧
      ∃ 𝒬 : CochainComplex X'.Modules ℤ,
        Stacks.Chow.IsLocallyBoundedFiniteLocallyFree 𝒬 ∧
          Nonempty (DerivedCategory.Q.obj 𝒬 ≅
            S.etaDerivedPullbackObject b hb.isGoodOver.pullbackDefined) := by
  obtain ⟨𝒬, h𝒬, e⟩ :=
    Stacks.BlowUpComplexes.exists_isLocallyBoundedFiniteLocallyFree_etaDerivedPullback
      S b hb.isGoodOver.pullbackDefined hb.isGoodOver.isGoodTriple hrep
  rw [S.etaDerivedPullbackObject_eq_derivedEtaData_obj b hb.isGoodOver.pullbackDefined]
  exact ⟨hb.isIso_resLE_divisorComplement,
    ⟨𝒬, Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree 𝒬 h𝒬, e⟩,
    𝒬, h𝒬, e⟩

end IsGoodBlowup

end AlgebraicGeometry.ComplexAndDivisorSituation

end
