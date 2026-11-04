module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZeroDimensionalFibres
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.Examples.Spaces.DimensionVersusPointSet

/-!
# A zero-dimensional point space on a space of positive dimension

The quotient `𝔸¹_k/ℤ` of the affine line by the integer translations, over a field `k` of
characteristic zero, is a nonempty algebraic space locally of finite type over `k` whose point
space is indiscrete and hence of Krull dimension zero, while the space itself has dimension
one at every point. It therefore satisfies condition (3) of Stacks 0ACA and none of the
conditions (2), (4), (5), so those four conditions are not equivalent without a further
hypothesis such as `T0` on the point space.

## Main results

* `Stacks.Examples.DimensionVersusPointSet.translationQuotientData`: `𝔸¹_k/ℤ` packaged as a
  nonempty algebraic space locally of finite type over `k`.
* `Stacks.Examples.DimensionVersusPointSet.exists_zeroTopologicalDimension_not_discretePoints`:
  there is a nonempty algebraic space locally of finite type over a field whose point space
  has Krull dimension zero but is not discrete, the space not being of dimension zero nor
  locally quasi-finite over the field.

## Implementation notes

That the space is not of dimension zero is immediate from its dimension being one at every
point, the dimension of an algebraic space being the supremum of its dimensions at its points.
The failures of conditions (2) and (5) are then read off from the equivalence of conditions
(2), (4) and (5), which holds with no extra hypothesis.

For a statement with no parameters left, the base field is taken to be `ℚ` in the universe of
the schemes of the site, and the site is one containing its spectrum.

## References

* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
* [Stacks Project, Tag 02Z7](https://stacks.math.columbia.edu/tag/02Z7)
* [Stacks Project, Tag 0DRF](https://stacks.math.columbia.edu/tag/0DRF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Examples.DimensionVersusPointSet

open AffineLineInvolution AffineLineTranslation NonSeparatedGroupSpace

attribute [local instance] AlgebraicGeometry.Space.pointTopology

variable (k : Type u) [Field k] [CharZero k] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of k)))
  [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]

/-- `𝔸¹_k/ℤ` as a nonempty algebraic space locally of finite type over `k`, the standing
situation of Stacks 0ACA. -/
def translationQuotientData : Space.FiniteTypeOverField.{u} where
  k := k
  B := B
  base_mem := hS
  X := Over.mk ((Space.yonedaMkIdTerminal B (Spec (.of k)) hS).from
    (translationQuotient k B hS (contains_affineLine k B hS)))
  isAlgebraicSpace := isAlgebraicSpace_translationQuotient k B hS
  nonempty := ⟨chartPointsMap k B hS
    (Classical.choice (inferInstance : Nonempty (AffineSpace PUnit.{u + 1} (Spec (.of k)))))⟩
  locallyOfFiniteType := isLocallyOfFiniteType_translationQuotient k B hS

/-- Condition (3) of Stacks 0ACA holds for `𝔸¹_k/ℤ`: its point space is indiscrete, hence of
Krull dimension zero. -/
theorem zeroTopologicalDimension_translationQuotientData :
    (translationQuotientData k B hS).ZeroTopologicalDimension :=
  topologicalKrullDim_points_translationQuotient_eq_zero k B hS

/-- Condition (4) of Stacks 0ACA fails for `𝔸¹_k/ℤ`: it has dimension one at every point. -/
theorem not_zeroDimension_translationQuotientData :
    ¬ (translationQuotientData k B hS).ZeroDimension := by
  intro hD
  obtain ⟨x⟩ := (translationQuotientData k B hS).nonempty
  have hx : Space.dimensionAtPoint (translationQuotientData k B hS).B
      (Spec (.of (translationQuotientData k B hS).k))
      (translationQuotientData k B hS).base_mem
      (translationQuotientData k B hS).X.left
      (translationQuotientData k B hS).isAlgebraicSpace x = 1 :=
    dimensionAtPoint_translationQuotient_eq_one k B hS x
  have hle : (1 : WithBot ℕ∞) ≤
      Space.dimension (translationQuotientData k B hS).B
        (Spec (.of (translationQuotientData k B hS).k))
        (translationQuotientData k B hS).base_mem
        (translationQuotientData k B hS).X.left
        (translationQuotientData k B hS).isAlgebraicSpace :=
    le_iSup_of_le x hx.ge
  rw [hD] at hle
  exact absurd hle (by simp)

/-- Condition (2) of Stacks 0ACA fails for `𝔸¹_k/ℤ`, conditions (2) and (4) being
equivalent. -/
theorem not_discretePoints_translationQuotientData :
    ¬ (translationQuotientData k B hS).DiscretePoints := fun hD ↦
  not_zeroDimension_translationQuotientData k B hS
    ((Space.FiniteTypeOverField.discretePoints_iff_zeroDimension _).mp hD)

/-- Condition (5) of Stacks 0ACA fails for `𝔸¹_k/ℤ`, conditions (4) and (5) being
equivalent. -/
theorem not_locallyQuasiFiniteOverField_translationQuotientData :
    ¬ (translationQuotientData k B hS).LocallyQuasiFiniteOverField := fun hD ↦
  not_zeroDimension_translationQuotientData k B hS
    ((Space.FiniteTypeOverField.zeroDimension_iff_locallyQuasiFinite _).mpr hD)

/-- A big fppf site containing the spectrum of the rationals, in the universe of the schemes
of the site. -/
def ratSite : BigFppfSite.{u} :=
  (BigFppfSite.exists_contains (Spec (.of (ULift.{u} ℚ)))).choose

/-- The chosen site contains the spectrum of the rationals. -/
theorem ratSite_contains : (ratSite.{u}).Contains (Spec (.of (ULift.{u} ℚ))) :=
  (BigFppfSite.exists_contains (Spec (.of (ULift.{u} ℚ)))).choose_spec

/-- **Stacks 0ACA.** Conditions (2), (3), (4) and (5) are not equivalent for a general
nonempty algebraic space locally of finite type over a field: the quotient of the affine line
by the integer translations has a point space of Krull dimension zero which is not discrete,
and is neither of dimension zero nor locally quasi-finite over the field. -/
@[stacks 0ACA "the erratum's counterexample: the unrestricted (3) => (2) is false"]
theorem exists_zeroTopologicalDimension_not_discretePoints :
    ∃ D : Space.FiniteTypeOverField.{u}, D.ZeroTopologicalDimension ∧ ¬ D.DiscretePoints ∧
      ¬ D.ZeroDimension ∧ ¬ D.LocallyQuasiFiniteOverField := by
  let : CharZero (ULift.{u} ℚ) := (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ).toRingHom.charZero
  let := BigFppfOver.hasSheafify_type ratSite.{u} (Spec (.of (ULift.{u} ℚ)))
    ratSite_contains.{u}
  exact ⟨translationQuotientData (ULift.{u} ℚ) ratSite.{u} ratSite_contains.{u},
    zeroTopologicalDimension_translationQuotientData _ _ _,
    not_discretePoints_translationQuotientData _ _ _,
    not_zeroDimension_translationQuotientData _ _ _,
    not_locallyQuasiFiniteOverField_translationQuotientData _ _ _⟩

/-- **Stacks 0ACA is false as stated.** The source asserts that conditions (2), (3), (4) and
(5) are equivalent for every algebraic space locally of finite type over a field; they are not.

This is the negation of that assertion, in the source's own vocabulary. The equivalence of
(2), (4) and (5) does hold with no further hypothesis, and the arrow out of (3) holds once
`|X|` is Kolmogorov — in particular for a decent space, by Stacks 03K3. -/
@[stacks 0ACA "the erratum's counterexample: the tag's four-way equivalence, negated"]
theorem not_forall_tfae :
    ¬ ∀ D : Space.FiniteTypeOverField.{u},
        [D.DiscretePoints, D.ZeroTopologicalDimension, D.ZeroDimension,
          D.LocallyQuasiFiniteOverField].TFAE := by
  intro h
  obtain ⟨D, h3, h2, -, -⟩ := exists_zeroTopologicalDimension_not_discretePoints.{u}
  exact h2 (((h D).out 2 1).mp h3)

end Stacks.Examples.DimensionVersusPointSet

end
