module

public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.StalkVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Normalization
public import StacksFrontier.RingTheory.AdicCompletion.QuotientFiniteLength

/-!
# Completing the normalization quotient of a local ring of a curve

Let `X` be a reduced scheme of dimension one, let `ν : X^ν ⟶ X` be its normalization and let
`x ∈ X`.  Writing `A = 𝒪_{X,x}` and `A' = (ν_* 𝒪_{X^ν})_x`, the `A`-module `A'/A` is unchanged
by `m_A`-adic completion: it is canonically the quotient of the completed normalization stalk by
the completed local ring, and the canonical map is the unique one compatible with the completion
maps.  This is the part of [Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R) that
lets the delta invariant be computed after completion.

The mechanism is Tag 0BNG, applied here through
`AdicCompletion.existsUnique_linearEquiv_quotientRange_of_isFiniteLength`: the sequence
`0 → A → A' → A'/A → 0` is short exact, and `A'/A` has finite length, hence is annihilated by a
power of `m_A`, which is exactly the hypothesis under which adic completion preserves exactness
and leaves the third term alone.  Finite length of `A'/A` is Tag 0C3S(4) transported along the
identification of `A'` with the integral closure of `A` in its total ring of fractions, Tag
0C3B(2); when the local ring happens to be zero-dimensional that identification collapses, the
local ring being a field, and `A'/A` vanishes.

## Main results

* `isFiniteLength_quotient_range_normalizationPushforwardStalk`: the normalization stalk modulo
  the local ring has finite length.
* `existsUnique_linearEquiv_quotient_adicCompletion_normalizationPushforwardStalk` is the unique
  `A`-linear isomorphism `A'/A ≅ A'^∧/A^∧` commuting with the completion maps.

## Implementation notes

The closedness of the point, which the source assumes, is not used: the dimension hypothesis
alone bounds `ringKrullDim A` by one, and both the one-dimensional and the zero-dimensional case
give a finite-length quotient.  The finiteness-of-irreducible-components input of the
normalization construction is taken as a hypothesis separate from the Nagata hypothesis, as
elsewhere in this directory, since only the latter is needed for the local rings to be Nagata.

Both quotients are quotients by the range of a canonical map, not by an abstractly chosen
submodule: `LinearMap.range (Algebra.linearMap A A')` downstairs and the range of its
completion upstairs.  The conclusion is an `∃!`, pinning the isomorphism by its compatibility
with `AdicCompletion.of`, rather than a bare existence statement.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 0BNG](https://stacks.math.columbia.edu/tag/0BNG) for the completion of a
  short exact sequence whose third term is power-torsion
* [Stacks Project, Tag 0C3S](https://stacks.math.columbia.edu/tag/0C3S) for the finite length of
  the integral closure modulo the ring
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotient

open Stacks.NormalizationStalkAmbient

attribute [local instance] normalizationPushforwardStalkAlgebra

/-- The normalization stalk modulo the local ring has finite length: in dimension one this is
Tag 0C3S(4) read through the identification of the normalization stalk with the integral closure
of the local ring in its total ring of fractions, and in dimension zero the local ring is a
field, so the quotient vanishes. -/
public theorem isFiniteLength_quotient_range_normalizationPushforwardStalk (X : Scheme.{u})
    [IsReduced X] (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X = 1)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    IsFiniteLength (X.presheaf.stalk x)
      (normalizationPushforwardStalk X hX x ⧸
        LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
          (normalizationPushforwardStalk X hX x))) := by
  let : IsReduced (X.presheaf.stalk x) := AlgebraicGeometry.isReduced_stalk_of_isReduced X x
  have hA : IsNagataRing (X.presheaf.stalk x) := stalk_isNagataRing X hNagata x
  let : IsNoetherianRing (X.presheaf.stalk x) := hA.1
  have hdimLE : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
    (ringKrullDim_stalk_le_topologicalKrullDim X x).trans hdim.le
  have hcases : ringKrullDim (X.presheaf.stalk x) = 0 ∨
      ringKrullDim (X.presheaf.stalk x) = 1 := by
    cases hdimA : ringKrullDim (X.presheaf.stalk x) using WithBot.recBotCoe with
    | bot =>
        have := ringKrullDim_nonneg_of_nontrivial (R := X.presheaf.stalk x)
        simp [hdimA] at this
    | coe d =>
        have hdle : d ≤ (1 : ℕ∞) := WithBot.coe_le_coe.mp (by simpa [hdimA] using hdimLE)
        rcases Order.le_one_iff.mp hdle with hd | hd
        · exact Or.inl (by simpa [hdimA] using hd)
        · exact Or.inr (by simpa [hdimA] using hd)
  rcases hcases with hdim0 | hdim1
  · -- A zero-dimensional reduced local ring is a field, hence integrally closed, so the stalk
    -- map is surjective and the quotient is trivial.
    let : Ring.KrullDimLE 0 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr (by simp [hdim0])
    let : Field (X.presheaf.stalk x) :=
      (Ring.KrullDimLE.isField_of_isReduced (R := X.presheaf.stalk x)).toField
    have : Subsingleton (normalizationPushforwardStalk X hX x ⧸
        LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
          (normalizationPushforwardStalk X hX x))) :=
      Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr
        (normalizationStalkMap_surjective_of_isIntegrallyClosed X hX x
          (isIntegrallyClosed_of_isRegularLocalRing (X.presheaf.stalk x))))
    exact IsFiniteLength.of_subsingleton
  · have hFL := isFiniteLength_integralClosure_quotient (A := X.presheaf.stalk x) hA hdim1
    have hcomp :
        ((normalizationStalkAlgEquivIntegralClosureSelf X hX x).toLinearEquiv :
            normalizationPushforwardStalk X hX x →ₗ[X.presheaf.stalk x]
              integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) ∘ₗ
          Algebra.linearMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) =
          Algebra.linearMap (X.presheaf.stalk x)
            (integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) :=
      LinearMap.ext fun a =>
        (normalizationStalkAlgEquivIntegralClosureSelf X hX x).commutes a
    have hmap : Submodule.map
        ((normalizationStalkAlgEquivIntegralClosureSelf X hX x).toLinearEquiv :
          normalizationPushforwardStalk X hX x →ₗ[X.presheaf.stalk x]
            integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))
        (LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
          (normalizationPushforwardStalk X hX x))) =
        LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
          (integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))) := by
      rw [← LinearMap.range_comp, hcomp]
    exact IsFiniteLength.of_injective hFL
      (Submodule.Quotient.equiv _ _
        (normalizationStalkAlgEquivIntegralClosureSelf X hX x).toLinearEquiv hmap).injective

/-- **Stacks Project, Tag 0C1R.** Let `X` be a reduced scheme of dimension one with
normalization `ν`, let `x ∈ X`, write `A = 𝒪_{X,x}` and `A' = (ν_* 𝒪_{X^ν})_x`, and complete at
the maximal ideal of `A`.  There is exactly one `A`-linear isomorphism `A'/A ≅ A'^∧/A^∧`
compatible with the canonical maps to the completions.

The closedness of the point assumed in the source is not used; the dimension hypothesis is. -/
@[stacks 0C1R "quotient_completion"]
public theorem existsUnique_linearEquiv_quotient_adicCompletion_normalizationPushforwardStalk
    (X : Scheme.{u}) [IsReduced X] (hNagata : IsNagataScheme X)
    (hdim : topologicalKrullDim X = 1)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    ∃! e :
        (normalizationPushforwardStalk X hX x ⧸
            LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
              (normalizationPushforwardStalk X hX x))) ≃ₗ[X.presheaf.stalk x]
          (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (normalizationPushforwardStalk X hX x) ⧸
            LinearMap.range (AdicCompletion.map
              (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (Algebra.linearMap (X.presheaf.stalk x)
                (normalizationPushforwardStalk X hX x)))),
      ∀ a : normalizationPushforwardStalk X hX x,
        e (Submodule.mkQ _ a) = Submodule.mkQ _
          (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (normalizationPushforwardStalk X hX x) a) :=
  AdicCompletion.existsUnique_linearEquiv_quotientRange_of_isFiniteLength
    (Algebra.linearMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x))
    (normalizationPushforwardStalk_map_injective X hX x)
    (isFiniteLength_quotient_range_normalizationPushforwardStalk X hNagata hdim hX x)

end Stacks.AlgebraicGeometry.NormalizationQuotient

end
