module

public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.RingTheory.Derivation.IntegralClosureUnique

/-!
# A Leibniz map on the stalk of the normalization is determined on the stalk of the base

Let `X` be a reduced scheme whose quasi-compact opens have finitely many irreducible components,
let `ν : X^ν ⟶ X` be its normalization and let `x` be a point of `X`. Two additive maps of
`(ν_* 𝒪_{X^ν})_x` obeying the Leibniz rule and agreeing on the image of `𝒪_{X, x}` are equal.

By Tag 0C3B(2), in the form
`Stacks.AlgebraicGeometry.NormalizationQuotient.normalizationStalkAlgEquivIntegralClosureSelf`,
that stalk is the integral closure of `𝒪_{X, x}` in its total ring of fractions, so this is
`Stacks.DerivationExtension.eq_of_leibniz_of_algebraMap` transported along the identification.

The reason for wanting it in the Leibniz-additive-map form rather than for bundled derivations is
that it is used to compare the *germs* of two candidate vector fields on `X^ν` built from data on
two different affine opens of `X`: the comparison has to happen where the two affine opens
overlap, where neither coordinate ring surjects onto the other, and the stalk is the first place
at which both become localizations of a common ring. No linearity over a base field is involved,
and none is assumed.

## Main results

* `Stacks.AlgebraicGeometry.NormalizationQuotient.eq_of_leibniz_normalizationPushforwardStalk` —
  **two Leibniz additive maps on the stalk of `ν_* 𝒪_{X^ν}` agreeing on the image of `𝒪_{X, x}`
  are equal.**

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotient

open Stacks.NormalizationStalkAmbient

/-- **Two Leibniz additive maps on the stalk of the pushforward of the structure sheaf of the
normalization which agree on the image of `𝒪_{X, x}` are equal.** That stalk is the integral
closure of `𝒪_{X, x}` in its total ring of fractions, and every element of an integral closure
in a localization is a fraction of elements of the base, so the Leibniz rule propagates the
agreement from the base to the whole stalk. -/
public theorem eq_of_leibniz_normalizationPushforwardStalk (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    ∀ f g : normalizationPushforwardStalk X hX x →+ normalizationPushforwardStalk X hX x,
      (∀ z w, f (z * w) = z * f w + w * f z) →
        (∀ z w, g (z * w) = z * g w + w * g z) →
          (∀ a : X.presheaf.stalk x,
              f (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) a)
                = g (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) a)) →
            f = g := by
  let : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  intro f g hf hg h
  let e := normalizationStalkAlgEquivIntegralClosureSelf X hX x
  -- conjugate both maps into the integral closure
  let conj : (normalizationPushforwardStalk X hX x →+ normalizationPushforwardStalk X hX x) →
      (↥(integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) →+
      ↥(integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))) :=
    fun k => AddMonoidHom.mk' (fun c => e (k (e.symm c))) (by intro a b; simp)
  have hleib : ∀ k : normalizationPushforwardStalk X hX x →+ normalizationPushforwardStalk X hX x,
      (∀ z w, k (z * w) = z * k w + w * k z) →
        ∀ c d, conj k (c * d) = c * conj k d + d * conj k c := by
    intro k hk c d
    change e (k (e.symm (c * d))) = c * e (k (e.symm d)) + d * e (k (e.symm c))
    rw [map_mul, hk]
    simp
  have hFG : conj f = conj g := by
    refine Stacks.DerivationExtension.eq_of_leibniz_of_algebraMap _ _ (hleib f hf) (hleib g hg) ?_
    intro a
    change e (f (e.symm (algebraMap _ _ a))) = e (g (e.symm (algebraMap _ _ a)))
    rw [e.symm.commutes a, h a]
  refine AddMonoidHom.ext fun z => ?_
  have hz := congrArg (fun H => H (e z)) hFG
  simp only [conj, AddMonoidHom.mk'_apply, AlgEquiv.symm_apply_apply] at hz
  exact e.injective hz

end Stacks.AlgebraicGeometry.NormalizationQuotient

end
