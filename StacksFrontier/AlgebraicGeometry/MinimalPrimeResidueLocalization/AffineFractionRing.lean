module

public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.AffineAlgEquiv
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine

/-!
# The normalization over an affine open is the integral closure in the total ring of fractions

For a reduced scheme `X` whose quasi-compact opens have finitely many irreducible components and
an affine open `U`, the sections of the normalization over `ν⁻¹ U` are the integral closure of
`Γ(X, U)` in its total ring of fractions, as an equivalence of `Γ(X, U)`-algebras for the algebra
structure given by `ν.app U` itself.

`AlgebraicGeometry.normalizationSectionsAlgEquivIntegralClosurePiResidueField` already says this
with the product of the residue fields at the generic points lying in `U` as the ambient ring;
for a reduced scheme that product *is* the total ring of fractions
(`AlgebraicGeometry.genericPreimageSectionsAlgEquivFractionRing`), and transporting the integral
closure along the identification is all that happens here.

The point of the `FractionRing` form is that it is the ring in which the ring-theoretic theory of
the normalization of a curve singularity is written — `integralClosure A (FractionRing A)` is the
`A'` of `Stacks.Curves.existsUnique_extend_integralClosure_branchResidues_of_finiteType` and of
`Stacks.DerivationExtension.extend_integralClosure_unique`. The scheme-level identification
`AlgebraicGeometry.preimageNormalizationIsoSpecIntegralClosure` is the same statement one level
up, but it is phrased for an arbitrary ring presenting the affine open and so cannot be composed
with section-level ring theory without carrying the presentation along.

## Main results

* `AlgebraicGeometry.finite_genericPointsInOpen` — the generic points lying in an affine open
  form a finite type.
* `AlgebraicGeometry.normalizationSectionsAlgEquivIntegralClosureFractionRing` — **the sections
  of the normalization over the preimage of an affine open are the integral closure of the
  coordinate ring in its total ring of fractions.**

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **The generic points lying in an affine open form a finite type.** An affine open is
quasi-compact, so it has finitely many irreducible components, and its generic points inject into
them. -/
public theorem finite_genericPointsInOpen {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Finite {η : genericPoints X // η.1 ∈ U} := by
  have : Finite (genericPoints (U : Set X)) :=
    (genericPoints.finite (hX U hU.isCompact)).to_subtype
  exact Finite.of_injective (Scheme.genericPointsInOpenEquiv X U)
    (Scheme.genericPointsInOpenEquiv X U).injective

/-- **The sections of the normalization over the preimage of an affine open are the integral
closure of the coordinate ring in its total ring of fractions.** The `Γ(X, U)`-algebra structure
on the left is the one given by `ν.app U`, so the equivalence carries `ν.app U` to
`algebraMap`. -/
public noncomputable def normalizationSectionsAlgEquivIntegralClosureFractionRing
    {X : Scheme.{u}} [IsReduced X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U)
        Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) :=
      ((Scheme.normalization X hX).app U).hom.toAlgebra
    Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) (FractionRing Γ(X, U)) :=
  letI : Algebra Γ(X, U)
      Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) :=
    ((Scheme.normalization X hX).app U).hom.toAlgebra
  letI (η : {η : genericPoints X // η.1 ∈ U}) : Algebra Γ(X, U) (X.residueField η.1.1) :=
    (X.evaluation U η.1.1 η.2).hom.toAlgebra
  letI : Algebra Γ(X, U) Γ(Scheme.genericPointResidueSpectrum X,
      Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) :=
    (Scheme.fromGenericPointResidueFields X).app U |>.hom.toAlgebra
  letI : Finite {η : genericPoints X // η.1 ∈ U} := finite_genericPointsInOpen hX U hU
  letI eAmbient : (∀ η : {η : genericPoints X // η.1 ∈ U}, X.residueField η.1.1) ≃ₐ[Γ(X, U)]
      FractionRing Γ(X, U) :=
    (genericPreimageSectionsAlgEquivPiResidueField U).symm.trans
      (genericPreimageSectionsAlgEquivFractionRing U hU)
  (normalizationSectionsAlgEquivIntegralClosurePiResidueField hX U hU).trans
    eAmbient.mapIntegralClosure

end AlgebraicGeometry

end
