module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine

/-!
# The normalization over an affine open, without assuming reducedness

Over an affine open `U` of a scheme `X` whose quasi-compact opens have finitely many
irreducible components, the normalization of `X` is the spectrum of the integral closure of
`Γ(X, U)` in the product of the residue fields of the generic points of `X` lying in `U`.

The existing affine description `preimageNormalizationIsoSpecIntegralClosure` names the total
ring of fractions of `Γ(X, U)` as the ambient algebra, and that identification needs `X` to be
reduced: the product of the residue fields at the generic points is the total ring of fractions
only then.  Naming the product itself as the ambient algebra removes the hypothesis, which is
what [Stacks, Tag 0C3B] parts (2) and (3) need, since they do not assume reducedness.

## Main results

* `genericPreimageSectionsAlgEquivPiResidueField`: the sections of the generic-point residue
  spectrum over the preimage of an affine open are the product of the residue fields at the
  generic points lying in that open, as an algebra over the ring of sections of the open.
* `normalizationSectionsRingEquivIntegralClosurePiResidueField`: consequently the sections of
  the normalization over the preimage of an affine open are the integral closure of the ring of
  sections of that open in that product.

## Implementation notes

The algebra structures are the ones induced by the structure-sheaf maps, so the first
equivalence is the ring equivalence `genericPreimageSectionsRingEquiv` together with its
compatibility lemma `genericPreimageSectionsRingEquiv_comp_app`; neither mentions reducedness.
The second is that equivalence transported through Mathlib's `normalizationObjIso`, which
describes the relative normalization over an affine open for any quasi-compact,
quasi-separated morphism.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The sections of the generic-point residue spectrum over the preimage of an affine open are
the product of the residue fields at the generic points lying in that open, as an algebra over
the ring of sections of the open. -/
public noncomputable def genericPreimageSectionsAlgEquivPiResidueField
    {X : Scheme.{u}} (U : X.Opens)
    [Finite {η : genericPoints X // η.1 ∈ U}] :
    letI := (Scheme.fromGenericPointResidueFields X).app U |>.hom.toAlgebra
    letI (η : {η : genericPoints X // η.1 ∈ U}) : Algebra Γ(X, U) (X.residueField η.1.1) :=
      (X.evaluation U η.1.1 η.2).hom.toAlgebra
    Γ(Scheme.genericPointResidueSpectrum X,
      Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
        (∀ η : {η : genericPoints X // η.1 ∈ U}, X.residueField η.1.1) :=
  letI : Algebra Γ(X, U) Γ(Scheme.genericPointResidueSpectrum X,
      Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) :=
    (Scheme.fromGenericPointResidueFields X).app U |>.hom.toAlgebra
  letI (η : {η : genericPoints X // η.1 ∈ U}) : Algebra Γ(X, U) (X.residueField η.1.1) :=
    (X.evaluation U η.1.1 η.2).hom.toAlgebra
  AlgEquiv.ofRingEquiv (f := genericPreimageSectionsRingEquiv X U) (fun r => by
    funext η
    exact congrArg (fun k : Γ(X, U) ⟶ X.residueField η.1.1 => k r)
      (genericPreimageSectionsRingEquiv_comp_app X U η))

/-- The sections of the normalization over the preimage of an affine open are the integral
closure of the ring of sections of that open in the product of the residue fields at the generic
points lying in it.  No reducedness hypothesis is needed. -/
public noncomputable def normalizationSectionsRingEquivIntegralClosurePiResidueField
    {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI (η : {η : genericPoints X // η.1 ∈ U}) : Algebra Γ(X, U) (X.residueField η.1.1) :=
      (X.evaluation U η.1.1 η.2).hom.toAlgebra
    Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) ≃+*
      integralClosure Γ(X, U)
        (∀ η : {η : genericPoints X // η.1 ∈ U}, X.residueField η.1.1) := by
  letI : QuasiCompact (Scheme.fromGenericPointResidueFields X) :=
    Scheme.quasiCompactFromGenericPointResidueFields X hX
  letI : QuasiSeparated (Scheme.fromGenericPointResidueFields X) :=
    Scheme.quasiSeparatedFromGenericPointResidueFields X
  haveI : Finite (genericPoints (U : Set X)) :=
    (genericPoints.finite (hX U hU.isCompact)).to_subtype
  letI : Finite {η : genericPoints X // η.1 ∈ U} :=
    Finite.of_injective (Scheme.genericPointsInOpenEquiv X U)
      (Scheme.genericPointsInOpenEquiv X U).injective
  letI : Algebra Γ(X, U) Γ(Scheme.genericPointResidueSpectrum X,
      Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) :=
    (Scheme.fromGenericPointResidueFields X).app U |>.hom.toAlgebra
  letI (η : {η : genericPoints X // η.1 ∈ U}) : Algebra Γ(X, U) (X.residueField η.1.1) :=
    (X.evaluation U η.1.1 η.2).hom.toAlgebra
  exact ((Scheme.Hom.normalizationObjIso (Scheme.fromGenericPointResidueFields X)
      hU).commRingCatIsoToRingEquiv).trans
    (genericPreimageSectionsAlgEquivPiResidueField U).mapIntegralClosure.toRingEquiv

end AlgebraicGeometry

end
