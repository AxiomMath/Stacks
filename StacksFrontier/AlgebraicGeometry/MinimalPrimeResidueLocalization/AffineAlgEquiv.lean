module

public import StacksFrontier.AlgebraicGeometry.AffineAmbientMinimalPrimes.Basic

/-!
# The affine description of the normalization, as an algebra equivalence

The sections of the normalization over the preimage of an affine open `U` are an integral closure
of `Γ(X, U)`, as an equivalence of `Γ(X, U)`-algebras, the algebra structure on the sections being
the one induced by the structure-sheaf map of the normalization.

## Main results

* `AlgebraicGeometry.normalizationSectionsAlgEquivIntegralClosurePiResidueField`: the sections of
  the normalization over the preimage of an affine open are the integral closure of `Γ(X, U)` in
  the product of the residue fields at the generic points lying in `U`, as a `Γ(X, U)`-algebra.
* `AlgebraicGeometry.normalizationSectionsAlgEquivIntegralClosureMinimalPrimeResidueFields`: the
  same with the product of the residue fields of the minimal primes of `Γ(X, U)` as the ambient
  algebra.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.NormalizationStalkAmbient

universe u

namespace AlgebraicGeometry

/-- The sections of the normalization over the preimage of an affine open `U` are the integral
closure of `Γ(X, U)` in the product of the residue fields at the generic points of `X` lying in
`U`, as an equivalence of `Γ(X, U)`-algebras. -/
public noncomputable def normalizationSectionsAlgEquivIntegralClosurePiResidueField
    {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U)
        Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) :=
      ((Scheme.normalization X hX).app U).hom.toAlgebra
    letI (η : {η : genericPoints X // η.1 ∈ U}) : Algebra Γ(X, U) (X.residueField η.1.1) :=
      (X.evaluation U η.1.1 η.2).hom.toAlgebra
    Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U)
        (∀ η : {η : genericPoints X // η.1 ∈ U}, X.residueField η.1.1) := by
  letI : QuasiCompact (Scheme.fromGenericPointResidueFields X) :=
    Scheme.quasiCompactFromGenericPointResidueFields X hX
  letI : QuasiSeparated (Scheme.fromGenericPointResidueFields X) :=
    Scheme.quasiSeparatedFromGenericPointResidueFields X
  have : Finite (genericPoints (U : Set X)) :=
    (genericPoints.finite (hX U hU.isCompact)).to_subtype
  letI : Finite {η : genericPoints X // η.1 ∈ U} :=
    Finite.of_injective (Scheme.genericPointsInOpenEquiv X U)
      (Scheme.genericPointsInOpenEquiv X U).injective
  letI : Algebra Γ(X, U) Γ(Scheme.genericPointResidueSpectrum X,
      Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) :=
    (Scheme.fromGenericPointResidueFields X).app U |>.hom.toAlgebra
  letI (η : {η : genericPoints X // η.1 ∈ U}) : Algebra Γ(X, U) (X.residueField η.1.1) :=
    (X.evaluation U η.1.1 η.2).hom.toAlgebra
  letI : Algebra Γ(X, U)
      Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) :=
    ((Scheme.normalization X hX).app U).hom.toAlgebra
  have key : (Scheme.normalization X hX).app U ≫
      (Scheme.Hom.normalizationObjIso (Scheme.fromGenericPointResidueFields X) hU).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U)
        Γ(Scheme.genericPointResidueSpectrum X,
          Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U))) := by
    rw [Scheme.Hom.fromNormalization_app (Scheme.fromGenericPointResidueFields X) hU,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine AlgEquiv.ofRingEquiv (f :=
    ((Scheme.Hom.normalizationObjIso (Scheme.fromGenericPointResidueFields X)
        hU).commRingCatIsoToRingEquiv).trans
      (genericPreimageSectionsAlgEquivPiResidueField U).mapIntegralClosure.toRingEquiv)
    fun a ↦ ?_
  have ha := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom key) a
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at ha
  exact (congrArg (genericPreimageSectionsAlgEquivPiResidueField U).mapIntegralClosure ha).trans
    ((genericPreimageSectionsAlgEquivPiResidueField U).mapIntegralClosure.commutes a)

/-- The sections of the normalization over the preimage of an affine open `U` are the integral
closure of `Γ(X, U)` in the product of the residue fields of the minimal primes of `Γ(X, U)`, as
an equivalence of `Γ(X, U)`-algebras. -/
public noncomputable def
    normalizationSectionsAlgEquivIntegralClosureMinimalPrimeResidueFields
    {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U)
        Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) :=
      ((Scheme.normalization X hX).app U).hom.toAlgebra
    letI : Algebra Γ(X, U) (minimalPrimeResidueFieldProduct Γ(X, U)) :=
      (minimalPrimeResidueFieldProductHom Γ(X, U)).toAlgebra
    Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) (minimalPrimeResidueFieldProduct Γ(X, U)) :=
  letI : Algebra Γ(X, U)
      Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) :=
    ((Scheme.normalization X hX).app U).hom.toAlgebra
  letI (η : {η : genericPoints X // η.1 ∈ U}) : Algebra Γ(X, U) (X.residueField η.1.1) :=
    (X.evaluation U η.1.1 η.2).hom.toAlgebra
  letI : Algebra Γ(X, U) (minimalPrimeResidueFieldProduct Γ(X, U)) :=
    (minimalPrimeResidueFieldProductHom Γ(X, U)).toAlgebra
  (normalizationSectionsAlgEquivIntegralClosurePiResidueField hX U hU).trans
    hU.genericPointResidueFieldsAlgEquivMinimalPrimeResidueFieldProduct.mapIntegralClosure

end AlgebraicGeometry

end
