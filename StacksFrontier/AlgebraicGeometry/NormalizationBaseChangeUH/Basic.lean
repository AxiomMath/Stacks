module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksFrontier.AlgebraicGeometry.NormalizationFieldExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral

/-!
# The normalization base-change comparison is integral

Let `k` be a field, `X` a scheme locally of finite type over `k`, and `K/k` an extension of
fields. `AlgebraicGeometry.normalizationBaseChangeComparison` is the canonical morphism from the
normalization of `X_K` to the base change `X^ν ×_{Spec k} Spec K` of the normalization of `X`.
Stacks Tag 0C3N asserts that this morphism is a universal homeomorphism, and an isomorphism when
`K/k` is separable.

This file supplies the first of the three conditions in the characterization of a universal
homeomorphism as an integral, universally injective, surjective morphism (Tag 04DF): the
comparison is integral. The argument is formal. The comparison composed with the base change of
the normalization morphism is the normalization morphism of `X_K` (Tag 0C3N, "compatibility with
normalization morphisms", already proved), which is integral because every relative normalization
morphism is; and the base change of the normalization morphism is itself integral, being a
pullback projection of the normalization morphism. Integral morphisms cancel on the right against
separated ones, so the comparison is integral.

With integrality in hand the universal-homeomorphism assertion reduces to two conditions instead
of three, and surjectivity in turn reduces to dominance, since an integral morphism is
universally closed and therefore has closed range. Both reductions are recorded below, together
with the identification of the composite of the comparison with the morphism from the
generic-point residue fields, which is where a proof of dominance would start.

## Main results

* `AlgebraicGeometry.baseChangeNormalization_eq`: the base change of the normalization morphism
  is, up to the canonical isomorphism of iterated fibre products, the pullback projection of the
  normalization morphism along `X_K ⟶ X`. This is what makes it integral.
* `AlgebraicGeometry.isIntegralHom_normalizationBaseChangeComparison`: the comparison of
  Tag 0C3N is integral.
* `AlgebraicGeometry.universalHomeomorphism_normalizationBaseChangeComparison_iff`: the comparison
  is a universal homeomorphism if and only if it is universally injective and dominant.
* `AlgebraicGeometry.toNormalization_normalizationBaseChangeComparison`: the composite of the
  normalization morphism of the generic-point residue fields of `X_K` with the comparison, as a
  morphism into the fibre product.

## Implementation notes

No `@[stacks 0C3N]` attribute is attached in this file. The tag's two unformalized assertions
are labelled "universal homeomorphism" and "separable extension"; integrality is one of three
conditions for the first and nothing at all for the second, so neither assertion is proved here
and the tag is not attached.

`baseChangeNormalization` is defined as the action of the base-change functor on the over
category, which is a `pullback.lift`. Rather than unfold that, the identification below is proved
by `pullback.hom_ext` from the two known projection formulas, so it does not depend on
how the base-change functor computes.

## References

* [Stacks Project, Tag 0C3N](https://stacks.math.columbia.edu/tag/0C3N)
* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom]

/- The quasi-compactness and quasi-separatedness facts needed to form the relative
normalizations are `local instance`s in `NormalizationFieldExtension.Basic`, so their instance
attribute does not reach this module; it is reinstated here. -/
attribute [local instance] quasiSeparatedFromGenericPointResidueFields'
  quasiCompactFromGenericPointResidueFields_left
  quasiCompactFromGenericPointResidueFields_baseChange

/-- The base change of the normalization morphism along `K/k` is the pullback projection of the
normalization morphism along the projection `X_K ⟶ X`, transported along the canonical
isomorphism `X^ν ×_X (X ×_{Spec k} Spec K) ≅ X^ν ×_{Spec k} Spec K`. -/
public theorem baseChangeNormalization_eq :
    baseChangeNormalization (k := k) (K := K) X =
      (pullbackRightPullbackFstIso X.hom (specMapAlgebraMap k K)
          (normalizationOverField k X.hom)).inv ≫
        pullback.snd (normalizationOverField k X.hom)
          (pullback.fst X.hom (specMapAlgebraMap k K)) := by
  refine pullback.hom_ext ?_ ?_
  · rw [baseChangeNormalization_fst, Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]
  · rw [baseChangeNormalization_snd, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]

/-- The base change of the normalization morphism is integral, being a pullback projection of the
normalization morphism. -/
public instance isIntegralHom_baseChangeNormalization :
    IsIntegralHom (baseChangeNormalization (k := k) (K := K) X) := by
  rw [baseChangeNormalization_eq]
  infer_instance

/-- **Stacks Project, Tag 0C3N**, first of the three conditions of Tag 04DF. The canonical
comparison from the normalization of `X_K` to the base change of the normalization of `X` is
integral: composed with the base change of the normalization morphism it is the normalization
morphism of `X_K`, which is integral, and integral morphisms cancel on the right against
separated ones. -/
public instance isIntegralHom_normalizationBaseChangeComparison :
    IsIntegralHom (normalizationBaseChangeComparison (k := k) (K := K) X) :=
  have : IsIntegralHom (normalizationBaseChangeComparison (k := k) (K := K) X ≫
      baseChangeNormalization X) := by
    rw [normalizationBaseChangeComparison_comp_baseChangeNormalization]
    infer_instance
  .of_comp _ (baseChangeNormalization X)

/-- Surjectivity of the comparison is equivalent to its dominance: the comparison is integral,
hence universally closed, hence has closed range. -/
public theorem surjective_normalizationBaseChangeComparison_iff :
    Surjective (normalizationBaseChangeComparison (k := k) (K := K) X) ↔
      IsDominant (normalizationBaseChangeComparison (k := k) (K := K) X) := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ surjective_of_isDominant_of_isClosed_range _ ?_⟩
  have h : IsClosedMap (normalizationBaseChangeComparison (k := k) (K := K) X).base :=
    UniversallyClosed.universally_isClosedMap _ _ _ IsPullback.of_id_snd
  exact Set.image_univ ▸ h _ isClosed_univ

/-- **Stacks Project, Tag 0C3N**, the "universal homeomorphism" assertion reduced by Tag 04DF.
Integrality being established, the comparison is a universal homeomorphism exactly when it is
universally injective and dominant. -/
public theorem universalHomeomorphism_normalizationBaseChangeComparison_iff :
    UniversalHomeomorphism (normalizationBaseChangeComparison (k := k) (K := K) X) ↔
      UniversallyInjective (normalizationBaseChangeComparison (k := k) (K := K) X) ∧
        IsDominant (normalizationBaseChangeComparison (k := k) (K := K) X) := by
  rw [universalHomeomorphism_iff_integral_universallyInjective_surjective,
    and_iff_right (isIntegralHom_normalizationBaseChangeComparison X),
    surjective_normalizationBaseChangeComparison_iff]

/-- The composite of the normalization morphism of the generic-point residue fields of `X_K` with
the comparison, computed on the two projections of the fibre product. The morphism from the
generic-point residue fields is dominant, so dominance of the comparison is equivalent to
dominance of this composite. -/
public theorem toNormalization_normalizationBaseChangeComparison :
    (Scheme.fromGenericPointResidueFields
          (pullback X.hom (specMapAlgebraMap k K))).toNormalization ≫
        normalizationBaseChangeComparison (k := k) (K := K) X =
      pullback.lift
        (genericPointResidueSpectrumBaseChangeMap X ≫
          (Scheme.fromGenericPointResidueFields X.left).toNormalization)
        (Scheme.fromGenericPointResidueFields (pullback X.hom (specMapAlgebraMap k K)) ≫
          pullback.snd X.hom (specMapAlgebraMap k K))
        (by
          dsimp only [Over.mk_hom]
          simp only [Category.assoc, Scheme.Hom.toNormalization_fromNormalization_assoc]
          rw [← Category.assoc, genericPointResidueSpectrumBaseChangeMap_comp,
            Category.assoc, pullback.condition]) := by
  have hfst : normalizationBaseChangeComparison X ≫
      pullback.fst (normalizationOverField k X.hom ≫ X.hom) (specMapAlgebraMap k K) =
      normalizationBaseChangeMap X := pullback.lift_fst _ _ _
  have hsnd : normalizationBaseChangeComparison X ≫
      pullback.snd (normalizationOverField k X.hom ≫ X.hom) (specMapAlgebraMap k K) =
      normalizationOverField K (pullback.snd X.hom (specMapAlgebraMap k K)) ≫
        pullback.snd X.hom (specMapAlgebraMap k K) :=
    normalizationBaseChangeComparison_comp_snd X
  refine pullback.hom_ext ?_ ?_
  · dsimp only [Over.mk_hom]
    rw [Category.assoc, pullback.lift_fst, hfst]
    exact Scheme.Hom.toNormalization_normalizationMap _ _ _ _ _
  · dsimp only [Over.mk_hom]
    rw [Category.assoc, pullback.lift_snd, hsnd,
      Scheme.Hom.toNormalization_fromNormalization_assoc]

/-- Dominance of the comparison is equivalent to dominance of its composite with the normalization
morphism of the generic-point residue fields of `X_K`, which is dominant. -/
public theorem isDominant_normalizationBaseChangeComparison_iff :
    IsDominant (normalizationBaseChangeComparison (k := k) (K := K) X) ↔
      IsDominant ((Scheme.fromGenericPointResidueFields
          (pullback X.hom (specMapAlgebraMap k K))).toNormalization ≫
        normalizationBaseChangeComparison (k := k) (K := K) X) :=
  (IsDominant.comp_iff _ _).symm

end AlgebraicGeometry

end
