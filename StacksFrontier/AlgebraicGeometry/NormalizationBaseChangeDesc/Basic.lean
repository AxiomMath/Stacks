module

public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeUH.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree

/-!
# The normalization base-change comparison is a relative normalization

Let `k` be a field, `X` a scheme locally of finite type over `k`, and `K/k` an extension of
fields. Write `Y = X_K` for the base change and
`Z = X^ν ×_{Spec k} Spec K` for the base change of the normalization of `X`. Tag 0C3N's
canonical comparison `AlgebraicGeometry.normalizationBaseChangeComparison` is a morphism
`c : Y^ν ⟶ Z`.

The comparison is already known to be integral, and `Z ⟶ Y` is integral as well. Since the
morphism `G_Y ⟶ Y` from the spectra of the residue fields at the generic points of `Y`
factors through `Z`, relative normalization over an intermediate scheme integral over the
base (Tag 035I) identifies `Y^ν`, together with its dominant map from `G_Y` and the
comparison `c`, as *the* relative normalization of `G_Y ⟶ Z` **over `Z`**. In other words `c`
is itself a relative normalization morphism.

This removes `X`, the base change and the comparison from the two assertions of Tag 0C3N that
remain open: both become statements about the single morphism `G_Y ⟶ Z`, namely that the
relative normalization of `Z` in the residue fields at the generic points of `Y` is a
universal homeomorphism over `Z`, respectively an isomorphism.

## Main definitions

* `AlgebraicGeometry.toBaseChangeNormalization` is the morphism from the spectra of the residue
  fields at the generic points of `X_K` into the base change of the normalization of `X`,
  obtained by composing the map to the normalization with the comparison.

## Main results

* `AlgebraicGeometry.toBaseChangeNormalization_comp` characterizes that morphism: composed with
  the base change of the normalization morphism it is the canonical morphism from the
  generic-point residue fields of `X_K`.
* `AlgebraicGeometry.normalizationBaseChangeComparison_eq_normalizationDesc` identifies the
  comparison with the canonical descent morphism of that factorization.
* `AlgebraicGeometry.normalizationBaseChangeComparison_universalProperty`: the normalization of
  `X_K`, with its dominant map from the generic-point residue fields and the comparison, has
  the universal property of the relative normalization of `toBaseChangeNormalization` over the
  base change of the normalization of `X`.
* `AlgebraicGeometry.existsUnique_iso_normalization_toBaseChangeNormalization`: consequently it
  is uniquely isomorphic, compatibly with both maps, to that relative normalization.
* `AlgebraicGeometry.isIso_normalizationBaseChangeComparison_iff`: the comparison is an
  isomorphism if and only if the structural morphism of the relative normalization of
  `toBaseChangeNormalization` is.
* In namespace `AlgebraicGeometry`:
  `universalHomeomorphism_normalizationBaseChangeComparison_iff_fromNormalization`: the
  comparison is a universal homeomorphism if and only if the structural morphism of the relative
  normalization of `toBaseChangeNormalization` is.

## Implementation notes

The two open assertions of Tag 0C3N, "universal homeomorphism" and "separable extension", are
reformulated here rather than proved:

* "universal homeomorphism" is, by
  `universalHomeomorphism_normalizationBaseChangeComparison_iff_fromNormalization`, equivalent
  to `UniversalHomeomorphism (toBaseChangeNormalization X).fromNormalization` for every field
  `k`, every extension `K/k` and every `X` locally of finite type over `k`. The affine case of
  this over a normal base is
  `AlgebraicGeometry.universalHomeomorphism_normalization_tensorProduct_of_normal`; passing to
  the general case needs normality of `X^ν` and a reduction of `Z` to a normal model, which is
  what is not available.
* "separable extension" is, by `isIso_normalizationBaseChangeComparison_iff`, equivalent to
  `IsIso (toBaseChangeNormalization X).fromNormalization` when `K/k` is separable. That in turn
  would follow from normality of `Z`, which needs Tag 0C3M (normality is preserved by separable
  extension of the ground field) and normality of `X^ν`, neither of which is available.

The quasi-compactness and quasi-separatedness facts needed to form the relative normalizations
are `local instance`s in `NormalizationFieldExtension.Basic`, so their instance attribute does
not reach this module; it is reinstated here.

## References

* [Stacks Project, Tag 0C3N](https://stacks.math.columbia.edu/tag/0C3N)
* [Stacks Project, Tag 035I](https://stacks.math.columbia.edu/tag/035I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom]

attribute [local instance] quasiSeparatedFromGenericPointResidueFields'
  quasiCompactFromGenericPointResidueFields_left
  quasiCompactFromGenericPointResidueFields_baseChange

/-- The morphism from the spectra of the residue fields at the generic points of `X_K` into the
base change of the normalization of `X`: the canonical map to the normalization of `X_K`,
followed by the comparison of Tag 0C3N. -/
public noncomputable abbrev toBaseChangeNormalization :
    Scheme.genericPointResidueSpectrum (pullback X.hom (specMapAlgebraMap k K)) ⟶
      pullback (normalizationOverField k X.hom ≫ X.hom) (specMapAlgebraMap k K) :=
  (Scheme.fromGenericPointResidueFields
      (pullback X.hom (specMapAlgebraMap k K))).toNormalization ≫
    normalizationBaseChangeComparison X

/-- Composed with the base change of the normalization morphism, the morphism into the base
change of the normalization is the canonical morphism from the generic-point residue fields of
`X_K`. -/
public theorem toBaseChangeNormalization_comp :
    toBaseChangeNormalization (k := k) (K := K) X ≫ baseChangeNormalization X =
      Scheme.fromGenericPointResidueFields (pullback X.hom (specMapAlgebraMap k K)) := by
  rw [Category.assoc, normalizationBaseChangeComparison_comp_baseChangeNormalization]
  exact Scheme.Hom.toNormalization_fromNormalization
    (Scheme.fromGenericPointResidueFields (pullback X.hom (specMapAlgebraMap k K)))

/-- The comparison of Tag 0C3N is the canonical descent morphism of the factorization of the
morphism from the generic-point residue fields of `X_K` through the base change of the
normalization of `X`. -/
public theorem normalizationBaseChangeComparison_eq_normalizationDesc :
    normalizationBaseChangeComparison X =
      (Scheme.fromGenericPointResidueFields
          (pullback X.hom (specMapAlgebraMap k K))).normalizationDesc
        (toBaseChangeNormalization (k := k) (K := K) X) (baseChangeNormalization X)
        (toBaseChangeNormalization_comp X).symm :=
  Scheme.Hom.normalization.hom_ext
    (Scheme.fromGenericPointResidueFields (pullback X.hom (specMapAlgebraMap k K)))
    (normalizationBaseChangeComparison X) _ (baseChangeNormalization X)
    (((Scheme.fromGenericPointResidueFields
        (pullback X.hom (specMapAlgebraMap k K))).toNormalization_normalizationDesc
      (toBaseChangeNormalization (k := k) (K := K) X) (baseChangeNormalization X)
      (toBaseChangeNormalization_comp X).symm).symm)
    (normalizationBaseChangeComparison_comp_baseChangeNormalization X)
    ((Scheme.fromGenericPointResidueFields
        (pullback X.hom (specMapAlgebraMap k K))).normalizationDesc_comp
      (toBaseChangeNormalization (k := k) (K := K) X) (baseChangeNormalization X)
      (toBaseChangeNormalization_comp X).symm)

/-- **Stacks Project, Tag 035I** applied to Tag 0C3N. The normalization of `X_K`, together with
its canonical map from the generic-point residue fields and the comparison of Tag 0C3N, has the
universal property of the relative normalization of `toBaseChangeNormalization` over the base
change of the normalization of `X`. -/
public theorem normalizationBaseChangeComparison_universalProperty
    (T : Scheme.{u})
    (j : Scheme.genericPointResidueSpectrum (pullback X.hom (specMapAlgebraMap k K)) ⟶ T)
    (q : T ⟶ pullback (normalizationOverField k X.hom ≫ X.hom) (specMapAlgebraMap k K))
    (hq : IsIntegralHom q) (hjq : j ≫ q = toBaseChangeNormalization (k := k) (K := K) X) :
    ∃! l : normalizationSchemeOverField K (pullback.snd X.hom (specMapAlgebraMap k K)) ⟶ T,
      (Scheme.fromGenericPointResidueFields
          (pullback X.hom (specMapAlgebraMap k K))).toNormalization ≫ l = j ∧
        l ≫ q = normalizationBaseChangeComparison X := by
  rw [normalizationBaseChangeComparison_eq_normalizationDesc]
  exact Scheme.Hom.normalizationDesc_universalProperty
    (Scheme.fromGenericPointResidueFields (pullback X.hom (specMapAlgebraMap k K)))
    (toBaseChangeNormalization (k := k) (K := K) X)
    (baseChangeNormalization X) (toBaseChangeNormalization_comp X).symm T j q hq hjq

/-- The morphism `toBaseChangeNormalization` is quasi-compact. -/
local instance quasiCompact_toBaseChangeNormalization :
    QuasiCompact (toBaseChangeNormalization (k := k) (K := K) X) := by
  dsimp only [toBaseChangeNormalization]
  infer_instance

/-- The morphism `toBaseChangeNormalization` is quasi-separated. -/
local instance quasiSeparated_toBaseChangeNormalization :
    QuasiSeparated (toBaseChangeNormalization (k := k) (K := K) X) := by
  dsimp only [toBaseChangeNormalization]
  infer_instance

/-- The normalization of `X_K` is uniquely isomorphic, compatibly with the map from the
generic-point residue fields and with the structural morphism, to the relative normalization of
`toBaseChangeNormalization`. -/
public theorem existsUnique_iso_normalization_toBaseChangeNormalization :
    ∃! e : normalizationSchemeOverField K (pullback.snd X.hom (specMapAlgebraMap k K)) ≅
        (toBaseChangeNormalization (k := k) (K := K) X).normalization,
      (Scheme.fromGenericPointResidueFields
            (pullback X.hom (specMapAlgebraMap k K))).toNormalization ≫ e.hom =
          (toBaseChangeNormalization (k := k) (K := K) X).toNormalization ∧
        e.hom ≫ (toBaseChangeNormalization (k := k) (K := K) X).fromNormalization =
          normalizationBaseChangeComparison X :=
  (Scheme.Hom.normalization_universalProperty_iff_existsUnique_iso
      (toBaseChangeNormalization (k := k) (K := K) X)
      (Scheme.fromGenericPointResidueFields
        (pullback X.hom (specMapAlgebraMap k K))).toNormalization
      (normalizationBaseChangeComparison X) rfl).mp
    fun T j q hq hjq => normalizationBaseChangeComparison_universalProperty X T j q hq hjq

/-- **Stacks Project, Tag 0C3N**, the "separable extension" assertion reformulated. The
comparison is an isomorphism exactly when the relative normalization of the base change of the
normalization of `X` in the generic-point residue fields of `X_K` is trivial. -/
public theorem isIso_normalizationBaseChangeComparison_iff :
    IsIso (normalizationBaseChangeComparison (k := k) (K := K) X) ↔
      IsIso (toBaseChangeNormalization (k := k) (K := K) X).fromNormalization := by
  obtain ⟨e, ⟨-, he⟩, -⟩ :=
    existsUnique_iso_normalization_toBaseChangeNormalization (k := k) (K := K) X
  rw [← he, isIso_comp_left_iff]

/-- **Stacks Project, Tag 0C3N**, the "universal homeomorphism" assertion reformulated. The
comparison is a universal homeomorphism exactly when the structural morphism of the relative
normalization of the base change of the normalization of `X` in the generic-point residue
fields of `X_K` is one. -/
public theorem universalHomeomorphism_normalizationBaseChangeComparison_iff_fromNormalization :
    UniversalHomeomorphism (normalizationBaseChangeComparison (k := k) (K := K) X) ↔
      UniversalHomeomorphism (toBaseChangeNormalization (k := k) (K := K) X).fromNormalization := by
  obtain ⟨e, ⟨-, he⟩, -⟩ :=
    existsUnique_iso_normalization_toBaseChangeNormalization (k := k) (K := K) X
  have hiso := universalHomeomorphism_of_isIso e.hom
  rw [← he]
  exact ⟨universalHomeomorphism_hasTwoOutOfThreeProperty.toHasOfPrecompProperty.of_precomp
    e.hom _ hiso, universalHomeomorphism_hasTwoOutOfThreeProperty.comp_mem e.hom _ hiso⟩

end AlgebraicGeometry

end
