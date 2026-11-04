module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPointsNormal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeInitial

/-!
# The weak normalization of a scheme, and weakly normal schemes

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components, so
that its normalization `AlgebraicGeometry.Scheme.normalization X hX` is defined. The
normalization morphism is quasi-compact, quasi-separated and dominant, hence has a relative
weak normalization: an initial factorization through a universal homeomorphism onto `X`. The
intermediate scheme of that factorization is the *weak normalization* of `X`, and `X` is
*weakly normal* when the resulting morphism to `X` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Scheme.weakNormalizationFactorization`: the factorization of the
  normalization morphism of `X` through its weak normalization.
* `AlgebraicGeometry.Scheme.weakNormalizationScheme`: the intermediate scheme.
* `AlgebraicGeometry.Scheme.weakNormalizationFromNormalization` and
  `AlgebraicGeometry.Scheme.weakNormalization`: its two maps.
* `AlgebraicGeometry.Scheme.IsWeaklyNormal`: weak normality of a scheme.

## Main results

* `AlgebraicGeometry.Scheme.normalization_isDominant`: the normalization morphism is dominant.

## Implementation notes

The factorization carries both maps and their compatibility with the normalization morphism; the
projection `weakNormalization` makes the isomorphism condition defining weak normality a direct
statement.

Dominance of the normalization morphism is obtained from dominance of the canonical morphism
`AlgebraicGeometry.Scheme.fromGenericPointResidueFields X`, which factors as its map to the
normalization followed by the normalization morphism.

The finiteness hypothesis on quasi-compact opens is an explicit argument rather than a
typeclass, because the normalization — and hence the weak normalization — is constructed from
it. Both the factorization and the weak normality predicate are abbreviations, so that clients
can use the underlying data and the isomorphism condition directly.

## References

* [Stacks Project, Tag 0H3R](https://stacks.math.columbia.edu/tag/0H3R)
* [Stacks Project, Tag 0H3S](https://stacks.math.columbia.edu/tag/0H3S)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The normalization morphism of a scheme is dominant: it is the second leg of the
canonical morphism from the generic-point residue fields, which is dominant. -/
public theorem normalization_isDominant (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsDominant (normalization X hX) := by
  let := quasiCompactFromGenericPointResidueFields X hX
  let := quasiSeparatedFromGenericPointResidueFields X
  let f := fromGenericPointResidueFields X
  have : IsDominant f := inferInstance
  have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  exact IsDominant.of_comp f.toNormalization f.fromNormalization

/-- The weak normalization of `X` in its normalization, as a factorization. -/
@[stacks 0H3R]
public noncomputable abbrev weakNormalizationFactorization (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    UniversalHomeomorphismFactorization (normalization X hX) :=
  letI := quasiCompactFromGenericPointResidueFields X hX
  letI := quasiSeparatedFromGenericPointResidueFields X
  letI : IsDominant (normalization X hX) := normalization_isDominant X hX
  _root_.AlgebraicGeometry.weakNormalizationFactorization (normalization X hX)

/-- The underlying scheme of the weak normalization. -/
public noncomputable abbrev weakNormalizationScheme (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Scheme.{u} :=
  (weakNormalizationFactorization X hX).middle

/-- The canonical morphism from the normalization to the weak normalization. -/
public noncomputable abbrev weakNormalizationFromNormalization (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    normalizationScheme X hX ⟶ weakNormalizationScheme X hX :=
  (weakNormalizationFactorization X hX).toMiddle

/-- The weak normalization morphism. -/
public noncomputable abbrev weakNormalization (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    weakNormalizationScheme X hX ⟶ X :=
  (weakNormalizationFactorization X hX).toBase

/-- A scheme is weakly normal if its weak normalization morphism is an isomorphism. -/
@[stacks 0H3S]
public abbrev IsWeaklyNormal (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) : Prop :=
  IsIso (weakNormalization X hX)

end AlgebraicGeometry.Scheme

end
