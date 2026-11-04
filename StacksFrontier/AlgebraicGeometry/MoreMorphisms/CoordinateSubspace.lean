module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# The coordinate affine subspace of affine space

Fix a commutative ring `R` and integers `m, n ≥ 0`, and write affine `(m + n)`-space over `R` as
the spectrum of `R[x₁, …, x_m, y₁, …, y_n]`, the polynomial ring on `Fin m ⊕ Fin n`. Setting the
last `n` coordinates to zero defines a surjection onto `R[x₁, …, x_m]` and hence realizes affine
`m`-space as a closed subscheme of affine `(m + n)`-space. This is the closed immersion
`Z = 𝔸^m_S ⟶ 𝔸^{m+n}_S` from which Stacks Tag 0H1H starts.

## Main definitions

* `Stacks.MoreMorphisms.coordinateProjection` is the ring map setting the last `n` variables
  to zero.
* `Stacks.MoreMorphisms.coordinateEmbedding` is the induced morphism of affine schemes.

## Main results

* `Stacks.MoreMorphisms.coordinateProjection_surjective` says that the coordinate projection is
  surjective, with the inclusion of the first `m` variables as an explicit section.
* `Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion` says that the coordinate affine
  subspace is closed in the ambient affine space.

## Implementation notes

The variables are indexed by `Fin m ⊕ Fin n` rather than by `Fin (m + n)`, so that the first and
the last coordinates are distinguished without an index shift; this is the indexing used in the
source's chart computations. The coordinate projection is built from `MvPolynomial.aeval` and is
therefore an `R`-algebra map, but it is recorded as a bare ring homomorphism because that is what
`AlgebraicGeometry.Spec.map` consumes.

Surjectivity is witnessed by `MvPolynomial.rename Sum.inl`, which is a one-sided inverse: the
composite reindexes along `Sum.elim MvPolynomial.X 0 ∘ Sum.inl = MvPolynomial.X`, which is the
identity substitution.

## References

* [Stacks Project, Tag 0H1H](https://stacks.math.columbia.edu/tag/0H1H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.MoreMorphisms

/-- The map of coordinate rings setting the last `n` variables to zero. -/
public noncomputable def coordinateProjection (R : Type*) [CommRing R] (m n : ℕ) :
    MvPolynomial (Fin m ⊕ Fin n) R →+* MvPolynomial (Fin m) R :=
  (MvPolynomial.aeval (fun i => Sum.elim MvPolynomial.X (fun _ => 0) i)).toRingHom

/-- The coordinate affine `m`-space embedded in affine `(m + n)`-space. -/
public noncomputable def coordinateEmbedding (R : Type*) [CommRing R] (m n : ℕ) :
    Spec (.of (MvPolynomial (Fin m) R)) ⟶
      Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)) :=
  Spec.map (CommRingCat.ofHom (coordinateProjection R m n))

/-- Reindexing along `Sum.inl` is a section of the coordinate projection. -/
public theorem coordinateProjection_rename_inl (R : Type*) [CommRing R] (m n : ℕ)
    (p : MvPolynomial (Fin m) R) :
    coordinateProjection R m n (MvPolynomial.rename Sum.inl p) = p := by
  simpa [coordinateProjection, MvPolynomial.aeval_rename, Function.comp_def] using
    MvPolynomial.aeval_X_left_apply p

/-- The coordinate projection is surjective: every polynomial in the first `m` variables is the
image of its reindexing along `Sum.inl`. -/
public theorem coordinateProjection_surjective (R : Type*) [CommRing R] (m n : ℕ) :
    Function.Surjective (coordinateProjection R m n) :=
  fun p => ⟨MvPolynomial.rename Sum.inl p, coordinateProjection_rename_inl R m n p⟩

/-- The coordinate affine subspace is closed in the ambient affine space. -/
@[stacks 0H1H "coordinate closed immersion"]
public theorem coordinateEmbedding_isClosedImmersion (R : Type*) [CommRing R] (m n : ℕ) :
    IsClosedImmersion (coordinateEmbedding R m n) :=
  IsClosedImmersion.spec_of_surjective _ (coordinateProjection_surjective R m n)

end Stacks.MoreMorphisms

end
