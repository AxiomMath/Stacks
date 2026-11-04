module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Defs

/-!
# Embedding dimension at a point of a scheme

The embedding dimension of a scheme at a point is the dimension, over the residue field at that
point, of the cotangent space of the local ring there. For a scheme locally of finite type over
a field it is equally the dimension of the relative tangent space at the point, and this
relative form is recorded separately.

## Main definitions

* `AlgebraicGeometry.Scheme.embeddingDimension`: the embedding dimension of a scheme at a point,
  as the dimension of the cotangent space of the local ring.
* `AlgebraicGeometry.Scheme.Hom.embeddingDimension`: the embedding dimension of a scheme over a
  field at a point, as the dimension of the relative tangent space.

## Implementation notes

The absolute form uses the residue field of the stalk, so it applies to any point whose
cotangent space is finite-dimensional; in particular the stalks of a locally algebraic scheme
over a field are Noetherian, and at a closed point over an algebraically closed field the
residue field is canonically isomorphic to the base field. The relative form takes the structure
morphism to `Spec k` explicitly, represents local algebraicity by `LocallyOfFiniteType`, and
uses the canonical vector space of dotted tangent arrows; local finite type over a field makes
that dimension finite. Both abbreviations expose the existing API for cotangent spaces,
tangent arrows and `Module.finrank`.

## References

* [Stacks Project, Tag 0C1Q](https://stacks.math.columbia.edu/tag/0C1Q)
* [Stacks Project, Tag 0C2H](https://stacks.math.columbia.edu/tag/0C2H)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The dimension of the cotangent space of the local ring of `X` at `x`, over its
residue field. -/
@[stacks 0C1Q] abbrev Scheme.embeddingDimension (X : Scheme.{u}) (x : X) [FiniteDimensional
    (ResidueField (X.presheaf.stalk x)) (CotangentSpace (X.presheaf.stalk x))] : ℕ :=
  Module.finrank (ResidueField (X.presheaf.stalk x)) (CotangentSpace (X.presheaf.stalk x))

/-- The dimension over `κ(x)` of the tangent space of `X` over `k` at `x`. -/
@[stacks 0C2H]
abbrev Scheme.Hom.embeddingDimension (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) : ℕ :=
  Module.finrank (X.residueField x) (DottedTangentArrow f x)

end AlgebraicGeometry

end
