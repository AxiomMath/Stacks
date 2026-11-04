module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RelativeSpecBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative spectrum over an affine base

Let `S` be an affine scheme and `A` a quasi-coherent sheaf of commutative `𝒪_S`-algebras. Then
the relative spectrum `Spec_S(A)` is affine, and it is the spectrum of the ring `Γ(S, A)` of
global sections of the algebra:

`Spec_S(A) ≅ Spec Γ(S, A)`.

This is [Stacks, Tag 01LT] at the level of schemes.
`Stacks.RelativeSpec.relativeSpecFunctor_representableBy` carries the tag in its
functor-of-points form — the functor of relative-spectrum pairs is represented by
`Spec Γ(S, A)` — which identifies `Spec Γ(S, A)` with *a* representing object; what is produced
here is the isomorphism with the glued relative spectrum
`Stacks.AffineAlgebraEquivalence.relativeSpec` that the rest of the library is written against.

The proof does not go through representability at all. The structure morphism of a relative
spectrum is affine ([Stacks, Tag 01LX] part (1)), so over an affine base the relative spectrum
is affine; and its ring of global functions is `Γ(S, A)` by [Stacks, Tag 01LX] part (3),
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`, evaluated at `⊤`. An affine scheme is
the spectrum of its global functions.

## Main results

* `Stacks.AffineAlgebraEquivalence.isAffine_relativeSpec`: **the relative spectrum over an
  affine base is affine.**
* `Stacks.AffineAlgebraEquivalence.relativeSpecSectionsIso`: its ring of global functions is
  `Γ(S, A)`.
* `Stacks.AffineAlgebraEquivalence.relativeSpecIsoSpecSections`: **[Stacks, Tag 01LT] at the
  level of schemes**, `Spec_S(A) ≅ Spec Γ(S, A)`.

## Implementation notes

`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` is an isomorphism in the category of
`𝒪_S`-algebras, that is in `Under S.sheaf`; forgetting the structure map and passing to
presheaves evaluates it at `⊤`. The preimage of `⊤` under the structure morphism is `⊤`, so no
transport along an equality of opens is needed and the two sides of
`relativeSpecSectionsIso` are the global sections of the two sheaves on the nose.

No compatibility of `relativeSpecIsoSpecSections` with the structure morphisms is claimed: it
is an isomorphism of schemes, not of schemes over `S`. What it is for is the base change
`Spec_X(f^* A) ≅ Spec Γ(S, A) ×_S X` of [Stacks, Tag 01LX] part (2), where the base of the
fibre product is the *target* of `relativeSpecToBase`, not `S`.

## References

* [Stacks Project, Tag 01LT](https://stacks.math.columbia.edu/tag/01LT)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {S : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf.{u} S)
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]

/-- **The relative spectrum of a quasi-coherent algebra over an affine base is affine.** Its
structure morphism is affine by [Stacks, Tag 01LX] part (1),
`Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase`, and the source of an affine
morphism with affine target is affine. -/
@[sga "3 I 4.2" "special case"]
public theorem isAffine_relativeSpec [IsAffine S] : IsAffine (relativeSpec A) :=
  isAffine_of_isAffineHom (relativeSpecToBase A)

/-- **The ring of global functions of the relative spectrum is the ring of global sections of
the algebra.** This is [Stacks, Tag 01LX] part (3),
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`, evaluated at the top open: the
preimage of `⊤` is `⊤`, so the global sections of `π_* 𝒪_{Spec_S(A)}` are the global functions
of `Spec_S(A)`. No affineness of the base is needed. -/
public noncomputable def relativeSpecSectionsIso :
    Γ(relativeSpec A, ⊤) ≅ A.right.obj.obj (op (⊤ : S.Opens)) :=
  ((sheafToPresheaf _ _).mapIso
    ((Under.forget S.sheaf).mapIso (pushforwardAlgebraIso A))).app (op (⊤ : S.Opens))

/-- **[Stacks, Tag 01LT] at the level of schemes.** Over an affine base the relative spectrum
of a quasi-coherent sheaf of algebras is the spectrum of the ring of global sections of the
algebra:

`Spec_S(A) ≅ Spec Γ(S, A)`.

`Stacks.RelativeSpec.relativeSpecFunctor_representableBy` is the same tag in its
functor-of-points form; this is the identification with the glued relative spectrum
`Stacks.AffineAlgebraEquivalence.relativeSpec`.

It is an isomorphism of schemes; no compatibility with the structure morphism to `S` is
claimed. -/
@[stacks 01LT "the scheme-level form: over an affine base the relative spectrum is the \
spectrum of the ring of global sections of the algebra"]
public noncomputable def relativeSpecIsoSpecSections [IsAffine S] :
    relativeSpec A ≅ Spec (A.right.obj.obj (op (⊤ : S.Opens))) :=
  haveI := isAffine_relativeSpec A
  (relativeSpec A).isoSpec ≪≫ Scheme.Spec.mapIso (relativeSpecSectionsIso A).symm.op

end Stacks.AffineAlgebraEquivalence

end
