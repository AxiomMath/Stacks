module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardAlgebraFunctorFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecPointsSheaf

/-!
# Stacks 081W, the bounded case: the relative spectrum of a bounded quasi-coherent algebra

Let `X` be an algebraic space over a scheme `S` and `𝒜` a quasi-coherent sheaf of commutative
`𝒪_X`-algebras.  Stacks 081W defines the relative spectrum `\underline{Spec}_X(𝒜) ⟶ X` as the
affine morphism corresponding to `𝒜` under the anti-equivalence of Stacks 081V, that is, the
algebraic space `Y` affine over `X` with `Y_* 𝒪_Y ≅ 𝒜`.  This file constructs it *inside the big
fppf site of `X`*, for the algebras satisfying the size condition below, and proves that it is
that object.  The relative spectrum of an arbitrary quasi-coherent algebra, with no size
condition, is `AlgebraicGeometry.Space.relativeSpectrum` of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpectrum`, which carries the registration of
Stacks 081W: it lives on an enlargement of the big fppf site and is built from the construction
here, applied over that enlargement.

## The bounded case

In this development algebraic spaces live on a big fppf site with a cardinal cutoff, while sheaves
of algebras are unbounded, and an algebra with at least `B.cutoff` sections over some chart is the
direct image of no affine morphism:
`AlgebraicGeometry.Space.not_essSurj_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections` and
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart` refute
the literal statement (Stacks' own set-theoretic conventions, Sets §3.9, impose the same bound
implicitly).  So inside the site of `X` the statement is the **bounded case**: `𝒜` has fewer than
`B.cutoff` sections over every étale chart
(`AlgebraicGeometry.Space.AlgebraSheaf.SectionsBelowCutoff`), which is exactly the bound every
direct image of an affine morphism satisfies
(`AlgebraicGeometry.Space.sectionsBelowCutoff_of_mem_essImage`), so no algebra that has a relative
spectrum at all is excluded
(`AlgebraicGeometry.Space.essImage_boundedPushforwardAlgebraFunctor_iff`).

## Main definitions

* `AlgebraicGeometry.Space.boundedRelativeSpec`: the bounded case of **Stacks 081W**, the relative
  spectrum `\underline{Spec}_X(𝒜)` as an algebraic space affine over `X` in the site of `X`.
  Its functor of points is
  `AlgebraicGeometry.Space.relativeSpecPoints 𝒜`: a point with values in `T` is a point `x ∈ X(T)`
  with a morphism of `𝒪_X`-algebras `𝒜 ⟶ x_* 𝒪_T`.
* `AlgebraicGeometry.Space.pushforwardAlgebraBoundedRelativeSpecIso`: the identification
  `π_* 𝒪_{\underline{Spec}_X(𝒜)} ≅ 𝒜`.

## Main results

* `AlgebraicGeometry.Space.essSurj_boundedPushforwardAlgebraFunctor`: the essential surjectivity
  clause of Stacks 081V in its corrected form: every bounded quasi-coherent algebra is a direct
  image.
* `AlgebraicGeometry.Space.nonempty_iso_boundedRelativeSpec`: `\underline{Spec}_X(𝒜)` is *the*
  object corresponding to `𝒜`: every algebraic space affine over `X` whose direct image is `𝒜`
  is isomorphic to it over `X` (full faithfulness of the direct image).

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS}

/-- **Stacks 081W, the bounded case.** The relative spectrum `\underline{Spec}_X(𝒜)` of a
quasi-coherent `𝒪_X`-algebra `𝒜` with fewer than `B.cutoff` sections over every étale chart, as an
algebraic space affine over `X` in the big fppf site of `X`: the object whose direct image
`π_* 𝒪` is `𝒜` (`AlgebraicGeometry.Space.pushforwardAlgebraBoundedRelativeSpecIso`), unique up to
isomorphism over `X` (`AlgebraicGeometry.Space.nonempty_iso_boundedRelativeSpec`).

The size condition is the bound that every direct image of an affine morphism *in the same site*
satisfies: an algebra violating it is the direct image of no algebraic space of the site affine
over `X`
(`AlgebraicGeometry.Space.not_essSurj_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections`).
The relative spectrum of an arbitrary quasi-coherent algebra is
`AlgebraicGeometry.Space.relativeSpectrum`, which carries the full registration of the tag and is
this construction applied over an enlargement of the site.

The construction is the functor of points `AlgebraicGeometry.Space.relativeSpecPoints 𝒜`; that it
is an algebraic space affine over `X` is
`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_isAffineHom_relativeSpecPoints`. -/
@[stacks 081W "the bounded case only: the relative spectrum of a quasi-coherent O_X-algebra A \
with fewer than the big fppf site's cutoff many sections at every etale chart, built inside the \
site of X from its functor of points relativeSpecPoints A, with \
pushforwardAlgebraBoundedRelativeSpecIso and nonempty_iso_boundedRelativeSpec identifying it as \
the object corresponding to A under 081V. The tag for an arbitrary quasi-coherent algebra is \
relativeSpectrum (RelativeSpectrum), which applies this construction over an enlarged site"]
def boundedRelativeSpec (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj) : AffineOver B S hS X :=
  relativeSpecAffineOverOf B S hS A.obj hA (isSheaf_relativeSpecPoints B S hS A.obj) A.property

/-- **The direct image of the structure sheaf of `\underline{Spec}_X(𝒜)` is `𝒜`.** -/
def pushforwardAlgebraBoundedRelativeSpecIso (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj) :
    pushforwardAlgebra B S hS (boundedRelativeSpec B S hS A hA).obj ≅ A.obj :=
  pushforwardAlgebraRelativeSpecAffineOverOfIso B S hS A.obj hA
    (isSheaf_relativeSpecPoints B S hS A.obj) A.property

/-- **Every bounded quasi-coherent algebra is a direct image**: the essential surjectivity clause
of Stacks 081V, in its corrected form. -/
theorem essSurj_boundedPushforwardAlgebraFunctor (X : AlgebraicSpaces B S hS) :
    (boundedPushforwardAlgebraFunctor B S hS X).EssSurj :=
  (essSurj_boundedPushforwardAlgebraFunctor_iff B S hS).2 fun A hA =>
    ⟨op (boundedRelativeSpec B S hS A hA),
      ⟨(quasicoherentAlgebraInclusion B S hS X).preimageIso
        (pushforwardAlgebraBoundedRelativeSpecIso B S hS A hA)⟩⟩

/-- **`\underline{Spec}_X(𝒜)` is the object corresponding to `𝒜`**: an algebraic space affine over
`X` whose direct image is `𝒜` is isomorphic to it over `X`. -/
theorem nonempty_iso_boundedRelativeSpec (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj) (Y : AffineOver B S hS X)
    (e : pushforwardAlgebra B S hS Y.obj ≅ A.obj) :
    Nonempty (Y ≅ boundedRelativeSpec B S hS A hA) := by
  have := full_affinePushforwardAlgebraFunctor B S hS X
  have := faithful_affinePushforwardAlgebraFunctor B S hS X
  let e' : (quasicoherentPushforwardAlgebraFunctor B S hS X).obj (op Y) ≅
      (quasicoherentPushforwardAlgebraFunctor B S hS X).obj
        (op (boundedRelativeSpec B S hS A hA)) :=
    (quasicoherentAlgebraInclusion B S hS X).preimageIso
      (e ≪≫ (pushforwardAlgebraBoundedRelativeSpecIso B S hS A hA).symm)
  exact ⟨((quasicoherentPushforwardAlgebraFunctor B S hS X).preimageIso e').unop.symm⟩

end AlgebraicGeometry.Space

end
