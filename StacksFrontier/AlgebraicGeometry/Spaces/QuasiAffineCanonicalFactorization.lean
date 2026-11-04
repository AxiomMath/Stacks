module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineDirectImageFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineOpenImmersionAffineOver
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSpecFactorization

/-!
# Quasi-affineness through the canonical factorization of Stacks 081X

Let `f : Y ⟶ X` be a quasi-compact morphism of algebraic spaces over `S`, and let `P` be an
algebraic space affine over `X` together with an identification `e : P_* 𝒪_P ≅ f_* 𝒪_Y` of
`𝒪_X`-algebras, that is, a relative spectrum `\underline{Spec}_X(f_* 𝒪_Y)` of the direct image.
The universal property of an algebraic space affine over `X`
(`AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom`) attaches to `e` the canonical
morphism `Y ⟶ P` over `X` of Stacks 081X,
`AlgebraicGeometry.Space.overHomOfPushforwardAlgebraIso`.  This file proves Stacks 086S for it:
`f` is quasi-affine if and only if the canonical morphism is an open immersion.

For `f` quasi-compact and quasi-separated the relative spectrum is constructed from `f`
(`AlgebraicGeometry.Space.directImageSpec`, Stacks 081W at `f_* 𝒪_Y`), with canonical morphism
`AlgebraicGeometry.Space.toDirectImageSpec`, and Stacks 086S is stated for exactly that morphism.

## Main results

* `AlgebraicGeometry.Space.isQuasiAffineHom_iff_isOpenImmersion_toDirectImageSpec`: **Stacks 086S**
  — a quasi-compact quasi-separated `f : Y ⟶ X` is quasi-affine if and only if its canonical
  factorization `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` of Stacks 081X is an open immersion.
* `AlgebraicGeometry.Space.isQuasiAffineHom_iff_isOpenImmersion_overHomOfPushforwardAlgebraIso`:
  the same for the canonical morphism into any relative spectrum `(P, e)` of `f_* 𝒪_Y`, for `f`
  only quasi-compact.

## Implementation notes

The statement is `AlgebraicGeometry.Space.isQuasiAffineHom_iff_isOpenImmersion_affineOver` at
`g = AlgebraicGeometry.Space.overHomOfPushforwardAlgebraIso e`; the condition that `g` induce an
isomorphism of direct-image rings is the instance
`AlgebraicGeometry.Space.isIso_pushforwardRingMap_overHomOfPushforwardAlgebraIso`.

In the general form the relative spectrum enters as a pair `(P, e)`: any two such pairs are
isomorphic over `X` compatibly with their canonical morphisms, by the universal property, so the
statement does not depend on the choice.  Quasi-separatedness of `f`, assumed in the Stacks
Project so that `f_* 𝒪_Y` is quasi-coherent and its relative spectrum exists, is used only to
construct that pair, which is what `AlgebraicGeometry.Space.directImageSpec` does.

## References

* [Stacks Project, Tag 086S](https://stacks.math.columbia.edu/tag/086S)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 086S.**  Let `f : Y ⟶ X` be a quasi-compact morphism of algebraic spaces over `S`,
let `P` be an algebraic space affine over `X`, and let `e : P_* 𝒪_P ≅ f_* 𝒪_Y` identify its
direct-image algebra with that of `f`, so that `P` is the relative spectrum
`\underline{Spec}_X(f_* 𝒪_Y)`.  Then `f` is quasi-affine if and only if the canonical morphism
`Y ⟶ P` over `X` of Stacks 081X attached to `e` is an open immersion. -/
@[stacks 086S "for every algebraic space P affine over X with an identification e of its \
direct-image algebra with f_* O_Y, i.e. every relative spectrum of f_* O_Y: a quasi-compact f is \
quasi-affine iff the canonical morphism Y ⟶ P over X of 081X attached to e is an open immersion; \
quasi-separatedness of f is not needed once P and e are given"]
theorem isQuasiAffineHom_iff_isOpenImmersion_overHomOfPushforwardAlgebraIso
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hfqc : IsQuasiCompact B S hS f.hom)
    (P : AffineOver B S hS X)
    (e : pushforwardAlgebra B S hS P.obj ≅ pushforwardAlgebra B S hS (Over.mk f)) :
    IsQuasiAffineHom B S hS f.hom ↔
      IsOpenImmersion B S hS (overHomOfPushforwardAlgebraIso B S hS e).left.hom :=
  isQuasiAffineHom_iff_isOpenImmersion_affineOver B S hS f hfqc P _ inferInstance

/-- **Stacks 086S, in the corrected (bounded) form.**  A quasi-compact, quasi-separated morphism
`f : Y ⟶ X` of algebraic spaces over `S` is quasi-affine if and only if its canonical
factorization `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` of Stacks 081X is an open immersion.

The relative spectrum is `AlgebraicGeometry.Space.directImageSpec`, Stacks 081W in its corrected
form: the relative spectrum of a quasi-coherent algebra whose sections over every chart number
fewer than the cutoff of the site.  The unbounded form of 081V that the source's
`\underline{Spec}_X` presupposes is refuted in this development by
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`.
The size condition on `f_* 𝒪_Y` is proved, not assumed
(`AlgebraicGeometry.Space.sectionsBelowCutoff_pushforwardAlgebra`), so the hypotheses are exactly
those of the source. -/
@[stacks 086S "corrected (bounded) form: Spec_X(f_* O_Y) is directImageSpec f, the relative \
spectrum of 081W in its bounded form (the unbounded 081V is refuted by \
not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart), whose size condition on \
f_* O_Y is proved; the morphism is toDirectImageSpec f, the canonical factorization of 081X; \
hypotheses exactly f quasi-compact and quasi-separated"]
theorem isQuasiAffineHom_iff_isOpenImmersion_toDirectImageSpec {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    IsQuasiAffineHom B S hS f.hom ↔
      IsOpenImmersion B S hS (toDirectImageSpec B S hS f hfqc hfqs).left.hom :=
  isQuasiAffineHom_iff_isOpenImmersion_overHomOfPushforwardAlgebraIso B S hS f hfqc _ _

end AlgebraicGeometry.Space
