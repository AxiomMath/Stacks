module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange

/-!
# Base change of an affine étale chart along an affine morphism of algebraic spaces

Let `f : Y ⟶ X` be a representable morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, and let `Q` be an étale scheme chart of `X` whose underlying scheme is
affine. Base change along `f` turns `Q` into an étale scheme chart `Q ×_X Y` of `Y`, by
Stacks 03G2, part (4). If `f` is an affine morphism in the sense of Stacks 03WF, then the
scheme underlying `Q ×_X Y` is again affine.

This is the geometric content of affineness that representability alone does not give: the
affine charts of `X` pull back to affine charts of `Y`.

## Main results

* `AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`: for an affine morphism `f : Y ⟶ X` of
  algebraic spaces and an étale chart `Q` of `X` with affine underlying scheme, the scheme
  underlying the base-changed chart `(smallBaseChange f).obj Q` is affine.

## Implementation notes

Affineness of `f` applies to the affine object `Q.left` of the big affine fppf site
`AlgebraicGeometry.BigAffineFppf` — the hypothesis on `Q` is exactly what promotes the chart's
source to that subcategory — and to the chart's structure morphism `Q.hom : yoneda.obj Q.left ⟶ X`
as the test morphism. It produces an *affine* object `W` of the site together with a pullback
square exhibiting `yoneda.obj W` as the fibre product of `f` and `Q.hom`.

The base-changed chart supplied by `AlgebraicGeometry.Space.smallBaseChange` is
`CategoryTheory.Functor.relativelyRepresentable.pullback` for the same pair, so
`CategoryTheory.Functor.relativelyRepresentable.isPullback` exhibits it as a fibre product of the
same cospan. Two pullbacks of one cospan are canonically isomorphic by
`CategoryTheory.IsPullback.isoIsPullback`, and here the isomorphism is one of representable
presheaves, hence comes from an isomorphism of the underlying objects of the site by full
faithfulness of Yoneda. Affineness then transfers along the induced isomorphism of schemes by
`AlgebraicGeometry.IsAffine.of_isIso`.

No comparison with the spaces-étale base change of Stacks 03G1 is needed, and the pullback
square used is the presheaf-level one of representability rather than its image
`AlgebraicGeometry.Space.smallBaseChange_isPullback` in the category of algebraic spaces: the
affineness hypothesis is itself stated at the level of presheaves on the big fppf site.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Affine morphisms pull affine étale charts back to affine étale charts.**

Let `f : Y ⟶ X` be a representable morphism of algebraic spaces over `S` which is affine in the
sense of Stacks 03WF, and let `Q` be an étale scheme chart of `X` whose underlying scheme is
affine. Then the scheme underlying the base-changed étale chart `Q ×_X Y` of `Y`, formed by
`AlgebraicGeometry.Space.smallBaseChange` as in Stacks 03G2, part (4), is affine.

Affineness of `f` tested on the affine chart `Q` produces an affine object of the site
representing the fibre product of `f` and `Q.hom`; the base-changed chart represents the same
fibre product, so the two are isomorphic and affineness transfers. -/
theorem isAffine_smallBaseChange_obj {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    (Q : SmallEtale B S hS X.1)
    (hQ : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj Q)) :
    IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj
      ((smallBaseChange B S hS f hf).obj Q)) := by
  obtain ⟨W, p, q, hpb⟩ := haff ⟨(SmallEtale.toOver B S hS X.1).obj Q, hQ⟩ Q.1.hom
  have hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj W)) := W.property
  have e := (BigFppfOver.toScheme B S hS).mapIso
    (yoneda.preimageIso (hpb.isoIsPullback _ _ (hf.isPullback Q.1.hom)))
  change IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.pullback Q.1.hom))
  exact IsAffine.of_isIso e.inv

end AlgebraicGeometry.Space

end
