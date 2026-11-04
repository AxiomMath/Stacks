module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Reducing quasi-compactness of a universally closed morphism to an affine base

Stacks 04XW asserts that a universally closed morphism of algebraic spaces is quasi-compact.
Quasi-compactness of a morphism, in the sense of Stacks 03HE, quantifies over all morphisms
from quasi-compact algebraic spaces, whereas the proof of the source is run over an affine
base: the base is replaced by `Spec(B)` and a polynomial algebra `B[a_i ; i \in I]` on an index
set of a quasi-compact open covering of the source is formed.

This file performs that replacement of the base, and only that. It isolates the affine case as
a hypothesis, so that the remaining content of Stacks 04XW is exactly one statement: a
universally closed morphism of algebraic spaces whose target is an affine scheme has
quasi-compact source.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_universallyClosed_of_affine_base`: a universally
  closed morphism of algebraic spaces is quasi-compact as soon as every universally closed
  morphism of algebraic spaces with affine representable target has quasi-compact source.

## Implementation notes

No declaration here carries `@[stacks 04XW]`: the statement of that tag is unconditional, and
the hypothesis `haffine` below is the mathematical content of the tag, not a formal
consequence of anything in the tree.

The three steps are all available. A quasi-compact algebraic space receives a surjective étale
morphism from an affine scheme of the site by Stacks 03H6,
`AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`. A base
change of a universally closed morphism is universally closed by Stacks 03IS,
`AlgebraicGeometry.Space.universallyClosed_pullback`, which is applied twice: once to replace
the morphism by its base change along the test morphism, and once more to replace the test
space by the affine chart. Quasi-compactness of an algebraic space propagates along a
surjective étale morphism by `AlgebraicGeometry.Space.IsQuasiCompactSpace.of_surjective_etale`,
and the second projection of the fibre product over the test space is such a morphism because
`CategoryTheory.MorphismProperty.presheaf` is stable under base change.

The algebraicity hypotheses of `AlgebraicGeometry.Space.UniversallyClosed` are propositions and
are therefore definitionally irrelevant; the hypothesis `haffine` quantifies over them rather
than naming a particular proof of algebraicity of a representable presheaf, of which the tree
carries two.

## References

* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03IS](https://stacks.math.columbia.edu/tag/03IS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The affine base reduction for Stacks 04XW.** Let `f : X ⟶ Y` be a universally closed
morphism of algebraic spaces over `S`. Suppose that every universally closed morphism of
algebraic spaces over `S` whose target is the presheaf represented by an affine scheme of the
site has quasi-compact source. Then `f` is quasi-compact in the sense of Stacks 03HE.

A test morphism `g : Z ⟶ Y` out of a quasi-compact algebraic space `Z` is pulled back along a
surjective étale morphism `a : h_V ⟶ Z` from an affine scheme `V`, which exists by Stacks 03H6.
The first projection of `Z ×_Y X` is universally closed, being a base change of `f`, and so is
the first projection of `h_V ×_Z (Z ×_Y X)`, being a base change of that; the hypothesis
applies to the latter. Its second projection to `Z ×_Y X` is a base change of `a`, hence
surjective and étale, so quasi-compactness transfers to `Z ×_Y X`. -/
theorem isQuasiCompact_of_universallyClosed_of_affine_base
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : UniversallyClosed B S hS f)
    (haffine : ∀ (V : BigFppfOver B S hS),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS W →
        IsAlgebraicSpace B S hS (yoneda.obj V) → ∀ h : W ⟶ yoneda.obj V,
        UniversallyClosed B S hS h → IsQuasiCompactSpace B S hS W) :
    IsQuasiCompact B S hS f := by
  intro Z hZ hqc g
  obtain ⟨V, a, hVaff, haS, haE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Z hZ).1 hqc
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hW : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hZ hX hY
  have hWuc : UniversallyClosed B S hS (pullback.fst g f) :=
    universallyClosed_pullback B S hS f g hf
  have hP : IsAlgebraicSpace B S hS (pullback a (pullback.fst g f)) :=
    isAlgebraicSpace_pullback B S hS a (pullback.fst g f) hV hW hZ
  have hPuc : UniversallyClosed B S hS (pullback.fst a (pullback.fst g f)) :=
    universallyClosed_pullback B S hS (pullback.fst g f) a hWuc
  have hPqc := haffine V hVaff _ hP hV _ hPuc
  have sq : IsPullback (pullback.fst a (pullback.fst g f))
      (pullback.snd a (pullback.fst g f)) a (pullback.fst g f) :=
    IsPullback.of_hasPullback _ _
  exact IsQuasiCompactSpace.of_surjective_etale B S hS
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq haS)
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq
      (presheaf_etale_of_isEtale B S hS haE)) hPqc

end AlgebraicGeometry.Space

end
