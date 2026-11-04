module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineModuliSpaceUniform
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeOfRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineModuliSpace

/-!
# The moduli space of a well-nigh affine stack is a uniform categorical moduli space (Stacks 0DUR)

Let `𝒳` be a well-nigh affine algebraic stack and `f : 𝒳 ⟶ M` the morphism of Stacks 0DUP, a
uniform categorical moduli space in the category of affine schemes. **Stacks 0DUR** says that `f`
is a uniform categorical moduli space, in the category of all algebraic spaces.

The statement is made for every 1-morphism `f` from a well-nigh affine algebraic stack to an
algebraic space which is a uniform categorical moduli space in the category of affine algebraic
spaces: this is the property by which Stacks 0DUP characterizes its morphism (two such morphisms
are uniquely isomorphic by the Yoneda lemma), so the statement applies to it and to every
morphism isomorphic to it, and it is what Stacks 0DUS uses on the open substacks of an étale
neighbourhood.

## The proof

By Stacks 0DUJ the uniform statement reduces to the non-uniform one for the base changes along
flat morphisms from affine schemes, which are again well-nigh affine
(`AlgebraicGeometry.Stack.isUniformCategoricalModuliSpace_of_isWellNighAffine_of`). For the
non-uniform statement, Stacks 0DUM presents `𝒳` as the quotient stack of a groupoid scheme
`(U, R, s, t, c)` with `U`, `R` affine and `s`, `t` finite locally free, read as a groupoid scheme
by `AlgebraicGeometry.Space.representedGroupoidScheme`; the canonical morphism `U ⟶ Spec C` to the
spectrum of the ring of invariants is a categorical quotient in the category of algebraic spaces
(`AlgebraicGeometry.Space.existsUnique_comp_quotientSite`, the source's argument: uniqueness by the
equalizer, which is a scheme because the diagonal of an algebraic space is representable;
existence étale locally on `Spec C`, by Stacks 07S0, 03JE and 0DT9 applied to `V ×_Y U` for an
étale `V ⟶ Y`), and Stacks 0DUH turns this into the moduli-space property of `f`
(`AlgebraicGeometry.Stack.isCategoricalModuliSpace_of_presentation`).

## Main results

* `AlgebraicGeometry.Stack.isCategoricalModuliSpace_of_isWellNighAffine`: the non-uniform
  statement.
* `AlgebraicGeometry.Stack.isUniformCategoricalModuliSpace_of_isUniformCategoricalModuliSpaceIn`:
  the statement for every such 1-morphism.
* `AlgebraicGeometry.Stack.isUniformCategoricalModuliSpace_of_isWellNighAffine`: **Stacks 0DUR**.

## References

* [Stacks Project, Tag 0DUR](https://stacks.math.columbia.edu/tag/0DUR)
* [Stacks Project, Tag 0DUP](https://stacks.math.columbia.edu/tag/0DUP)
-/

universe u w

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open AlgebraicGeometry.GroupoidScheme

noncomputable section

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism from a well-nigh affine algebraic stack to an algebraic space which is a
categorical moduli space among affine algebraic spaces is a categorical moduli space.** -/
theorem isCategoricalModuliSpace_of_isWellNighAffine (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) (N : AlgebraicSpaces B S hS)
    (f : 𝒳.val ⟶ fibredCategory B S hS N.obj)
    (hf : IsCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj) N f) :
    IsCategoricalModuliSpace B S hS N f := by
  obtain ⟨U, R, s, t, c, hG, hU, hR, hs, ht, ⟨E⟩⟩ :=
    hasAffineFiniteLocallyFreeGroupoidPresentation_of_isWellNighAffine B S hS 𝒳 h𝒳
  let G := Space.representedGroupoidScheme s t c hG
  have : IsAffine G.objects.left := hU
  have : IsAffine G.arrows.left := hR
  have : IsFiniteLocallyFree G.source.left := hs
  have : IsFiniteLocallyFree G.target.left := ht
  have hUc : B.Contains G.objects.left := U.left.2
  have hRc : B.Contains G.arrows.left := R.left.2
  exact isCategoricalModuliSpace_of_presentation G hUc hRc (invariantSpectrumToBase G)
    (objectsToInvariantSpectrum_comp_invariantSpectrumToBase G)
    (Space.contains_spec_invariantRing_of_contains G hUc) c hG E N f hf

/-- **Every 1-morphism from a well-nigh affine algebraic stack to an algebraic space which is a
uniform categorical moduli space among affine algebraic spaces is a uniform categorical moduli
space.** -/
theorem isUniformCategoricalModuliSpace_of_isUniformCategoricalModuliSpaceIn
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) (M : AlgebraicSpaces B S hS)
    (f : 𝒳.val ⟶ fibredCategory B S hS M.obj)
    (hf : IsUniformCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj)
      M f) :
    IsUniformCategoricalModuliSpace B S hS M f :=
  isUniformCategoricalModuliSpace_of_isWellNighAffine_of B S hS
    (isCategoricalModuliSpace_of_isWellNighAffine B S hS) 𝒳 h𝒳 M f hf

/-- **Stacks 0DUR.** Let `𝒳` be a well-nigh affine algebraic stack. The morphism `f : 𝒳 ⟶ M` of
Stacks 0DUP is a uniform categorical moduli space.

The first clause is the morphism of Stacks 0DUP with all the properties that lemma gives it, and
the conclusion of Stacks 0DUR. The second clause says the same of every 1-morphism to an algebraic
space which is a uniform categorical moduli space in the category of affine algebraic spaces, the
property by which Stacks 0DUP characterizes its morphism up to unique isomorphism. -/
@[stacks 0DUR]
theorem isUniformCategoricalModuliSpace_of_isWellNighAffine (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) :
    (∃ (M : AlgebraicSpaces B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property),
        IsUniformCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj) M
            f.hom ∧
          AlgebraicStacks.IsSeparated B S hS f ∧ IsQuasiCompactMorphism.{u, w} B S hS f ∧
          UniversalHomeomorphism B S hS f ∧ IsUniformCategoricalModuliSpace B S hS M f.hom) ∧
      ∀ (M : AlgebraicSpaces B S hS) (f : 𝒳.val ⟶ fibredCategory B S hS M.obj),
        IsUniformCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj)
          M f →
        IsUniformCategoricalModuliSpace B S hS M f := by
  refine ⟨?_, isUniformCategoricalModuliSpace_of_isUniformCategoricalModuliSpaceIn B S hS 𝒳 h𝒳⟩
  obtain ⟨M, f, hf, hsep, hqc, huh⟩ := exists_isUniformCategoricalModuliSpaceIn_of_isWellNighAffine
    B S hS 𝒳 h𝒳
  exact ⟨M, f, hf, hsep, hqc, huh,
    isUniformCategoricalModuliSpace_of_isUniformCategoricalModuliSpaceIn B S hS 𝒳 h𝒳 M f.hom hf⟩

end AlgebraicGeometry.Stack

end

end
