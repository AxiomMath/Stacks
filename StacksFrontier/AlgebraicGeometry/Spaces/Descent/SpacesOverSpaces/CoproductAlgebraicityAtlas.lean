module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductAlgebraicity

/-!
# The algebraic sheaf coproduct under the hypothesis of Stacks 02WQ itself

`AlgebraicGeometry.Space.Descent.sigmaAlgebraicSheafCoproduct` produces an algebraic sheaf
coproduct of a family of algebraic spaces from
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`, a bound on the index type by the
cofinality of the site's size cutoff. That bound is *stronger* than what Stacks 02WQ asks, which
is only that the coproduct of a choice of atlases of the members be an object of the site.

This file produces the algebraic sheaf coproduct under that weaker, source-level hypothesis. It
is available because the only clause of algebraicity that an
`AlgebraicGeometry.Space.Descent.AlgebraicSheafCoproduct` asks for is the atlas: the sheaf
condition holds because its vertex is a sheaf, and the diagonal is representable for an index
type of any size whatever, by
`AlgebraicGeometry.relativelyRepresentable_diag_of_isColimit_cofan`. The cofinality bound is
what the *diagonal* clause of `AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit` consumes,
and here it is not needed, so what remains is exactly
`AlgebraicGeometry.Space.exists_atlas_of_isColimit_of_contains`, whose own docstring records
that it uses no bound on the size of the index type.

Only `Small.{u} I` remains, and it is not a restriction that can be removed: without it the
coproduct of the sources does not exist in sheaves on the site, nor the coproduct of the atlases
in schemes, so neither side of Stacks 0ADK can be formed.

## Main results

* `AlgebraicGeometry.Space.Descent.contains_sigma_shrink`: a coproduct of schemes contained in
  the site stays contained when reindexed along the canonical `u`-small copy of the index.
* `AlgebraicGeometry.Space.Descent.exists_atlas_of_isColimit_cofan_spaceSheaf_of_contains`: the
  atlas clause of an algebraic sheaf coproduct, under the hypothesis of Stacks 02WQ.
* `AlgebraicGeometry.Space.Descent.algebraicSheafCoproductOfContainsSigma` and
  `AlgebraicGeometry.Space.Descent.nonempty_algebraicSheafCoproduct_of_containsSigma`: hence the
  algebraic sheaf coproduct itself.

## Implementation notes

The hypothesis is stated on the given index type `I`, which may live in any universe, whereas
`AlgebraicGeometry.Space.exists_atlas_of_isColimit_of_contains` asks for one in the working
universe. `AlgebraicGeometry.Space.Descent.contains_sigma_shrink` moves the hypothesis to
`Shrink I` along `CategoryTheory.Limits.Sigma.whiskerEquiv` and
`AlgebraicGeometry.Scheme.size_congr`, and the colimit cofan is moved by
`CategoryTheory.Limits.Cofan.isColimitEquivOfEquiv`, as in
`AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le`.

Under `AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex` the hypothesis below holds for every
choice of atlases, by `AlgebraicGeometry.BigFppfOver.contains_sigma_toScheme`; that is the
precise sense in which this strengthens
`AlgebraicGeometry.Space.Descent.nonempty_algebraicSheafCoproduct`. It does not supersede it for
descent data: the hypothesis here refers to a choice of atlases of the family, so it is not a
condition on the index type alone, and the objects of the descent data varying over a whole
category cannot be covered by one instance of it.

Nothing here carries a `@[stacks 02WQ]` attribute: that tag is attached to
`AlgebraicGeometry.isAlgebraicSpace_coproduct`.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 0ADK](https://stacks.math.columbia.edu/tag/0ADK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v w

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A coproduct of schemes contained in the site stays contained when the index is replaced
by its canonical `u`-small copy.** The two coproducts are isomorphic by
`CategoryTheory.Limits.Sigma.whiskerEquiv`, and the size of a scheme is an isomorphism
invariant. -/
public theorem contains_sigma_shrink {I : Type v} [Small.{u} I] (Z : I → Scheme.{u})
    (hsum : B.Contains (∐ Z)) :
    B.Contains (∐ fun k : Shrink.{u} I => Z ((equivShrink.{u} I).symm k)) := by
  have e : (∐ Z) ≅ ∐ fun k : Shrink.{u} I => Z ((equivShrink.{u} I).symm k) :=
    Sigma.whiskerEquiv (equivShrink.{u} I) fun i => eqToIso (by simp)
  change (∐ Z).size < B.cutoff at hsum
  rwa [Scheme.size_congr e] at hsum

section Atlas

variable {I : Type v} [Small.{u} I]
  (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
  (U : I → BigFppfOver B S hS) (a : ∀ i, yoneda.obj (U i) ⟶ X i)

/-- **The atlas clause of an algebraic sheaf coproduct, under the hypothesis of Stacks 02WQ.**

Given surjective étale scheme atlases `a i` of the members whose disjoint union is an object of
the site, the coproduct of the members in sheaves carries a surjective étale scheme atlas. No
bound on the size of the index type is used beyond `Small.{u} I`: the diagonal of the coproduct
is representable for an index type of any size, by
`AlgebraicGeometry.relativelyRepresentable_diag_of_isColimit_cofan`, and that is the only other
input of `AlgebraicGeometry.Space.exists_atlas_of_isColimit_of_contains`. -/
public theorem exists_atlas_of_isColimit_cofan_spaceSheaf_of_contains
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, spaceSheaf (X i) (hX i) ⟶ G) (hG : IsColimit (Cofan.mk G ι))
    (hsurj : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (a i))
    (het : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (a i))
    (hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (U i))) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ G.obj),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g :=
  AlgebraicGeometry.Space.exists_atlas_of_isColimit_of_contains B S hS
    (fun k => ι ((equivShrink.{u} I).symm k))
    ((Cofan.isColimitEquivOfEquiv (equivShrink.{u} I).symm (Cofan.mk G ι)) hG)
    (fun k => U ((equivShrink.{u} I).symm k)) (fun k => a ((equivShrink.{u} I).symm k))
    (fun _ => hsurj _) (fun _ => het _)
    (contains_sigma_shrink (fun i => (BigFppfOver.toScheme B S hS).obj (U i)) hsum)
    (relativelyRepresentable_diag_of_isColimit_cofan ι hG
      fun i => (hX i).diagonal_representable)

/-- **A family of algebraic spaces whose chosen atlases have their disjoint union in the site
has an algebraic sheaf coproduct**, namely its coproduct in sheaves on the big fppf site
over `S`.

This is `AlgebraicGeometry.Space.Descent.sigmaAlgebraicSheafCoproduct` under the hypothesis of
Stacks 02WQ in place of `AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`, which is the
stronger of the two. -/
public def algebraicSheafCoproductOfContainsSigma
    (hsurj : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (a i))
    (het : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (a i))
    (hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (U i))) :
    AlgebraicSheafCoproduct X hX where
  sheaf := ∐ fun i => spaceSheaf (X i) (hX i)
  ι := Sigma.ι _
  isColimit := coproductIsCoproduct fun i => spaceSheaf (X i) (hX i)
  exists_atlas := exists_atlas_of_isColimit_cofan_spaceSheaf_of_contains X hX U a _
    (coproductIsCoproduct fun i => spaceSheaf (X i) (hX i)) hsurj het hsum

/-- **Stacks 02WQ's own hypothesis suffices for an algebraic sheaf coproduct.** A family of
algebraic spaces over `S`, indexed by a `u`-small type and equipped with surjective étale
scheme atlases whose disjoint union is an object of the site, has an algebraic sheaf
coproduct. -/
public theorem nonempty_algebraicSheafCoproduct_of_containsSigma
    (hsurj : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (a i))
    (het : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (a i))
    (hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (U i))) :
    Nonempty (AlgebraicSheafCoproduct X hX) :=
  ⟨algebraicSheafCoproductOfContainsSigma X hX U a hsurj het hsum⟩

end Atlas

end AlgebraicGeometry.Space.Descent

end
