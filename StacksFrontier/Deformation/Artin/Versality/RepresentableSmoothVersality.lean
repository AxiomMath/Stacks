module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ArtinianSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.Deformation.Artin.Versality.SmoothPredeformationAlong

/-!
# Smooth 1-morphisms satisfy the versality condition of Stacks 07XS

Let `S` be a locally Noetherian scheme and let `p : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred
in groupoids over the big fppf category of `S` which is representable by algebraic spaces and
smooth. Then `p` induces, at every finite type field-valued point of `𝒳`, a smooth functor of
predeformation categories: this is the representable-and-smooth clause of **Stacks 07XW**, the
condition of Stacks 07XS. Its other clause, formal smoothness on objects, is
`Deformation.Artin.isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjects`.

## Main results

* `Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth'`: **Stacks
  07XW**, the representable-and-smooth clause, at exactly the source's hypotheses.

## Implementation notes

The source proves the lemma as a reformulation of Stacks 07WK, whose case (3) passes through the
implication of Stacks 04AM from smoothness to formal smoothness. Only the lifting problems that the
predeformation categories see are needed, namely thickenings of spectra of Artinian local rings,
and for those the implication is
`AlgebraicGeometry.Space.formallySmoothAlong_isSpecArtinianLocal_of_isSmooth`. The rest is
Stacks 06D3 along those test objects
(`AlgebraicGeometry.BigFppfOver.isFormallySmoothOnObjectsAlong_of_isRelativelyFormallySmoothAlong`)
followed by case (1) of Stacks 07WK along them
(`Deformation.Artin.isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjectsAlong`).

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 06D3](https://stacks.math.columbia.edu/tag/06D3)
* [Stacks Project, Tag 07WK](https://stacks.math.columbia.edu/tag/07WK)
* [Stacks Project, Tag 07XS](https://stacks.math.columbia.edu/tag/07XS)
* [Stacks Project, Tag 07XW](https://stacks.math.columbia.edu/tag/07XW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

/-- **Stacks 07XW, the representable-and-smooth clause.** A 1-morphism of categories fibred in
groupoids over the big fppf category of a locally Noetherian scheme `S` which is representable by
algebraic spaces and smooth induces a smooth functor of predeformation categories at every finite
type field-valued point of the source; that is, it satisfies the condition of Stacks 07XS. -/
@[stacks 07XW "the representable-and-smooth clause: representable by algebraic spaces and smooth \
implies smooth on predeformation categories"]
public theorem isSmoothOnPredeformationCategories_of_isRelativelySmooth'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hsmooth : Stack.IsRelativelySmooth B S hS p) :
    IsSmoothOnPredeformationCategories B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p) := by
  obtain ⟨hrep, hP⟩ := hsmooth
  refine isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjectsAlong B S hS p
    (BigFppfOver.isFormallySmoothOnObjectsAlong_of_isRelativelyFormallySmoothAlong B S hS _ p
      hrep ?_)
  intro U y hy F hF hE
  exact Space.formallySmoothAlong_isSpecArtinianLocal_of_isSmooth B S hS
    (ObjectProperty.FullSubcategory.property _) _ (hP U y hy F hF hE)

end Deformation.Artin

end
