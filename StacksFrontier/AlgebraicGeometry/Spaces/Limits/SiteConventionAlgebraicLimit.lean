module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings

/-!
# The limit of a system satisfying the chapter's convention is an algebraic space

Let `D` be a cofiltered inverse system of quasi-compact algebraic spaces over `S` with affine
transition morphisms satisfying the chapter's standing convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`. Then `limit D` is an algebraic space:
the base change of an affine étale surjective atlas of one stage along the projection is
represented by an affine object of the site, by Stacks 07SF, part (1), under the convention;
it is a surjective étale atlas of the limit, being a base change of one, and the limit is a
sheaf, so Stacks 0BGQ applies.

No condition is asked of the index.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits`.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 0BGQ](https://stacks.math.columbia.edu/tag/0BGQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **The limit is an algebraic space under the chapter's convention.** On a site satisfying
`SiteContainsBaseChangeLimits` for `D`, the limit of a cofiltered diagram `D` of quasi-compact
algebraic spaces with affine transition morphisms is an algebraic space. -/
theorem isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i)) :
    IsAlgebraicSpace B S hS (limit D) := by
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, p₀, hU₀, hs₀, he₀⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (D.obj i) (hD i)).mp
      (hQc i)
  obtain ⟨U, p, q, hp⟩ :=
    isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D hconv hAffine i ⟨U₀, hU₀⟩ p₀
  have key (W : MorphismProperty Scheme.{u}) [W.IsStableUnderBaseChange]
      (h : (W.inverseImage (BigFppfOver.toScheme B S hS)).presheaf p₀) :
      (W.inverseImage (BigFppfOver.toScheme B S hS)).presheaf p :=
    have := (W.inverseImage (BigFppfOver.toScheme B S hS)).relative_isStableUnderBaseChange
      (F := yoneda)
    MorphismProperty.of_isPullback hp.flip h
  exact isAlgebraicSpace_of_surjective_etale_atlas B S hS
    (isSheaf_limit B S hS D fun i => (hD i).isSheaf) U.obj p
    (key _ hs₀) (key _ ((isEtale_iff_presheaf_of_yoneda B S hS p₀).mp he₀))

end AlgebraicGeometry.Space

end
