module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentSections
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopologyEtaleComparison

/-!
# The h sheaf condition for `π_S⁻¹F`, from descent along proper surjections

Let `F` be a sheaf of sets on the small étale site of `S`. By
`AlgebraicGeometry.smallEtaleInverseImage_isSheaf_h_of_isProperFinitePresentationSheaf`,
`π_S⁻¹F` is an h sheaf as soon as it satisfies descent along every proper surjective morphism of
finite presentation of the big h category over `S`. That remaining half of Stacks 0EW8 is
deduced here from effective descent of small étale sheaves along proper surjections, Stacks 0GF0,
taken as the single named hypothesis.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImage_isProperFinitePresentationSheaf_of_descent` — the
  proper half of the h sheaf condition, from effective descent along proper surjections.
* `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_h_of_descent` — Stacks 0EW8, with the
  conclusion of Stacks 0GF0 as the single hypothesis.

## Implementation notes

The argument is the one for Stacks 0DDW,
`AlgebraicGeometry.isSheafFor_smallEtaleInverseImage_singleton_of_isEquivalence`. The source
deduces Stacks 0EW8 from Stacks 0DDW, since an h covering is a ph covering, but the big h and
big ph sites of this development are separate structures, so the argument is repeated on the h
site. Finite presentation is not used.

## References

* [Stacks Project, Tag 0DDW](https://stacks.math.columbia.edu/tag/0DDW)
* [Stacks Project, Tag 0EW8](https://stacks.math.columbia.edu/tag/0EW8)
* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) S hS) (Type (u + 1)))

/-- **Descent along proper surjections gives the proper half of the h sheaf condition.** If
descent of small étale sheaves along every proper surjective morphism of the underlying category
is effective (Stacks 0GF0), then `π_S⁻¹F` satisfies descent along every proper surjective
morphism of finite presentation of the big h category over `S`, by
`AlgebraicGeometry.isSheafFor_smallEtaleInverseImage_singleton_of_isEquivalence`. Finite
presentation is not used. -/
public theorem smallEtaleInverseImage_isProperFinitePresentationSheaf_of_descent
    (h0GF0 : ∀ {X Y : (hAssociatedBigEtaleSite B).Scheme} (f : X ⟶ Y)
      [Surjective ((hAssociatedBigEtaleSite B).inclusion.map f)]
      [IsProper ((hAssociatedBigEtaleSite B).inclusion.map f)],
      (smallEtaleSheafDescentFunctor (hAssociatedBigEtaleSite B) f).IsEquivalence) :
    BigHOver.IsProperFinitePresentationSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj := by
  intro X Y f hp hs _
  exact isSheafFor_smallEtaleInverseImage_singleton_of_isEquivalence (hAssociatedBigEtaleSite B)
    ((hAssociatedBigEtaleSite B).obj S hS) F f (@h0GF0 _ _ f.left hs hp)

/-- **Stacks 0EW8, granted effective descent along proper surjections (Stacks 0GF0).** For a sheaf
of sets `F` on the small étale site of `S`, the rule `X ↦ Γ(X_ét, f_X⁻¹F)` — the presheaf
underlying `π_S⁻¹F`, by `AlgebraicGeometry.etaleInverseImageSectionsIso` — is a sheaf for the
h topology of the big h category over `S`, and the unit of `ε_S⁻¹ ⊣ ε_{S,*}` at `π_S⁻¹F` is an
isomorphism, so the h sheaf is `ε_S⁻¹π_S⁻¹F`. That `π_S⁻¹F` is a sheaf for the étale topology,
and is the rule on the big étale site, holds by construction and by Stacks 09XN.

The single input `h0GF0` is the conclusion of Stacks 0GF0 on the underlying category of the
site. -/
public theorem smallEtaleInverseImage_isSheaf_h_of_descent
    (h0GF0 : ∀ {X Y : (hAssociatedBigEtaleSite B).Scheme} (f : X ⟶ Y)
      [Surjective ((hAssociatedBigEtaleSite B).inclusion.map f)]
      [IsProper ((hAssociatedBigEtaleSite B).inclusion.map f)],
      (smallEtaleSheafDescentFunctor (hAssociatedBigEtaleSite B) f).IsEquivalence) :
    Presieve.IsSheaf (BigHOver.topology B S hS)
        ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj
          F).obj ∧
      IsIso ((hToBigEtaleMorphism B (B.obj S hS)).adj.unit.app
        ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj F)) := by
  have h := smallEtaleInverseImage_isProperFinitePresentationSheaf_of_descent B S hS F h0GF0
  exact ⟨(isSheaf_iff_isSheaf_of_type _ _).mp
      (smallEtaleInverseImage_isSheaf_h_of_isProperFinitePresentationSheaf B S hS F h),
    smallEtaleInverseImage_isIso_hToBigEtale_unit_app_of_properFinitePresentation B S hS F h⟩

end AlgebraicGeometry

end
