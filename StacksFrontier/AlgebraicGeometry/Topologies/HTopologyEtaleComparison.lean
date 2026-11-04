module

public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfSheafCondition
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.HToEtaleSquares
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackFpqcEtaleRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion

/-!
# Inverse image from the small étale site, on the big h site

Let `B` be a chosen big h site, let `S` be one of its schemes and let `F` be a sheaf of sets on
the small étale site of `S`. The underlying category of `B` also carries the big étale topology,
by `AlgebraicGeometry.hAssociatedBigEtaleSite`, so the inverse image `π_S⁻¹F` along the
projection from the big étale topos over `S` to the small étale topos of `S` is a presheaf on
the big h category over `S`; by the sections formula
`AlgebraicGeometry.etaleInverseImageSectionsIso` it is the rule `X ↦ Γ(X_ét, f_X⁻¹F)` of
Stacks 0EW8.

By Stacks 0EU5 the h sheaf condition for a presheaf on that slice splits into Zariski descent
and descent along a single proper surjective morphism of finite presentation. The first half is
proved here: a Zariski covering family is an fpqc covering family, and `π_S⁻¹F` satisfies fpqc
descent by Stacks 09XN. The second half is the input this development does not have, and the
remaining statements of Stacks 0EW8 are recorded as consequences of it.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImage_isZariskiSheaf_h` — **Stacks 0EW8, the Zariski half
  of the h sheaf condition**: `π_S⁻¹F` satisfies descent for every family of the big h category
  over `S` whose underlying family of schemes is a Zariski covering.
* `AlgebraicGeometry.isIso_hToBigEtale_unit_app_iff` — the unit of `ε_X⁻¹ ⊣ ε_{X,*}` at a big
  étale sheaf over `X` is invertible exactly when that sheaf is an h sheaf.
* `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_h_of_isProperFinitePresentationSheaf`,
  `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_h_of_isAffineProperFinitePresentationSheaf`
  and
  `AlgebraicGeometry.smallEtaleInverseImage_isIso_hToBigEtale_unit_app_of_properFinitePresentation`
  — what the h sheaf condition for `π_S⁻¹F`, and its identification with `ε_S⁻¹π_S⁻¹F`, reduce
  to.

## Implementation notes

The big h category over `S` and the big étale category over `S` of the associated big étale site
are the same category: the associated site is built with the h site's own cutoff, so the two
slices are slices of the same category over the same object. Only the topologies differ, and
`AlgebraicGeometry.BigHOver.IsZariskiSheaf` names a condition on a presheaf which does not
mention either topology, so it can be read off the fpqc sheaf condition of Stacks 09XN directly.

That the unit of the change-of-topology adjunction detects the h sheaf condition is the general
statement `Stacks.Sites.isIso_sheafAdjunctionContinuousId_unit_app_iff`, already used for the
fppf topology in Stacks 0DDL; the direct image of `ε_X` is restriction along the identity functor
of the common slice, so it is fully faithful.

The remaining half of Stacks 0EW8 — descent along a proper surjective morphism of finite
presentation, equivalently the equalizer diagram of the source — is not proved here. The source
deduces it from the ph statement Stacks 0DDW, whose argument takes stalks at a geometric point
and appeals to the proper base change computation of the stalk of a pushforward, Stacks 0A3T.
The alternative route through effective descent of small étale sheaves along a proper surjection,
Stacks 0GF0, is formalized in this development only up to the dévissage Stacks 0GF1, which
`AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_proper` carries as
an explicit hypothesis; so that route does not discharge the gap either. The hypotheses of
`AlgebraicGeometry.smallEtaleInverseImage_isSheaf_h_of_isProperFinitePresentationSheaf` record
exactly what is missing. They are the h-site conditions of Stacks 0EU5, hence weaker than the
ph-site conditions carried by the sibling file for Stacks 0DDW: an h covering is a ph covering
whose members are locally of finite presentation.

## References

* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
* [Stacks Project, Tag 0A3T](https://stacks.math.columbia.edu/tag/0A3T)
* [Stacks Project, Tag 0DDW](https://stacks.math.columbia.edu/tag/0DDW)
* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
* [Stacks Project, Tag 0EW8](https://stacks.math.columbia.edu/tag/0EW8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The unit of `ε_X⁻¹ ⊣ ε_{X,*}` at a big étale sheaf `G` over `X` is an isomorphism exactly
when the underlying presheaf of `G` satisfies the h sheaf condition.

The big h and big étale sites share their slice over `X` and the direct image of `ε_X` is
restriction along the identity functor, so the statement is
`Stacks.Sites.isIso_sheafAdjunctionContinuousId_unit_app_iff`. -/
public theorem isIso_hToBigEtale_unit_app_iff (B : BigHSite.{u}) (X : B.Schemes)
    (G : Sheaf (BigEtaleOver.topology (hAssociatedBigEtaleSite B) X.1 X.2) (Type (u + 1))) :
    IsIso ((hToBigEtaleMorphism B X).adj.unit.app G) ↔
      Presheaf.IsSheaf (B.topology.over X) G.obj :=
  Stacks.Sites.isIso_sheafAdjunctionContinuousId_unit_app_iff _ _ G

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) S hS) (Type (u + 1)))

/-- **Stacks 0EW8, the Zariski half of the h sheaf condition.** For a sheaf of sets `F` on the
small étale site of `S`, the presheaf underlying `π_S⁻¹F` — by the sections formula the rule
`X ↦ Γ(X_ét, f_X⁻¹F)` of the source — satisfies descent for every family of the big h category
over `S` whose underlying family of schemes is a Zariski covering.

A Zariski covering family is an fpqc covering family, and `π_S⁻¹F` is a sheaf for the fpqc
topology of the slice by Stacks 09XN,
`AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc`. -/
@[stacks 0EW8 "the Zariski half of the h sheaf condition, condition (1) of Stacks 0EU5; descent \
along a proper surjective morphism of finite presentation is not proved"]
public theorem smallEtaleInverseImage_isZariskiSheaf_h :
    BigHOver.IsZariskiSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj := by
  intro X E hE
  have hfpqc := (isSheaf_iff_isSheaf_of_type _ _).mp
    (bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc (hAssociatedBigEtaleSite B) S hS F)
  refine hfpqc.isSheafFor E.presieve₀ (Precoverage.generate_mem_toGrothendieck ?_)
  rw [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
  exact Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ hE

/-- The h sheaf condition for `π_S⁻¹F` reduces to descent along the proper surjective morphisms
of finite presentation of the big h category over `S`: the Zariski half is
`AlgebraicGeometry.smallEtaleInverseImage_isZariskiSheaf_h` and the characterization is
Stacks 0EU5,
`AlgebraicGeometry.BigHOver.isSheaf_iff_isZariskiSheaf_and_isProperFinitePresentationSheaf`.

This is not Stacks 0EW8: the hypothesis is the half of the sheaf condition which the source
proves by taking stalks at a geometric point, and which this development does not have. -/
public theorem smallEtaleInverseImage_isSheaf_h_of_isProperFinitePresentationSheaf
    (h : BigHOver.IsProperFinitePresentationSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj) :
    Presheaf.IsSheaf (BigHOver.topology B S hS)
      ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj :=
  (BigHOver.isSheaf_iff_isZariskiSheaf_and_isProperFinitePresentationSheaf B S hS _).2
    ⟨smallEtaleInverseImage_isZariskiSheaf_h B S hS F, h⟩

/-- The same reduction, with the proper surjective morphisms of finite presentation restricted
to those with affine target, by the affine reduction of Stacks 0EU5,
`AlgebraicGeometry.BigHOver.isProperFinitePresentationSheaf_of_affine`. -/
public theorem smallEtaleInverseImage_isSheaf_h_of_isAffineProperFinitePresentationSheaf
    (h : BigHOver.IsAffineProperFinitePresentationSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj) :
    Presheaf.IsSheaf (BigHOver.topology B S hS)
      ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj :=
  smallEtaleInverseImage_isSheaf_h_of_isProperFinitePresentationSheaf B S hS F
    (BigHOver.isProperFinitePresentationSheaf_of_affine
      (smallEtaleInverseImage_isZariskiSheaf_h B S hS F) h)

/-- Granted descent along the proper surjective morphisms of finite presentation, the rule
`X ↦ Γ(X_ét, f_X⁻¹F)` is `ε_S⁻¹π_S⁻¹F` on the big h category over `S`: the unit of
`ε_S⁻¹ ⊣ ε_{S,*}` at `π_S⁻¹F` is an isomorphism, by
`AlgebraicGeometry.isIso_hToBigEtale_unit_app_iff`.

This is the last clause of Stacks 0EW8, under the same unproved hypothesis as
`AlgebraicGeometry.smallEtaleInverseImage_isSheaf_h_of_isProperFinitePresentationSheaf`. -/
public theorem smallEtaleInverseImage_isIso_hToBigEtale_unit_app_of_properFinitePresentation
    (h : BigHOver.IsProperFinitePresentationSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj) :
    IsIso ((hToBigEtaleMorphism B (B.obj S hS)).adj.unit.app
      ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj F)) :=
  (isIso_hToBigEtale_unit_app_iff B (B.obj S hS) _).2
    (smallEtaleInverseImage_isSheaf_h_of_isProperFinitePresentationSheaf B S hS F h)

end AlgebraicGeometry

end
