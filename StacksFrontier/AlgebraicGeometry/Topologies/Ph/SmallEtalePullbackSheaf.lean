module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfSheafCondition
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.PhToEtaleSquares
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackFpqcEtaleRefinement

/-!
# Inverse image from the small étale site, on the big ph site

Let `B` be a chosen big ph site, let `S` be one of its schemes and let `F` be a sheaf of sets
on the small étale site of `S`. The underlying category of `B` also carries the big étale
topology, by `AlgebraicGeometry.phAssociatedBigEtaleSite`, so the inverse image `π_S⁻¹F` along
the projection from the big étale topos over `S` to the small étale topos of `S` is a presheaf
on the big ph category over `S`; by the sections formula
`AlgebraicGeometry.etaleInverseImageSectionsIso` it is the rule `X ↦ Γ(X_ét, f_X⁻¹F)` of
Stacks 0DDW.

By Stacks 0DBQ the ph sheaf condition for a presheaf on that slice splits into Zariski descent
and descent along a single proper surjective morphism. The first half is proved here: a Zariski
covering family is an fpqc covering family, and `π_S⁻¹F` satisfies fpqc descent by Stacks 09XN.
The second half is taken as a hypothesis, and the remaining statements of Stacks 0DDW are
deduced from it.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImage_isZariskiSheaf_ph` — **Stacks 0DDW, the Zariski
  half of the ph sheaf condition**: `π_S⁻¹F` satisfies descent for every family of the big ph
  category over `S` whose underlying family of schemes is a Zariski covering.
* `AlgebraicGeometry.isIso_phToBigEtale_unit_app_iff` — the unit of `ε_X⁻¹ ⊣ ε_{X,*}` at a big
  étale sheaf over `X` is invertible exactly when that sheaf is a ph sheaf.
* `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph_of_isProperSurjectiveSheaf`,
  `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph_of_isAffineProperSurjectiveSheaf` and
  `AlgebraicGeometry.smallEtaleInverseImage_isIso_phToBigEtale_unit_app_of_properSurjective` —
  what the ph sheaf condition for `π_S⁻¹F`, and its identification with `ε_S⁻¹π_S⁻¹F`, reduce
  to.

## Implementation notes

The big ph category over `S` and the big étale category over `S` of the associated big étale
site are the same category: the associated site is built with the ph site's own cutoff, so the
two slices are slices of the same category over the same object. Only the topologies differ,
and `AlgebraicGeometry.IsZariskiSheaf` names a condition on a presheaf which does not mention
either topology, so it can be read off the fpqc sheaf condition of Stacks 09XN directly.

That the unit of the change-of-topology adjunction detects the ph sheaf condition is the
general statement `Stacks.Sites.isIso_sheafAdjunctionContinuousId_unit_app_iff`, already used
for the fppf topology in Stacks 0DDL; the direct image of `ε_X` is restriction along the
identity functor of the common slice, so it is fully faithful.

The remaining half of Stacks 0DDW — descent along a proper surjective morphism, equivalently
the equalizer diagram of the source — is the hypothesis of
`AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph_of_isProperSurjectiveSheaf`. The argument of
the source takes stalks at a geometric point and appeals to the proper base change computation
of the stalk of a pushforward, Stacks 0A3T; the route through effective descent of small étale
sheaves along a proper surjective morphism, Stacks 0GF0, rests on the same input through
Stacks 0GF1.

## References

* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
* [Stacks Project, Tag 0A3T](https://stacks.math.columbia.edu/tag/0A3T)
* [Stacks Project, Tag 0DBQ](https://stacks.math.columbia.edu/tag/0DBQ)
* [Stacks Project, Tag 0DDW](https://stacks.math.columbia.edu/tag/0DDW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

add_to_stacks 0DDW "the rule is the inverse image π_S⁻¹F on the big étale site"
  AlgebraicGeometry.etaleInverseImageSectionsIso

/-- The unit of `ε_X⁻¹ ⊣ ε_{X,*}` at a big étale sheaf `G` over `X` is an isomorphism exactly
when the underlying presheaf of `G` satisfies the ph sheaf condition.

The big ph and big étale sites share their slice over `X` and the direct image of `ε_X` is
restriction along the identity functor, so the statement is
`Stacks.Sites.isIso_sheafAdjunctionContinuousId_unit_app_iff`. -/
public theorem isIso_phToBigEtale_unit_app_iff (B : BigPHSite.{u}) (X : B.Schemes)
    (G : Sheaf (BigEtaleOver.topology (phAssociatedBigEtaleSite B) X.1 X.2) (Type (u + 1))) :
    IsIso ((phToBigEtaleMorphism B X).adj.unit.app G) ↔
      Presheaf.IsSheaf (B.topology.over X) G.obj :=
  Stacks.Sites.isIso_sheafAdjunctionContinuousId_unit_app_iff _ _ G

variable (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) S hS) (Type (u + 1)))

/-- **Stacks 0DDW, the Zariski half of the ph sheaf condition.** For a sheaf of sets `F` on the
small étale site of `S`, the presheaf underlying `π_S⁻¹F` — by the sections formula the rule
`X ↦ Γ(X_ét, f_X⁻¹F)` of the source — satisfies descent for every family of the big ph category
over `S` whose underlying family of schemes is a Zariski covering.

A Zariski covering family is an fpqc covering family, and `π_S⁻¹F` is a sheaf for the fpqc
topology of the slice by Stacks 09XN,
`AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc`. -/
@[stacks 0DDW "the Zariski half of the ph sheaf condition, Stacks 0DBQ; descent along a proper \
surjective morphism is not proved"]
public theorem smallEtaleInverseImage_isZariskiSheaf_ph :
    IsZariskiSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj := by
  intro X E hE
  have hfpqc := (isSheaf_iff_isSheaf_of_type _ _).mp
    (bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc (phAssociatedBigEtaleSite B) S hS F)
  refine hfpqc.isSheafFor E.presieve₀ (Precoverage.generate_mem_toGrothendieck ?_)
  rw [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
  exact Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ hE

/-- The ph sheaf condition for `π_S⁻¹F` reduces to descent along the proper surjective
morphisms of the big ph category over `S`: the Zariski half is
`AlgebraicGeometry.smallEtaleInverseImage_isZariskiSheaf_ph` and the characterization is
Stacks 0DBQ, `AlgebraicGeometry.isSheaf_iff_zariski_and_properSurjective`.

This is not Stacks 0DDW: the hypothesis is the half of the sheaf condition which the source
proves by taking stalks at a geometric point. -/
public theorem smallEtaleInverseImage_isSheaf_ph_of_isProperSurjectiveSheaf
    (h : IsProperSurjectiveSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj) :
    Presieve.IsSheaf (BigPHOver.topology B S hS)
      ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj :=
  (isSheaf_iff_zariski_and_properSurjective B S hS _).2
    ⟨smallEtaleInverseImage_isZariskiSheaf_ph B S hS F, h⟩

/-- The same reduction, with the proper surjective morphisms restricted to those with affine
target, by the affine reduction of Stacks 0DBQ,
`AlgebraicGeometry.properSurjective_iff_affine`. -/
public theorem smallEtaleInverseImage_isSheaf_ph_of_isAffineProperSurjectiveSheaf
    (h : IsAffineProperSurjectiveSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj) :
    Presieve.IsSheaf (BigPHOver.topology B S hS)
      ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj :=
  smallEtaleInverseImage_isSheaf_ph_of_isProperSurjectiveSheaf B S hS F
    ((properSurjective_iff_affine B S hS _
      (smallEtaleInverseImage_isZariskiSheaf_ph B S hS F)).2 h)

/-- Granted descent along the proper surjective morphisms, the rule `X ↦ Γ(X_ét, f_X⁻¹F)` is
`ε_S⁻¹π_S⁻¹F` on the big ph category over `S`: the unit of `ε_S⁻¹ ⊣ ε_{S,*}` at `π_S⁻¹F` is an
isomorphism, by `AlgebraicGeometry.isIso_phToBigEtale_unit_app_iff`.

This is the last clause of Stacks 0DDW, under the same hypothesis as
`AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph_of_isProperSurjectiveSheaf`. -/
public theorem smallEtaleInverseImage_isIso_phToBigEtale_unit_app_of_properSurjective
    (h : IsProperSurjectiveSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj) :
    IsIso ((phToBigEtaleMorphism B (B.obj S hS)).adj.unit.app
      ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj F)) :=
  (isIso_phToBigEtale_unit_app_iff B (B.obj S hS) _).2
    ((isSheaf_iff_isSheaf_of_type _ _).mpr
      (smallEtaleInverseImage_isSheaf_ph_of_isProperSurjectiveSheaf B S hS F h))

end AlgebraicGeometry

end
