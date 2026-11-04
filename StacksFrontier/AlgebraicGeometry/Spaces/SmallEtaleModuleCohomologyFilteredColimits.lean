module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyFilteredColimits

/-!
# Filtered colimits and the cohomology of `𝒪_F`-modules on the small étale site

On a quasi-compact and quasi-separated algebraic space `F` over a scheme `S`, the cohomology of
`𝒪_F`-modules on the small étale site commutes with filtered colimits: for every filtered diagram
`D` of `𝒪_F`-modules and every degree `p`, the canonical comparison
`colim_i H^p(F, D_i) ⟶ H^p(F, colim_i D_i)` is an isomorphism.

This is **Stacks 073E read at module coefficients**.  It is the abelian statement
`AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections`, which is Stacks 073E
itself, carried across Stacks 03FD by
`ModuleSheafCohomology.isIso_colimit_post_globalModuleCohomology`.

## Main results

* `AlgebraicGeometry.Space.isIso_colimit_post_smallEtaleModuleCohomology`: **the comparison for
  the cohomology of `𝒪_F`-modules is an isomorphism.**
* `AlgebraicGeometry.Space.preservesColimit_smallEtaleModuleCohomology`: the same as preservation
  of the colimit.

## Implementation notes

*The module universe.*  Stacks 03FD on this site is
`AlgebraicGeometry.Space.smallEtaleGlobalSectionsComparisonIso`, whose module universe is
`max (u + 1) w`, and the abelian statement it has to be fed is at the *same* coefficient universe.
`AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections` is available only at
`Ab.{u + 1}`, so the conclusion below is at module universe `u + 1`, that being the one value of
`max (u + 1) w` the abelian input exists at.  Every universe of
`ModuleSheafCohomology.isIso_colimit_post_globalModuleCohomology` is therefore supplied
explicitly, and the cohomology is named by
`Stacks.Cohomology.SiteModules.globalModuleCohomology`: written out as a `Functor.rightDerived`
at the concrete module universe `u + 1`, the statement sets instance search the constraint
`max (u + 1) ?w =?= u + 1`, which it cannot solve, and the enough-injectives and abelian data of
the modules are not found.

*What this does not reach.*  The module universe of
`AlgebraicGeometry.Space.BaseChangeDiagram`, and so of the comparison map of Stacks 073K part (2)
(`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap`), is the universe `u`
of the structure rings, not `u + 1`: `AlgebraicGeometry.Space.Modules.{u, u}`.  Stacks 03FD is not
available there -- `CategoryTheory.SheafOfModules.toSheaf` sends modules at universe `m` to
abelian sheaves at coefficient universe `m`, and the comparison needs the coefficient universe to
contain the universe `u + 1` of the objects of the site, so `max (u + 1) w = u` is impossible.
This is the same obstruction recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseRingUniverse` and of
`StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections`, and it is why the statements below
do not discharge the filtered-colimit step of Stacks 073K part (2).

*No `@[stacks]` attribute.*  [Stacks, Tag 073E] is a statement about *abelian* sheaves -- "for
every filtered diagram of abelian sheaves on `X_étale`" -- and is registered in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits` on exactly that
statement.  The module-coefficient reading below is a different statement, not an enumerated part
of the tag, so it carries no registration.

## References

* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.Space

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 073E at module coefficients.**  On a quasi-compact and quasi-separated algebraic
space, the cohomology of `𝒪_F`-modules on the small étale site preserves a filtered colimit. -/
theorem preservesColimit_smallEtaleModuleCohomology
    (hqc : IsQuasiCompactSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u + 1}]
    (D : I ⥤ Modules.{u, u + 1} B S hS F hF) :
    have := site_hasSheafify_addCommGrp.{u + 1, u, u}
      (J := (smallEtaleRingedSite B S hS F hF).J)
    have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, u}
      (J := (smallEtaleRingedSite B S hS F hF).J)
    PreservesColimit D (globalModuleCohomology.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O) p) :=
  ModuleSheafCohomology.preservesColimit_globalModuleCohomology.{w, w, u + 1, u, u, u}
    (smallEtaleRingedSite B S hS F hF).J
    (ringSheaf (smallEtaleRingedSite B S hS F hF).O) p D
    (isIso_colimit_post_rightDerived_globalSections.{u, w} B S hS hZ F hF hqc hqs p _)

/-- **Stacks 073E at module coefficients**, as invertibility of the canonical comparison
`colim_i H^p(F, D_i) ⟶ H^p(F, colim_i D_i)` of the cohomology of `𝒪_F`-modules. -/
theorem isIso_colimit_post_smallEtaleModuleCohomology
    (hqc : IsQuasiCompactSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u + 1}]
    (D : I ⥤ Modules.{u, u + 1} B S hS F hF) :
    have := site_hasSheafify_addCommGrp.{u + 1, u, u}
      (J := (smallEtaleRingedSite B S hS F hF).J)
    have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, u}
      (J := (smallEtaleRingedSite B S hS F hF).J)
    IsIso (colimit.post D (globalModuleCohomology.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O) p)) :=
  ModuleSheafCohomology.isIso_colimit_post_globalModuleCohomology.{w, w, u + 1, u, u, u}
    (smallEtaleRingedSite B S hS F hF).J
    (ringSheaf (smallEtaleRingedSite B S hS F hF).O) p D
    (isIso_colimit_post_rightDerived_globalSections.{u, w} B S hS hZ F hF hqc hqs p _)

end AlgebraicGeometry.Space

end
