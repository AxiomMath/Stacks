module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleQuasiSplittingAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RestrictionSubgroupoidDerealization

/-!
# Shrinking the quasi-splitting of Stacks 04RY to an affine étale neighbourhood

**Stacks 04S0** says that for a groupoid scheme `(U, R, s, t, c)` with `U` affine and with `s` and
`t` flat and locally of finite presentation, and for a point `u` of `U` in the quasi-splitting
situation of Stacks 04RV, there are an *affine* scheme `U''`, an étale morphism `U'' ⟶ U` and a
point `u''` of `U''` over `u` with `κ(u) = κ(u'')` such that `R|_{U''}` is quasi-split over `u''`.

The shrinking itself is
`Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt`, which runs the last paragraph
of the source's proof on the output of Stacks 04RY packaged as
`Stacks.Groupoids.GroupoidScheme.EtaleQuasiSplitting`; that package is produced from Stacks 04RY
by `Stacks.Groupoids.GroupoidScheme.nonempty_etaleQuasiSplitting_of_derealization`, whose
de-realization step is
`Stacks.Groupoids.GroupoidScheme.nonempty_openFiniteSubgroupoid_of_realization`. This file puts
the two together.

## Main results

* `Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation`:
  **Stacks 04S0** in Situation 04RV.

## Implementation notes

The neighbourhood `U'` of Stacks 04RY, the restriction `R' = R|_{U'}` and the affine open `U''`
of `U'` are all produced, so they are existentially quantified in the conclusion; the morphism
`U'' ⟶ U` of the tag is the composite `U'' ⟶ U' ⟶ U`.

In two respects the conclusion is stronger than the tag.  The morphism `U'' ⟶ U'` is an open
immersion, not merely étale — that is how the shrinking is carried out, by Stacks 03JE — and the
quasi-splitting is produced for *every* groupoid scheme realizing the restriction rather than for
one, which is what the uniqueness principle
`AlgebraicGeometry.GroupoidScheme.Restriction.hom_ext` makes possible.  `R|_{U''}` is read both
as the restriction of `R` along the composite, as the tag reads it, and as the restriction of
`R'` to `U''`; the two are identified by
`AlgebraicGeometry.GroupoidScheme.isQuasiSplitAt_of_iteratedRestriction'`.

## References

* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04RY](https://stacks.math.columbia.edu/tag/04RY)
* [Stacks Project, Tag 04S0](https://stacks.math.columbia.edu/tag/04S0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

/-- **Stacks Project, Tag 04S0.**

In the quasi-splitting situation of Stacks 04RV, with `U` affine and with `s` and `t` flat and
locally of finite presentation, there are a separated étale neighbourhood `U' ⟶ U`, a groupoid
scheme `R'` realizing the restriction `R|_{U'}`, an affine open `U'' ⊆ U'` and a point `u''` of
`U''` over `u` with `κ(u) = κ(u'')`, such that `U'' ⟶ U` is étale and `R|_{U''}` is quasi-split
over `u''` — both when `R|_{U''}` is read as the restriction of `R'` to `U''` and when it is
read, as the tag reads it, as the restriction of `R` along the composite `U'' ⟶ U' ⟶ U`.

Stacks 04RY supplies the neighbourhood and a quasi-splitting of the restriction of the
*realization* of the groupoid scheme; the comparison with the groupoid-scheme notion is
`Stacks.Groupoids.GroupoidScheme.nonempty_openFiniteSubgroupoid_of_realization`, and the
shrinking to an affine neighbourhood is
`Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt`. -/
@[stacks 04S0 "ALL ASSERTIONS, in Situation 04RV with U affine and with s and t flat and \
locally of finite presentation: the separated etale neighbourhood U\' -> U, a groupoid scheme \
R\' realizing R|_{U\'}, an AFFINE open U\'\' of U\' with a point u\'\' over u at which the \
residue field map is an ISOMORPHISM, and the QUASI-SPLITTING of R|_{U\'\'} over u\'\' -- all \
PRODUCED. Stacks 04RY is invoked internally as \
exists_quasiSplit_separated_scheme_of_quasiSplittingSituation; its quasi-splitting is \
AlgebraicGeometry.GroupoidInAlgebraicSpaces.QuasiSplitting of the restriction of the \
REALIZATION, and it is converted to the groupoid-scheme notion \
Stacks.Groupoids.GroupoidScheme.QuasiSplitting by \
nonempty_openFiniteSubgroupoid_of_realization, which de-realizes the open finite subgroupoid. \
In two respects the conclusion is STRONGER than the tag: the morphism U\'\' -> U\' is an open \
immersion, not merely etale, and the quasi-splitting is produced for EVERY groupoid scheme \
realizing the restriction. R|_{U\'\'} is read both as the restriction of R along the composite \
U\'\' -> U\' -> U, as the tag reads it, and as the restriction of R\' to U\'\'. Beyond \
Situation 04RV the only requirements are that the big fppf site contain the base, object, arrow \
and composable-pair schemes and Spec k(u), this library\'s standing ambient requirement"]
theorem exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation
    (D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u})
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    [IsAffine D.groupoid.objects.left]
    [Flat D.groupoid.source.left] [LocallyOfFinitePresentation D.groupoid.source.left]
    [Flat D.groupoid.target.left] [LocallyOfFinitePresentation D.groupoid.target.left]
    :
    ∃ (U' : Over D.S) (gp : U' ⟶ D.groupoid.objects)
      (R' : AlgebraicGeometry.GroupoidScheme.Restriction D.groupoid gp)
      (U'' : Over D.S) (j : U'' ⟶ R'.groupoid.objects) (u'' : U''.left),
      AlgebraicGeometry.IsSeparated gp.left ∧ Etale gp.left ∧
      IsAffine U''.left ∧ IsOpenImmersion j.left ∧
      Etale (j ≫ R'.hom.mapObjects).left ∧
      (j ≫ R'.hom.mapObjects).left.base u'' = D.u ∧
      IsIso ((j ≫ R'.hom.mapObjects).left.residueFieldMap u'') ∧
      (∀ R'' : AlgebraicGeometry.GroupoidScheme.Restriction R'.groupoid j,
        IsQuasiSplitAt R''.groupoid ((eqToHom R''.objects_eq.symm).left.base u'')) ∧
      ∀ R''' : AlgebraicGeometry.GroupoidScheme.Restriction D.groupoid
          (j ≫ R'.hom.mapObjects),
        IsQuasiSplitAt R'''.groupoid ((eqToHom R'''.objects_eq.symm).left.base u'') := by
  obtain ⟨E⟩ := nonempty_etaleQuasiSplitting_of_derealization D C hS hU hR hP hK
    inferInstance inferInstance
    (fun hY q U'' g' ε hε R' P => nonempty_openFiniteSubgroupoid_of_realization
      D.groupoid C hS hU hR hP hY q U'' g' ε hε
      (contains_pullback_target_left D.groupoid C hR hY q)
      (contains_pullback_source_left D.groupoid C hR hY q)
      (contains_restrictionArrows_left D.groupoid C hR hY q) R' P)
  obtain ⟨U'', j, u'', haff, hoi, het, hbase, hres, hqs, hqs'⟩ :=
    exists_isAffine_isQuasiSplitAt E
  exact ⟨E.objects, E.projection, E.restriction, U'', j, u'',
    E.projection_isSeparated, E.projection_etale, haff, hoi, het, hbase, hres, hqs, hqs'⟩

end Stacks.Groupoids.GroupoidScheme

end
