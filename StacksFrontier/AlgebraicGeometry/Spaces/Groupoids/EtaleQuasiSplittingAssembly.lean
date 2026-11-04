module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleNeighbourhoodDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingEtaleScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingAffineLocalization

/-!
# Assembling the output of Stacks 04RY into a scheme-level étale quasi-splitting

Stacks 04RY produces, in the quasi-splitting situation of Stacks 04RV, an algebraic space `U'`
étale and separated over the object space of the realization of the groupoid scheme, a point of
`U'` over the chosen point with the same residue field, and a quasi-splitting of the restriction
of the *realization* to `U'`.  The consumer of Stacks 04RY in this library,
`Stacks.Groupoids.GroupoidScheme.EtaleQuasiSplitting`, asks instead for a *scheme* `U'` over `S`,
a separated étale morphism of schemes `U' ⟶ U`, the restriction `R|_{U'}` as a groupoid *scheme*,
and a quasi-splitting of that groupoid scheme.

This file assembles the first four of those from the first four of Stacks 04RY: the scheme and
the étale morphism are
`Stacks.Groupoids.GroupoidScheme.exists_etale_scheme_of_isRepresentable`, separatedness is
`Stacks.Groupoids.GroupoidScheme.isSeparated_of_isSeparated_realizationIso`, the restriction is
`AlgebraicGeometry.GroupoidScheme.restrict`, and the point is the fourth clause of Stacks 04RY
read on the scheme produced by the de-realization.  The remaining field, the quasi-splitting, is
supplied by the de-realization of an open finite subgroupoid, which is carried here as the
hypothesis `hderealize` and proved elsewhere.

## Main results

* `Stacks.Groupoids.GroupoidScheme.nonempty_etaleQuasiSplitting_of_derealization`: the output of
  Stacks 04RY, assembled into an étale quasi-splitting, given the de-realization of an open
  finite subgroupoid of a restricted realization.

## Implementation notes

The fourth clause of Stacks 04RY is stated for an arbitrary scheme of the site representing `U'`
and an arbitrary morphism of the site inducing the projection; the de-realization supplies
exactly such a pair, with the comparison isomorphism in the direction
`yoneda.obj X' ≅ U'`, so it is applied to its inverse.

The point of the object scheme of the restriction is the point of the neighbourhood transported
along the equality of object schemes recorded by
`AlgebraicGeometry.GroupoidScheme.Restriction`, and the two assertions about it — that it lies
over the chosen point and that the residue field extension is trivial — are transported with
`Stacks.Groupoids.GroupoidScheme.over_eqToHom_apply_symm` and
`AlgebraicGeometry.Scheme.residueFieldMap_comp`, the transport itself being an isomorphism.

Only the quasi-splitting needs the de-realization; the hypothesis is stated for an arbitrary
realization of the restriction, so that the result applies to
`AlgebraicGeometry.GroupoidScheme.restrict` and to any other.

## References

* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04RY](https://stacks.math.columbia.edu/tag/04RY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

/-- **The output of Stacks 04RY, assembled into a scheme-level étale quasi-splitting**, given the
de-realization of an open finite subgroupoid of a restricted realization. -/
theorem nonempty_etaleQuasiSplitting_of_derealization
    (D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u})
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    (hflat : AlgebraicGeometry.Flat D.groupoid.source.left)
    (hfp : AlgebraicGeometry.LocallyOfFinitePresentation D.groupoid.source.left)
    (hderealize : ∀ {Y : Over D.S} (hY : C.Contains Y.left) (q : Y ⟶ D.groupoid.objects)
      (U' : AlgebraicGeometry.AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects)
      (ε : yoneda.obj (schemeSiteObject C hS hY) ≅ U'.obj),
      ε.hom ≫ g.hom = yoneda.map (schemeSiteMap C hS hY hU q) →
      ∀ (R' : AlgebraicGeometry.GroupoidScheme.Restriction D.groupoid q),
        AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
            (AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrict
              (D.groupoid.realization C hS hU hR hP) g).groupoid →
          Nonempty (OpenFiniteSubgroupoid R'.groupoid)) :
    Nonempty (EtaleQuasiSplitting D.groupoid D.u) := by
  obtain ⟨U', g, hrep, hetale, hsep, v, hv, hqs, hpt⟩ :=
    exists_quasiSplit_separated_scheme_of_quasiSplittingSituation D C hS hU hR hP hK hflat hfp
  obtain ⟨Y, hY, q, ε, hqet, hεg⟩ :=
    exists_etale_scheme_of_isRepresentable D.groupoid C hS hU hR hP U' hrep g hetale
  obtain ⟨u', hu'base, hu'iso⟩ := hpt (schemeSiteObject C hS hY) ε.symm
    (schemeSiteMap C hS hY hU q) hεg.symm
  have hqleft : (AlgebraicGeometry.BigFppfOver.toScheme C D.S hS).map
      (schemeSiteMap C hS hY hU q) = q.left :=
    toScheme_map_schemeSiteMap_eq C hS hY hU q
  rw [hqleft] at hu'base hu'iso
  have hqsep : AlgebraicGeometry.IsSeparated q.left :=
    isSeparated_of_isSeparated_realizationIso D.groupoid C hS hU hR hP hY q U' g ε hεg hsep
  have hback : (eqToHom (AlgebraicGeometry.GroupoidScheme.restrict
        D.groupoid q).objects_eq).left.base
      ((eqToHom (AlgebraicGeometry.GroupoidScheme.restrict
        D.groupoid q).objects_eq.symm).left.base u') = u' :=
    over_eqToHom_apply_symm _ u'
  obtain ⟨P⟩ := hqs
  obtain ⟨Q⟩ := hderealize hY q U' g ε hεg
    (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q) P.toOpenFiniteSubgroupoid
  refine ⟨{ objects := Y
            projection := q
            projection_isSeparated := hqsep
            projection_etale := hqet
            restriction := AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q
            point := (eqToHom
              (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q).objects_eq.symm).left.base
              u'
            point_over := ?_
            residueFieldMap_isIso := ?_
            splitting := Q.toQuasiSplitting _ }⟩
  · rw [(AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q).mapObjects_eq, Over.comp_left,
      Scheme.Hom.comp_apply, hback]
    exact hu'base
  · rw [(AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q).mapObjects_eq, Over.comp_left,
      Scheme.residueFieldMap_comp]
    have h1 : IsIso (q.left.residueFieldMap ((eqToHom
        (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q).objects_eq).left.base
        ((eqToHom (AlgebraicGeometry.GroupoidScheme.restrict
          D.groupoid q).objects_eq.symm).left.base u'))) := by
      rw [hback]
      exact hu'iso
    have hiso : IsIso (eqToHom (AlgebraicGeometry.GroupoidScheme.restrict
        D.groupoid q).objects_eq).left :=
      inferInstanceAs (IsIso ((Over.forget D.S).map (eqToHom
        (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q).objects_eq)))
    have h2 : IsIso ((eqToHom (AlgebraicGeometry.GroupoidScheme.restrict
        D.groupoid q).objects_eq).left.residueFieldMap
        ((eqToHom (AlgebraicGeometry.GroupoidScheme.restrict
          D.groupoid q).objects_eq.symm).left.base u')) := inferInstance
    exact IsIso.comp_isIso' h1 h2

end Stacks.Groupoids.GroupoidScheme

end
