module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Groupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.RestrictedSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.SeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The finite part of a groupoid in algebraic spaces as a scheme separated over the objects

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces with `s` and `t` separated, `s` flat and
locally of finite presentation, `t` locally of finite type, and `U` a scheme. The finite part
`U' = (R_s/U, e)_fin`, which carries the groupoid of Stacks 04RU clause (3), is then a scheme,
its projection `U' ⟶ U` is separated as well as étale, and the restriction `R|_{U'}` is
quasi-split at every point of `U'`.

These are three of the four clauses in the conclusion of Stacks 04RY: the upgrade of the
construction of `U'` in the proof of Stacks 04RW by Stacks 04RI and Stacks 04RR, together with
the quasi-splitting which Stacks 04RU clause (3) supplies. The remaining clause, a point `u'` of
`U'` over the chosen point `u` of `U` with `κ(u) = κ(u')`, is not stated here.

## Main results

* `AlgebraicGeometry.Space.exists_finitePartGroupoid_isRepresentable_isSeparated`: the finite
  part of such a groupoid is a scheme whose projection to the object space is separated and
  étale, and the restriction of the groupoid along that projection is quasi-split at every
  point.

## Implementation notes

The hypotheses are imposed on a groupoid in algebraic spaces rather than on the realization of
a groupoid scheme in the situation of Stacks 04RV; that form of the tag, with all four clauses,
is `Stacks.Groupoids.GroupoidScheme.exists_quasiSplit_separated_scheme_of_quasiSplittingSituation`.
Quasi-finiteness of `s` at `e(u)`, the remaining hypothesis of Stacks 04RV, is unused here,
since no clause proved here mentions `u`.

Separatedness is read off the factorisation `objectProjection_spec` of the projection, as an
isomorphism followed by the inclusion of `(R_s/U, e)_fin` into `(R_s/U)_fin` followed by the
projection of the latter: the inclusion is an open immersion by Stacks 04RR part (1), hence
separated, and the projection is separated by Stacks 04RI part (1). That the finite part is a
scheme is Stacks 04RI part (2) for `(R_s/U)_fin`, followed by Stacks 04RR part (4) for the open
subscheme cut out by containment of the unit.

The quasi-splitting comes from
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.nonempty_openFiniteSubgroupoid_restrict`, which
realizes `Z_univ` as an open finite subgroupoid of `R|_{U'}`.

The residue-field point `u'` is the clause left out of this statement. The fibre
`F_u = R ×_{s, U} Spec κ(u)` splits as `Z_u ⊔ Rest` with `Z_u` finite over `κ(u)` and
concentrated at `e(u)`, and `(u, Z_u)` is then a `Spec κ(u)`-valued point of `(R_s/U, e)_fin`
over `u`; stating the clause needs the site hypothesis `C.Contains (Spec κ(u))`, which this
form of the tag does not carry.

## References

* [Stacks Project, Tag 04RI](https://stacks.math.columbia.edu/tag/04RI)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04RW](https://stacks.math.columbia.edu/tag/04RW)
* [Stacks Project, Tag 04RY](https://stacks.math.columbia.edu/tag/04RY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 04RY**, three of the four clauses of its conclusion. For a groupoid in algebraic
spaces whose source and target are separated, whose source is flat and locally of finite
presentation, whose target is locally of finite type and whose object space is a scheme, the
finite part is a scheme, its projection to the object space is separated and étale, and the
restriction along that projection is quasi-split at every point. -/
@[stacks 04RY "the finite part U' = (R_s/U, e)_fin is a scheme, U' ⟶ U is separated and étale,
and R|_{U'} is quasi-split at every point of U'"]
theorem exists_finitePartGroupoid_isRepresentable_isSeparated
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    (hs_sep : IsSeparated C S hS G.source.hom)
    (ht_sep : IsSeparated C S hS G.target.hom)
    (hs_flat : IsFlat C S hS G.source.hom)
    (hs_fp : IsLocallyOfFinitePresentation C S hS G.source.hom)
    (ht_lft : IsLocallyOfFiniteType C S hS G.target.hom)
    (hU : G.objects.obj.IsRepresentable) :
    ∃ F : FinitePartGroupoid G,
      F.groupoid.objects.obj.IsRepresentable ∧
      IsSeparated C S hS F.objectProjection.hom ∧
      IsEtale C S hS F.objectProjection.hom ∧
      ∀ u' : points C S hS
          (GroupoidInAlgebraicSpaces.restrict G F.objectProjection).groupoid.objects.obj,
        GroupoidInAlgebraicSpaces.IsQuasiSplitAt
          (GroupoidInAlgebraicSpaces.restrict G F.objectProjection).groupoid u' := by
  have hs_lft : IsLocallyOfFiniteType C S hS G.source.hom :=
    isLocallyOfFiniteType_of_isLocallyOfFinitePresentation C S hS hs_fp
  obtain ⟨F⟩ := nonempty_finitePartGroupoid G hs_sep ht_sep hs_lft ht_lft
  have hP : (finiteOpenSubspacePresheaf C S hS G.source).toFunctor.IsRepresentable :=
    isRepresentable_finiteOpenSubspacePresheaf_of_isRepresentable C S hS G.source
      hs_sep hs_flat hs_fp hU
  obtain ⟨W, -, e, -, -⟩ := openSubscheme_finitePartWithSection C S hS G.source F.unit
    F.unit_source (Functor.reprX (finiteOpenSubspacePresheaf C S hS G.source).toFunctor)
    (Functor.reprW _)
  have hsub : Nonempty (GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict G F.objectProjection).groupoid) := by
    have hres := GroupoidInAlgebraicSpaces.nonempty_openFiniteSubgroupoid_restrict G
      F.groupoid F.hom.toGroupoidHom F.universalOpen
      (by rw [F.universalOpen_base]; exact F.objectProjection_eq)
      (by rw [F.universalOpen_base]; exact F.objectProjection_etale)
      F.arrows_eq F.source_eq F.arrowProjection_eq
    rwa [F.universalOpen_base] at hres
  refine ⟨F, Functor.IsRepresentable.mk' (e.trans F.objectsEquiv.symm), ?_,
    F.objectProjection_etale,
    fun u' => GroupoidInAlgebraicSpaces.isQuasiSplitAt_of_openFiniteSubgroupoid _
      (Classical.choice hsub) u'⟩
  rw [F.objectProjection_spec]
  exact isSeparated_comp C S hS _ _ (isSeparated_of_isIso C S hS _)
    (isSeparated_comp C S hS _ _
      (isSeparated_of_isImmersion C S hS (isImmersion_of_isOpenImmersion C S hS
        (isOpenImmersion_finitePartWithSection C S hS G.source F.unit F.unit_source)))
      (isSeparated_baseMap_finiteOpenSubspacePresheaf C S hS G.source hs_sep hs_flat hs_fp))

end AlgebraicGeometry.Space

end
