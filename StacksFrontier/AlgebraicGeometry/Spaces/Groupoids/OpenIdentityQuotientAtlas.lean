module

public import StacksFrontier.AlgebraicGeometry.Groupoids.EtaleOfOpenIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RefinementSiteData
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional

/-!
# The quotient of a groupoid scheme with open identity section

Let `(U, R, s, t, c, e, i)` be a groupoid scheme over `S` whose target and source form an
internal equivalence relation, whose source is flat and locally of finite presentation, and
whose identity section is an open immersion.  Then the fppf quotient sheaf `U/R` is an algebraic
space over `S` and `U` *itself* is a surjective étale atlas of it.

Both halves are read off [Stacks, Tag 02WW]: the identity section being an open immersion makes
`s` and `t` étale (`Stacks.Groupoids.GroupoidScheme.etale_source_of_isOpenImmersion_identity`),
and the quotient of an étale equivalence relation on an object of the site is an algebraic space
with surjective étale quotient map.  The arrow scheme lies in the site automatically, the
relation being a monomorphism into `U ×_S U`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpaceAtlasSizeLE_quotientSheaf_of_isOpenImmersion_identity`:
  the quotient sheaf is an algebraic space with an atlas of size at most that of the object
  scheme.

## Implementation notes

The bound on the atlas is `size U`: the atlas *is* `U`.  The pair `(s, t)` of morphisms of
objects of the site whose pre-relation is `AlgebraicGeometry.groupoidPreRelation G` is built from
the structure morphisms of the groupoid, and its comparison with
`AlgebraicGeometry.Space.relation` is definitional.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04R9](https://stacks.math.columbia.edu/tag/04R9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

/-- **The quotient of a groupoid scheme with open identity section is an algebraic space with
atlas the object scheme.**

If the target and source of a groupoid scheme over `S` form an internal equivalence relation,
the source is flat and locally of finite presentation, and the identity section is an open
immersion, then the fppf quotient sheaf is an algebraic space over `S` with a surjective étale
atlas by an object of the site whose underlying scheme is the object scheme itself. -/
theorem isAlgebraicSpaceAtlasSizeLE_quotientSheaf_of_isOpenImmersion_identity
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left)
    [CategoryTheory.IsEquivalenceRelation G.target G.source]
    [_root_.AlgebraicGeometry.IsOpenImmersion G.identity.left] [Flat G.source.left]
    [LocallyOfFinitePresentation G.source.left] :
    IsAlgebraicSpaceAtlasSizeLE B S hS
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (groupoidPreRelation G)).obj G.objects.left.size := by
  have hR : B.Contains G.arrows.left := B.contains_arrows_of_isEquivalenceRelation G hU
  set U : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk G.objects.hom : B.obj hU ⟶ B.obj hS)
  set Rs : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk G.arrows.hom : B.obj hR ⟶ B.obj hS)
  set sm : Rs ⟶ U := Over.homMk (ObjectProperty.homMk G.source.left) (by ext; exact G.source.w)
  set tm : Rs ⟶ U := Over.homMk (ObjectProperty.homMk G.target.left) (by ext; exact G.target.w)
  have hjt : (relation B S hS sm tm).target = G.target := prod.lift_fst _ _
  have hjs : (relation B S hS sm tm).source = G.source := prod.lift_snd _ _
  have hrel : CategoryTheory.IsEquivalenceRelation (relation B S hS sm tm).target
      (relation B S hS sm tm).source := by
    have hG : CategoryTheory.IsEquivalenceRelation G.target G.source := inferInstance
    rwa [← hjt, ← hjs] at hG
  have _ : IsEtaleEquivalenceRelation (relation B S hS sm tm) :=
    { isEquivalenceRelation := hrel
      etale_source := by rw [hjs]; exact G.etale_source_of_isOpenImmersion_identity
      etale_target := by rw [hjt]; exact G.etale_target_of_isOpenImmersion_identity }
  exact ⟨isAlgebraicSpace_quotient_unconditional B S hS sm tm, U, quotientMap B S hS sm tm,
    quotientMap_surjective_unconditional B S hS sm tm, quotientMap_etale_unconditional B S hS sm tm,
    le_rfl⟩

end AlgebraicGeometry.Space

end
