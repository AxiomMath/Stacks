module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.FppfQuotient
public import StacksFrontier.AlgebraicGeometry.Groupoids.OpenIdentityEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize

/-!
# The quotient of a relation whose identity is an open immersion

Let `(U, R, s, t, c)` be a groupoid scheme over `S` which is an equivalence relation, with `U`
contained in a big fppf site `B`, with flat and locally finitely presented source map, and whose
identity `e : U ⟶ R` is an open immersion. Then `s` and `t` are étale, so the relation is an
étale equivalence relation between objects of the big fppf site of `S`, and
[Stacks, Tag 02WW] makes its quotient sheaf an algebraic space with `U` for a surjective étale
atlas.

This is the final case of the proof of [Stacks, Tag 04S6]: the quasi-splitting and
finite-locally-free-division steps of the source reduce the general flat, locally finitely
presented equivalence relation to one with open identity, and this is what closes it.

## Main results

* `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_of_isOpenImmersion_identity`: the relation
  of such a groupoid is an étale equivalence relation between objects of the site.
* `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion_identity`: its
  quotient sheaf is an algebraic space.
* `AlgebraicGeometry.Space.exists_atlas_quotientSheaf_of_isOpenImmersion_identity`: the object
  scheme itself is a surjective étale atlas of the quotient, so the atlas can be chosen without
  increasing the size.

## Implementation notes

The relation of the groupoid is `AlgebraicGeometry.groupoidPreRelation`, a pre-relation between
objects of `CategoryTheory.Over S`, whereas `AlgebraicGeometry.Space.relation` is the
pre-relation determined by a pair of morphisms of the *site* `BigFppfOver B S hS`. The two agree
on the nose once the object and arrow schemes are read as objects of the site: the arrow scheme
is contained in the site because the relation is a monomorphism into `U ×_S U`
(`Stacks.Groupoids.contains_left_of_mono`), and the two source and target maps are then the same
morphisms. The identification is definitional, so it is `rfl`, and the étale
equivalence-relation instance of Stacks 02WS can be transported to it by rewriting the target and
source projections of a `CategoryTheory.Limits.prod.lift`.

Only flatness and local finite presentation of the *source* map are assumed: the target map is
the source map precomposed with the inverse, which is an isomorphism once the target and source
are jointly monomorphic.

## References

* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

/-- The target and the source of a groupoid scheme whose pre-relation is an equivalence relation
are an equivalence relation. -/
theorem isEquivalenceRelation_target_source {S : Scheme.{u}} (G : GroupoidScheme S)
    (hrel : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source) :
    IsEquivalenceRelation G.target G.source := by
  simpa only [groupoidPreRelation, PreRelation.target, PreRelation.source, prod.lift_fst,
    prod.lift_snd] using hrel

/-- The arrow scheme of an equivalence-relation groupoid on an object of the site is contained in
the site: its pre-relation is a monomorphism into `U ×_S U`. -/
theorem contains_arrows_left (B : BigFppfSite.{u}) {S : Scheme.{u}} (G : GroupoidScheme S)
    (hU : B.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source) :
    B.Contains G.arrows.left :=
  have : Mono (groupoidPreRelation G) :=
    ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation (groupoidPreRelation G)).mp
      hrel).1
  contains_left_of_mono B (groupoidPreRelation G) hU

/-- The arrow scheme of the groupoid, read as an object of the big fppf site of `S`. -/
abbrev siteArrows (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source) : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk G.arrows.hom :
    B.obj (contains_arrows_left B G hU hrel) ⟶ B.obj hS)

/-- The source map of the groupoid, read as a morphism of the big fppf site of `S`. -/
abbrev siteSource (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source) :
    siteArrows B S hS G hU hrel ⟶ GroupoidScheme.objectsSite B S hS G hU :=
  Over.homMk (ObjectProperty.homMk G.source.left) (by ext; exact G.source.w)

/-- The target map of the groupoid, read as a morphism of the big fppf site of `S`. -/
abbrev siteTarget (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source) :
    siteArrows B S hS G hU hrel ⟶ GroupoidScheme.objectsSite B S hS G hU :=
  Over.homMk (ObjectProperty.homMk G.target.left) (by ext; exact G.target.w)

/-- Reading the object and arrow schemes of the groupoid as objects of the site recovers its
pre-relation on the nose. -/
theorem relation_siteSource_siteTarget (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source) :
    relation B S hS (siteSource B S hS G hU hrel) (siteTarget B S hS G hU hrel) =
      groupoidPreRelation G := rfl

/-- **The relation of an equivalence-relation groupoid whose identity is an open immersion and
whose source is flat and locally of finite presentation is an étale equivalence relation**
between objects of the big fppf site of `S`. -/
theorem isEtaleEquivalenceRelation_of_isOpenImmersion_identity (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source)
    [_root_.AlgebraicGeometry.IsOpenImmersion G.identity.left] [Flat G.source.left]
    [LocallyOfFinitePresentation G.source.left] :
    IsEtaleEquivalenceRelation
      (relation B S hS (siteSource B S hS G hU hrel) (siteTarget B S hS G hU hrel)) := by
  have : IsEquivalenceRelation G.target G.source := isEquivalenceRelation_target_source G hrel
  have : JointlyMono₂ G.target G.source := G.jointlyMono_of_isEquivalenceRelation
  have hs : Etale G.source.left := G.etale_source_of_isOpenImmersion_identity
  have ht : Etale G.target.left := G.etale_target_of_isOpenImmersion_identity
  have hj := relation_siteSource_siteTarget B S hS G hU hrel
  have hjs : (relation B S hS (siteSource B S hS G hU hrel)
      (siteTarget B S hS G hU hrel)).source = G.source := prod.lift_snd _ _
  have hjt : (relation B S hS (siteSource B S hS G hU hrel)
      (siteTarget B S hS G hU hrel)).target = G.target := prod.lift_fst _ _
  exact { isEquivalenceRelation := hj ▸ hrel
          etale_source := hjs ▸ hs
          etale_target := hjt ▸ ht }

/-- **Stacks 04S6, the case of an open identity.** The quotient sheaf of an equivalence-relation
groupoid scheme on an object of the big fppf site of `S`, with flat and locally finitely
presented source map and with open-immersion identity, is an algebraic space over `S`. -/
theorem isAlgebraicSpace_quotientSheaf_of_isOpenImmersion_identity (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source)
    [_root_.AlgebraicGeometry.IsOpenImmersion G.identity.left] [Flat G.source.left]
    [LocallyOfFinitePresentation G.source.left] :
    IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (groupoidPreRelation G)).obj := by
  have := isEtaleEquivalenceRelation_of_isOpenImmersion_identity B S hS G hU hrel
  exact relation_siteSource_siteTarget B S hS G hU hrel ▸
    isAlgebraicSpace_quotient_unconditional B S hS (siteSource B S hS G hU hrel)
      (siteTarget B S hS G hU hrel)

/-- **The object scheme is a surjective étale atlas of the quotient** in the open-identity case,
so an atlas can be chosen whose size does not exceed that of the object scheme. -/
theorem exists_atlas_quotientSheaf_of_isOpenImmersion_identity (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source)
    [_root_.AlgebraicGeometry.IsOpenImmersion G.identity.left] [Flat G.source.left]
    [LocallyOfFinitePresentation G.source.left] :
    ∃ (W : BigFppfOver B S hS) (a : yoneda.obj W ⟶
        (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (groupoidPreRelation G)).obj),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj W).size ≤ G.objects.left.size := by
  have := isEtaleEquivalenceRelation_of_isOpenImmersion_identity B S hS G hU hrel
  rw [← relation_siteSource_siteTarget B S hS G hU hrel]
  exact ⟨GroupoidScheme.objectsSite B S hS G hU,
    quotientMap B S hS (siteSource B S hS G hU hrel) (siteTarget B S hS G hU hrel),
    quotientMap_surjective_unconditional B S hS (siteSource B S hS G hU hrel)
      (siteTarget B S hS G hU hrel),
    quotientMap_etale_unconditional B S hS (siteSource B S hS G hU hrel)
      (siteTarget B S hS G hU hrel), le_rfl⟩

end AlgebraicGeometry.Space

end
