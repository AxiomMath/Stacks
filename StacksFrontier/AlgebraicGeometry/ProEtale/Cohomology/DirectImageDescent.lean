module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ZariskiLocality
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange

/-!
# Descent of the direct-image counit along a cover of the target

Let `f : T ⟶ S` be a morphism in a chosen big pro-étale site. Full faithfulness of the direct
image on small pro-étale sheaves of sets along `f` is *local on the target*: it holds as soon as
it holds over the members of a family of objects covering the final object of the small
pro-étale site of `S`, in particular over the members of a Zariski open cover of `S`, since the
inclusion of a Zariski open is weakly étale.

Concretely, the base change along `f` of such a family covers the final object of the small
pro-étale site of `T`, and the counit of the direct-image adjunction is a natural transformation
of sheaves on that site, so its invertibility is detected over the base-changed family.

## Main results

* `AlgebraicGeometry.ProEtale.nonempty_hom_smallProetaleBaseChange_smallIdentity`: the base
  change of the final object of the small pro-étale site of `S` is weakly final in the small
  pro-étale site of `T`.
* `AlgebraicGeometry.ProEtale.coversTop_smallProetaleBaseChange`: base change along `f` carries
  a family covering the final object of the small pro-étale site of `S` to a family covering the
  final object of the small pro-étale site of `T`.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop`: the counit of
  the direct-image adjunction along `f` is a natural isomorphism as soon as, over each
  base-changed member of a covering family of the target, every component is bijective on
  sections.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_pushforward_fullyFaithful_of_coversTop`:
  consequently the direct image along `f` is fully faithful.

## What this supplies for Stacks 09AA, and what it does not

Stacks 09AA asserts, for a closed immersion `i : Z ⟶ X`, that `i_*` on small pro-étale sheaves
of sets is fully faithful, equivalently that the counit `i^{-1} i_* ⟹ id` is invertible. The
Stacks proof is in two halves: the equivalence of the two formulations is Sites 04D6, which is
available as `StacksFrontier.CategoryTheory.Sites.Topos.ExactnessOfMorphism`, and the reduction to
the case of affine `X`, which is Stacks 09BL, by *Zariski locality on `X`*. The locality step is
what this file provides: no statement of the source performs it, and it is genuinely
needed, because the fully faithful cocontinuous left adjoint to base change that drives 09BL
(the ind-étale quotient lift of Stacks 097P) is constructed on rings and therefore exists only
when both schemes are affine.

Two things remain between `smallProetaleMorphism_pushforward_fullyFaithful_of_coversTop` and
09AA, and neither is available here, which is why no `stacks` attribute is attached to any
declaration in this file.

1. Stacks 09BL itself, the affine case. It is absent from the library: its proof rests on the
   site of affine ind-étale algebras (Stacks 098X) and the affine ind-étale lift (Stacks 09BK),
   neither of which is formalized, and whose dependency closure contains three results that the
   source leaves unproved.
2. The identification of the local hypothesis of
   `smallProetaleMorphism_counit_isIso_of_coversTop` with the conclusion of 09BL over a member
   `U` of the cover. The hypothesis here is bijectivity of the counit of `f` on sections over
   the objects of the small pro-étale site of `T` lying over `T ×_S U`; 09BL would give
   invertibility of the counit of the base-changed morphism `T ×_S U ⟶ U`. Matching the two
   requires the comparison of the small pro-étale site of a weakly étale `T`-scheme `Y` with the
   localization of the small pro-étale site of `T` at `Y`, together with the resulting
   comparison of the two counits across the base-change square of
   `StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.BaseChangeSquare`. That comparison
   is not in the library either.

So 09AA is *not* yet "09BL plus this file": it is 09BL, plus this file, plus the site
localization comparison of item 2.

## Implementation notes

The counit lives on sheaves on the small pro-étale site of the *source* `T`, so the covering
family that detects it is the base change of the covering family of the target; this is the only
place where the geometry enters, through
`AlgebraicGeometry.ProEtale.smallProetaleBaseChange_isMorphismOfSites`, which makes base change
cover-preserving, and through the explicit weakly final object constructed by
`AlgebraicGeometry.ProEtale.nonempty_hom_smallProetaleBaseChange_smallIdentity`. The locality
criterion itself is sectionwise and contains no reference to a localized site; see
`StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ZariskiLocality`.

The covering family of the target is an arbitrary family covering the final object rather than a
Zariski open cover, which is the generality the proof has and is what makes the statement usable
for the affine covers that 09BL is stated over.

## References

* [Stacks Project, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09BN](https://stacks.math.columbia.edu/tag/09BN)
* [Stacks Project, Tag 04D6](https://stacks.math.columbia.edu/tag/04D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- Every object of the small pro-étale site of `T` admits a morphism to the base change along
`f` of the final object of the small pro-étale site of `S`: the structure morphism of such an
object and its composite with `f` lift through the fibre product. -/
theorem nonempty_hom_smallProetaleBaseChange_smallIdentity
    (Y : SmallProetale B T.obj T.property) :
    Nonempty (Y ⟶ (smallProetaleBaseChange B T S f).obj
      (smallIdentity B S.obj S.property)) := by
  refine ⟨ObjectProperty.homMk ?_⟩
  refine Over.homMk (pullback.lift (Y.obj.hom ≫ f) Y.obj.hom ?_) ?_
  · simp [smallIdentity]
  · exact pullback.lift_snd _ _ _

/-- Base change along `f` carries a family of objects covering the final object of the small
pro-étale site of `S` to a family covering the final object of the small pro-étale site of
`T`. -/
theorem coversTop_smallProetaleBaseChange {ι : Type*}
    {U : ι → SmallProetale B S.obj S.property}
    (hU : (SmallProetale.topology B S.obj S.property).CoversTop U) :
    (SmallProetale.topology B T.obj T.property).CoversTop
      fun i => (smallProetaleBaseChange B T S f).obj (U i) := by
  let hcont : (smallProetaleBaseChange B T S f).IsContinuous
      (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property) :=
    (smallProetaleBaseChange_isMorphismOfSites B T S f).toIsContinuous
  exact coversTop_map_of_coverPreserving (smallProetaleBaseChange B T S f) _ _
    (CoverPreserving.of_isContinuous _ _ _) hU
    (nonempty_hom_smallProetaleBaseChange_smallIdentity B T S f)

/-- **Locality on the target of the direct-image counit.** The counit of the direct-image
adjunction along `f` on small pro-étale sheaves of sets is a natural isomorphism as soon as, for
every sheaf on the small pro-étale site of `T` and every member `U i` of a family covering the
final object of the small pro-étale site of `S`, the corresponding component of the counit is
bijective on the sections over every object of the small pro-étale site of `T` lying over the
base change of `U i`. -/
theorem smallProetaleMorphism_counit_isIso_of_coversTop {ι : Type*}
    {U : ι → SmallProetale B S.obj S.property}
    (hU : (SmallProetale.topology B S.obj S.property).CoversTop U)
    (h : ∀ (F : Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1))) (i : ι)
      (Z : SmallProetale B T.obj T.property),
      (Z ⟶ (smallProetaleBaseChange B T S f).obj (U i)) →
      Function.Bijective
        (((smallProetaleMorphism B T S f).adj.counit.app F).hom.app (op Z))) :
    IsIso (smallProetaleMorphism B T S f).adj.counit :=
  isIso_natTrans_of_bijective_of_coversTop
    (coversTop_smallProetaleBaseChange B T S f hU) _ h

/-- **Locality on the target of full faithfulness of the direct image.** Under the hypothesis of
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop`, the direct image
along `f` on small pro-étale sheaves of sets is fully faithful. -/
theorem smallProetaleMorphism_pushforward_fullyFaithful_of_coversTop {ι : Type*}
    {U : ι → SmallProetale B S.obj S.property}
    (hU : (SmallProetale.topology B S.obj S.property).CoversTop U)
    (h : ∀ (F : Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1))) (i : ι)
      (Z : SmallProetale B T.obj T.property),
      (Z ⟶ (smallProetaleBaseChange B T S f).obj (U i)) →
      Function.Bijective
        (((smallProetaleMorphism B T S f).adj.counit.app F).hom.app (op Z))) :
    Nonempty (smallProetaleMorphism B T S f).pushforward.FullyFaithful := by
  have := smallProetaleMorphism_counit_isIso_of_coversTop B T S f hU h
  exact ⟨(smallProetaleMorphism B T S f).adj.fullyFaithfulROfIsIsoCounit⟩

end AlgebraicGeometry.ProEtale

end
