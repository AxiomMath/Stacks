module

public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcomposeBaseChangeAdjunction

/-!
# The counit of the post-composition adjunction is the base-change projection

Let `B` be a big étale site containing a scheme `X`, and let `U` be an object of the small
étale site of `X`.  `AlgebraicGeometry.SmallEtale.postcomposeBaseChangeAdjunction` is the slice
adjunction `CategoryTheory.Over.mapPullbackAdj p_U` restricted to the étale objects, so its
counit is the slice adjunction's counit — the first projection of the fibre product — once the
étale condition is forgotten.

This is the *characterisation* the derived identifications of
`AlgebraicGeometry.SmallEtale.baseChangeIsoStarCompInverse` and
`AlgebraicGeometry.SmallEtale.baseChangeLocalizationIsoStar` need.  Those are produced by
`CategoryTheory.Adjunction.rightAdjointUniq`, which has no formula:  a comparison of right
adjoints is pinned only by what it does to the counits, through
`CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`.  Without the identity below that
lemma cannot be used, because the counit it produces is a morphism of the small étale site about
which nothing is known.

## Main results

* `AlgebraicGeometry.SmallEtale.inclusion_map_postcomposeBaseChangeAdjunction_counit_app`: the
  counit of `AlgebraicGeometry.SmallEtale.postcomposeBaseChangeAdjunction`, pushed into the big
  étale category over `X`, is the counit of `CategoryTheory.Over.mapPullbackAdj p_U`.
* `AlgebraicGeometry.SmallEtale.baseChangeLocalizationIsoStar_inv_app_left_comp_counit`: the
  comparison `U ⨯ W ⟶ U ×_X W` of
  `AlgebraicGeometry.SmallEtale.baseChangeLocalizationIsoStar`, followed by that counit, is
  `prod.snd`.

## Implementation notes

**This replaces a `private` declaration.**
`AlgebraicGeometry.Stack.smallEtalePostcomposeAdjunction_counit_map`, in
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/SmallEtaleRestrictionEtaleIso.lean`, is the same
statement for the `private` adjunction of that file, which is
`AlgebraicGeometry.SmallEtale.postcomposeBaseChangeAdjunction` at `U := ⟨Over.mk j, hj⟩` — the
étale `j : U ⟶ V` of that file is exactly the structure morphism of an object of the small étale
site of the target.  Both are special cases of the statement below;  it is
stated here, publicly, for the library's adjunction, rather than by dropping the `private` modifier
there, precisely so that no second public declaration of the same content is created.

**No hypothesis is added.**  Nothing is assumed of `X`, of `B`, or of `U` beyond its being an
object of the small étale site of `X`;  in particular the structure morphism of `U` is not
assumed to be an open immersion or a monomorphism.

## References

* [Stacks Project, Tag 03PM](https://stacks.math.columbia.edu/tag/03PM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- **The counit of the post-composition adjunction is the base-change projection.**  The counit
of `AlgebraicGeometry.SmallEtale.postcomposeBaseChangeAdjunction` at an object `W` of the small
étale site of `X`, read in the big étale category over `X`, is the counit
`U ×_X W ⟶ W` of the slice adjunction `CategoryTheory.Over.mapPullbackAdj p_U`.

The adjunction *is* that slice adjunction restricted along the two fully faithful inclusions, and
`CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app` computes the counit of a
restricted adjunction;  the two comparison isomorphisms are `eqToIso`s of equalities of functors,
so both correction terms are identities. -/
public theorem inclusion_map_postcomposeBaseChangeAdjunction_counit_app
    (W : SmallEtale B X hX) :
    (inclusion B X hX).map ((postcomposeBaseChangeAdjunction B X hX U).counit.app W) =
      (Over.mapPullbackAdj U.obj.hom).counit.app ((inclusion B X hX).obj W) := by
  change (inclusion B X hX).map
      (((Over.mapPullbackAdj U.obj.hom).restrictFullyFaithful
        (ObjectProperty.fullyFaithfulι
          (BigEtaleOver.IsEtaleOver B U.obj.left.obj U.obj.left.property))
        (ObjectProperty.fullyFaithfulι (BigEtaleOver.IsEtaleOver B X hX))
        (eqToIso rfl)
        (eqToIso (smallEtaleBaseChange_comp_inclusion B U.obj.hom).symm)).counit.app W) = _
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  simp [Over.mapPullbackAdj_counit_app]
  rfl

/- The statement below composes a morphism of the slice at `U`, read through
`CategoryTheory.Over.Hom.left`, with a morphism of the small étale site; the two spellings of
its source —
`((smallEtaleBaseChange B p_U ⋙ (localizationEquivalence B X hX U).functor).obj W).left` and
`((smallEtaleBaseChange B p_U ⋙ postcompose B X hX U).obj W)` — are identified only by unfolding
the equivalence, which the `implicit` transparency level does not do. The goals are then not
type-correct at that level and `rw` and `Trans` synthesis decline to act on them; naming the
unfolding chain here is what lets the ordinary tactics see through it. -/
attribute [local implicit_reducible] AlgebraicGeometry.SmallEtale.postcompose
  AlgebraicGeometry.SmallEtale.localization
  AlgebraicGeometry.SmallEtale.localizationEquivalence CategoryTheory.Over.lift in
/-- **The inverse of `AlgebraicGeometry.SmallEtale.baseChangeLocalizationIsoStar`, followed by
the base-change projection, is the second projection.**  At an object `W` of the small étale site
of `X`, the comparison `U ⨯ W ⟶ U ×_X W` of the binary product with the fibre product, followed
by the counit `U ×_X W ⟶ W` of
`AlgebraicGeometry.SmallEtale.postcomposeBaseChangeAdjunction`, is `prod.snd`.

This is the counit characterisation of a comparison of right adjoints.  Both
`AlgebraicGeometry.SmallEtale.baseChangeIsoStarCompInverse` and the derived
`AlgebraicGeometry.SmallEtale.baseChangeLocalizationIsoStar` are produced by
`CategoryTheory.Adjunction.rightAdjointUniq`, for which
`CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit` says exactly this:  the comparison
composed with one adjunction's counit is the other's.  The counit of
`AlgebraicGeometry.SmallEtale.postcomposeStarAdjunction` is the counit of
`CategoryTheory.Over.forgetAdjStar`, namely `prod.snd`, up to the counit of the localization
equivalence, which cancels against the one in
`AlgebraicGeometry.SmallEtale.baseChangeLocalizationIsoStar`.

Nothing is assumed of `X`, of `B` or of `U`. -/
public theorem baseChangeLocalizationIsoStar_inv_app_left_comp_counit (W : SmallEtale B X hX) :
    ((baseChangeLocalizationIsoStar B X hX U).inv.app W).left ≫
        (postcomposeBaseChangeAdjunction B X hX U).counit.app W =
      Limits.prod.snd := by
  have h1 : (baseChangeLocalizationIsoStar B X hX U).inv.app W =
      (localizationEquivalence B X hX U).counitIso.inv.app ((Over.star U).obj W) ≫
        (localizationEquivalence B X hX U).functor.map
          ((baseChangeIsoStarCompInverse B X hX U).inv.app W) := by
    simp [baseChangeLocalizationIsoStar]
  have h2 : Over.Hom.left ((localizationEquivalence B X hX U).functor.map
        ((baseChangeIsoStarCompInverse B X hX U).inv.app W)) ≫
      (postcomposeBaseChangeAdjunction B X hX U).counit.app W =
      (postcomposeStarAdjunction B X hX U).counit.app W := by
    rw [baseChangeIsoStarCompInverse, Adjunction.rightAdjointUniq_inv_app]
    exact Adjunction.rightAdjointUniq_hom_app_counit (postcomposeStarAdjunction B X hX U)
      (postcomposeBaseChangeAdjunction B X hX U) W
  have h3 : Over.Hom.left
        ((localizationEquivalence B X hX U).counitIso.inv.app ((Over.star U).obj W)) ≫
      (postcomposeStarAdjunction B X hX U).counit.app W = Limits.prod.snd := by
    have hc : Over.Hom.left
          ((localizationEquivalence B X hX U).counitIso.inv.app ((Over.star U).obj W)) ≫
        Over.Hom.left
          ((localizationEquivalence B X hX U).counit.app ((Over.star U).obj W)) = 𝟙 _ :=
      Over.inv_left_hom_left _
    have hfin : Over.Hom.left
          ((localizationEquivalence B X hX U).counitIso.inv.app ((Over.star U).obj W)) ≫
        Over.Hom.left
          ((localizationEquivalence B X hX U).counit.app ((Over.star U).obj W)) ≫
            (Over.forgetAdjStar U).counit.app W = (Over.forgetAdjStar U).counit.app W := by
      rw [← Category.assoc, hc, Category.id_comp]
    simpa [postcomposeStarAdjunction, Over.forgetAdjStar_counit_app, eqToHom_refl, -cancelIso]
      using hfin
  have h4 : (Over.Hom.left
        ((localizationEquivalence B X hX U).counitIso.inv.app ((Over.star U).obj W)) ≫
      Over.Hom.left ((localizationEquivalence B X hX U).functor.map
        ((baseChangeIsoStarCompInverse B X hX U).inv.app W))) ≫
      (postcomposeBaseChangeAdjunction B X hX U).counit.app W = Limits.prod.snd := by
    rw [Category.assoc, h2]
    exact h3
  rw [h1, Over.comp_left]
  exact h4

end AlgebraicGeometry.SmallEtale

end
