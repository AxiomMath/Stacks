module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.DirectImageDescent
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.SiteLocalization
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation

/-!
# The direct-image counit across a base-change square of small pro-étale sites

Let `f : T ⟶ S` be a morphism in a chosen big pro-étale site and let `U` be an object of the
small pro-étale site of `S`, so that the base change `T ×_S U` of `U` along `f` is an object of
the small pro-étale site of `T` and

```
T ×_S U --g'--> T
   |            |
  f'            f
   v            v
   U    --g-->  S
```

is cartesian with weakly étale horizontal arrows. By
`StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.SiteLocalization`, restriction along `g` and
`g'` is restriction to the localizations of the two small pro-étale sites, and this file compares
the direct-image adjunctions along `f` and along `f'` across the square: direct image along `f`
followed by restriction to `U` is restriction to `T ×_S U` followed by direct image along `f'`,
and consequently the counit along `f`, restricted to the small pro-étale site of `T ×_S U`,
is comparable with the counit along `f'`.

## Main definitions

* `AlgebraicGeometry.ProEtale.smallProetaleRestrict`: restriction of small pro-étale sheaves of
  sets along composition with a weakly étale morphism.
* `AlgebraicGeometry.ProEtale.smallProetaleComposeBaseChangeIso`: the base-change square of site
  functors between small pro-étale sites.
* `AlgebraicGeometry.ProEtale.smallProetaleComposeBaseChangePushforwardIso`: the induced
  comparison of direct images.
* `AlgebraicGeometry.ProEtale.smallProetaleBaseChangeCounitMate`: the Beck–Chevalley comparison
  of inverse images across the square, defined as the mate of the previous isomorphism.

## Main results

* `AlgebraicGeometry.ProEtale.isIso_smallProetaleRestrict_map_counit_app`: if the Beck–Chevalley
  comparison and the counit along `f'` are invertible, then so is the restriction along `g'` of
  every component of the counit along `f`.
* `AlgebraicGeometry.ProEtale.bijective_app_of_isIso_smallProetaleRestrict`: invertibility after
  restriction along the structure morphism of an object `Y` is bijectivity on the sections over
  every object lying over `Y`.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop_of_restrict`: the
  counit along `f` is invertible as soon as its restriction along the base change of every member
  of a covering family of the target is invertible.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop_of_baseChange`: the
  counit along `f` is invertible as soon as, over the members of a covering family of the target,
  the counit of the base-changed morphism and the Beck–Chevalley comparison are invertible.

## References

* [Stacks Project, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u})

section Restrict

variable {Z T : B.Scheme} (j : Z ⟶ T) (hj : WeaklyEtale (B.inclusion.map j))

/-- Restriction of small pro-étale sheaves of sets along composition with a weakly étale
morphism `j : Z ⟶ T`: the sections over an object of the small pro-étale site of `Z` are the
sections over its composite over `T`. Under
`AlgebraicGeometry.ProEtale.smallProetaleLocalizationEquivalence` this is restriction to the
localization of the small pro-étale site of `T` at `j`. -/
def smallProetaleRestrict :
    Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1)) ⥤
      Sheaf (SmallProetale.topology B Z.obj Z.property) (Type (u + 1)) :=
  (smallProetaleCompose B j hj).sheafPushforwardContinuous (Type (u + 1))
    (SmallProetale.topology B Z.obj Z.property)
    (SmallProetale.topology B T.obj T.property)

/-- Restriction acts on a morphism of sheaves by evaluating it on the composites over `T`. -/
theorem smallProetaleRestrict_map_hom_app
    {F G : Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1))} (φ : F ⟶ G)
    (V : SmallProetale B Z.obj Z.property) :
    ((smallProetaleRestrict B j hj).map φ).hom.app (op V) =
      φ.hom.app (op ((smallProetaleCompose B j hj).obj V)) := rfl

end Restrict

section Square

variable {T' T S' S : B.Scheme} (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)
  (hg : WeaklyEtale (B.inclusion.map g)) (hg' : WeaklyEtale (B.inclusion.map g'))

/-- For a cartesian square in a chosen big pro-étale site whose horizontal arrows `g` and `g'`
are weakly étale, composition with `g` followed by base change along `f` is base change along
`f'` followed by composition with `g'`, as functors between small pro-étale sites. -/
def smallProetaleComposeBaseChangeIso (h : IsPullback g' f' f g) :
    smallProetaleCompose B g hg ⋙ smallProetaleBaseChange B T S f ≅
      smallProetaleBaseChange B T' S' f' ⋙ smallProetaleCompose B g' hg' := by
  refine Functor.fullyFaithfulCancelRight
    (SmallProetale.inclusion B T.obj T.property) ?_
  have e1 : (smallProetaleCompose B g hg ⋙ smallProetaleBaseChange B T S f) ⋙
      SmallProetale.inclusion B T.obj T.property =
      SmallProetale.inclusion B S'.obj S'.property ⋙
        (Over.map g ⋙ Over.pullback f) := rfl
  have e2 : (smallProetaleBaseChange B T' S' f' ⋙ smallProetaleCompose B g' hg') ⋙
      SmallProetale.inclusion B T.obj T.property =
      SmallProetale.inclusion B S'.obj S'.property ⋙
        (Over.pullback f' ⋙ Over.map g') := rfl
  exact eqToIso e1 ≪≫
    Functor.isoWhiskerLeft (SmallProetale.inclusion B S'.obj S'.property)
      (overPullbackBaseChangeIso g' f' f g h) ≪≫ eqToIso e2.symm

/-- **Direct image across a base-change square of small pro-étale sites.** For a cartesian
square whose horizontal arrows are weakly étale, direct image along `f` followed by restriction
to the small pro-étale site of `S'` agrees naturally with restriction to the small pro-étale site
of `T'` followed by direct image along `f'`. -/
def smallProetaleComposeBaseChangePushforwardIso (h : IsPullback g' f' f g) :
    (smallProetaleMorphism B T S f).pushforward ⋙ smallProetaleRestrict B g hg ≅
      smallProetaleRestrict B g' hg' ⋙ (smallProetaleMorphism B T' S' f').pushforward := by
  letI : (smallProetaleBaseChange B T S f).IsContinuous
      (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property) :=
    (smallProetaleBaseChange_isMorphismOfSites B T S f).toIsContinuous
  letI : (smallProetaleBaseChange B T' S' f').IsContinuous
      (SmallProetale.topology B S'.obj S'.property)
      (SmallProetale.topology B T'.obj T'.property) :=
    (smallProetaleBaseChange_isMorphismOfSites B T' S' f').toIsContinuous
  letI := Functor.isContinuous_comp (smallProetaleCompose B g hg)
    (smallProetaleBaseChange B T S f)
    (SmallProetale.topology B S'.obj S'.property)
    (SmallProetale.topology B S.obj S.property)
    (SmallProetale.topology B T.obj T.property)
  letI := Functor.isContinuous_comp (smallProetaleBaseChange B T' S' f')
    (smallProetaleCompose B g' hg')
    (SmallProetale.topology B S'.obj S'.property)
    (SmallProetale.topology B T'.obj T'.property)
    (SmallProetale.topology B T.obj T.property)
  calc (smallProetaleMorphism B T S f).pushforward ⋙ smallProetaleRestrict B g hg
      ≅ (smallProetaleCompose B g hg ⋙
          smallProetaleBaseChange B T S f).sheafPushforwardContinuous (Type (u + 1))
          (SmallProetale.topology B S'.obj S'.property)
          (SmallProetale.topology B T.obj T.property) :=
        Functor.sheafPushforwardContinuousComp (smallProetaleCompose B g hg)
          (smallProetaleBaseChange B T S f) (Type (u + 1))
          (SmallProetale.topology B S'.obj S'.property)
          (SmallProetale.topology B S.obj S.property)
          (SmallProetale.topology B T.obj T.property)
    _ ≅ (smallProetaleBaseChange B T' S' f' ⋙
          smallProetaleCompose B g' hg').sheafPushforwardContinuous (Type (u + 1))
          (SmallProetale.topology B S'.obj S'.property)
          (SmallProetale.topology B T.obj T.property) :=
        Functor.sheafPushforwardContinuousIso
          (smallProetaleComposeBaseChangeIso B g' f' f g hg hg' h) (Type (u + 1))
          (SmallProetale.topology B S'.obj S'.property)
          (SmallProetale.topology B T.obj T.property)
    _ ≅ smallProetaleRestrict B g' hg' ⋙ (smallProetaleMorphism B T' S' f').pushforward :=
        (Functor.sheafPushforwardContinuousComp (smallProetaleBaseChange B T' S' f')
          (smallProetaleCompose B g' hg') (Type (u + 1))
          (SmallProetale.topology B S'.obj S'.property)
          (SmallProetale.topology B T'.obj T'.property)
          (SmallProetale.topology B T.obj T.property)).symm

/-- The Beck–Chevalley comparison of inverse images across the square: the mate, with respect to
the two direct-image adjunctions, of
`AlgebraicGeometry.ProEtale.smallProetaleComposeBaseChangePushforwardIso`. -/
def smallProetaleBaseChangeCounitMate (h : IsPullback g' f' f g) :
    smallProetaleRestrict B g hg ⋙ (smallProetaleMorphism B T' S' f').inverseImage ⟶
      (smallProetaleMorphism B T S f).inverseImage ⋙ smallProetaleRestrict B g' hg' :=
  (mateEquiv (smallProetaleMorphism B T S f).adj
      (smallProetaleMorphism B T' S' f').adj).symm
    (smallProetaleComposeBaseChangePushforwardIso B g' f' f g hg hg' h).hom

/-- If the Beck–Chevalley comparison of inverse images across the square is invertible and the
counit of the direct-image adjunction along `f'` is invertible, then the restriction to the small
pro-étale site of `T'` of every component of the counit along `f` is invertible. -/
theorem isIso_smallProetaleRestrict_map_counit_app (h : IsPullback g' f' f g)
    (hmate : IsIso (smallProetaleBaseChangeCounitMate B g' f' f g hg hg' h))
    (hcounit : IsIso (smallProetaleMorphism B T' S' f').adj.counit)
    (F : Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1))) :
    IsIso ((smallProetaleRestrict B g' hg').map
      ((smallProetaleMorphism B T S f).adj.counit.app F)) := by
  let β := smallProetaleComposeBaseChangePushforwardIso B g' f' f g hg hg' h
  let α := smallProetaleBaseChangeCounitMate B g' f' f g hg hg' h
  have key := mateEquiv_counit_symm (smallProetaleMorphism B T S f).adj
    (smallProetaleMorphism B T' S' f').adj β.hom F
  have := NatIso.isIso_app_of_isIso α (((smallProetaleMorphism B T S f).pushforward).obj F)
  have : IsIso (α.app _ ≫
      (smallProetaleRestrict B g' hg').map ((smallProetaleMorphism B T S f).adj.counit.app F)) := by
    change IsIso (((mateEquiv _ _).symm β.hom).app _ ≫ _)
    rw [← key]
    infer_instance
  exact IsIso.of_isIso_comp_left (α.app _) _

end Square

/-- Sectionwise form of invertibility after restriction: if a morphism of small pro-étale sheaves
of sets on `T` becomes invertible after restriction along the structure morphism of an object `Y`
of the small pro-étale site of `T`, then it is bijective on the sections over every object
admitting a morphism to `Y`. -/
theorem bijective_app_of_isIso_smallProetaleRestrict (T : B.Scheme)
    (Y : SmallProetale B T.obj T.property)
    {F G : Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1))} (φ : F ⟶ G)
    (h : IsIso ((smallProetaleRestrict B Y.obj.hom Y.property).map φ))
    {W : SmallProetale B T.obj T.property} (q : W ⟶ Y) :
    Function.Bijective (φ.hom.app (op W)) := by
  obtain ⟨V, ⟨e⟩⟩ := exists_iso_smallProetaleCompose_obj B T Y q
  have : IsIso (((smallProetaleRestrict B Y.obj.hom Y.property).map φ).hom.app (op V)) :=
    inferInstance
  have : IsIso (φ.hom.app (op W) ≫ G.obj.map e.hom.op) := by
    rw [← φ.hom.naturality e.hom.op]
    exact IsIso.comp_isIso' (F.obj.mapIso e.op).isIso_hom this
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (IsIso.of_isIso_comp_right _ (G.obj.map e.hom.op))

/-- **Locality of the direct-image counit, in restricted form.** The counit of the direct-image
adjunction along `f` on small pro-étale sheaves of sets is invertible as soon as, for every sheaf
and every member `U i` of a family covering the final object of the small pro-étale site of `S`,
its restriction along the base change of `U i` is invertible. -/
theorem smallProetaleMorphism_counit_isIso_of_coversTop_of_restrict
    (T S : B.Scheme) (f : T ⟶ S) {ι : Type*}
    {U : ι → SmallProetale B S.obj S.property}
    (hU : (SmallProetale.topology B S.obj S.property).CoversTop U)
    (h : ∀ (F : Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1))) (i : ι),
      IsIso ((smallProetaleRestrict B ((smallProetaleBaseChange B T S f).obj (U i)).obj.hom
        ((smallProetaleBaseChange B T S f).obj (U i)).property).map
        ((smallProetaleMorphism B T S f).adj.counit.app F))) :
    IsIso (smallProetaleMorphism B T S f).adj.counit :=
  smallProetaleMorphism_counit_isIso_of_coversTop B T S f hU fun F i _ q =>
    bijective_app_of_isIso_smallProetaleRestrict B T
      ((smallProetaleBaseChange B T S f).obj (U i)) _ (h F i) q

/-- The base-change square attached to a member of a covering family: the base change of `U`
along `f`, its first projection, `f` and the structure morphism of `U` form a cartesian
square. -/
theorem isPullback_smallProetaleBaseChange (T S : B.Scheme) (f : T ⟶ S)
    (U : SmallProetale B S.obj S.property) :
    IsPullback ((smallProetaleBaseChange B T S f).obj U).obj.hom
      (pullback.fst U.obj.hom f) f U.obj.hom :=
  (IsPullback.of_hasPullback U.obj.hom f).flip

/-- **Locality of the direct-image counit, via base change.** The counit of the direct-image
adjunction along `f` on small pro-étale sheaves of sets is invertible as soon as, over the
members `U i` of a family covering the final object of the small pro-étale site of `S`, the
counit of the direct-image adjunction along the base-changed morphism is invertible and the
Beck–Chevalley comparison of inverse images across the base-change square is invertible. -/
theorem smallProetaleMorphism_counit_isIso_of_coversTop_of_baseChange
    (T S : B.Scheme) (f : T ⟶ S) {ι : Type*}
    {U : ι → SmallProetale B S.obj S.property}
    (hU : (SmallProetale.topology B S.obj S.property).CoversTop U)
    (hmate : ∀ i, IsIso (smallProetaleBaseChangeCounitMate B
      ((smallProetaleBaseChange B T S f).obj (U i)).obj.hom
      (pullback.fst (U i).obj.hom f) f (U i).obj.hom (U i).property
      ((smallProetaleBaseChange B T S f).obj (U i)).property
      (isPullback_smallProetaleBaseChange B T S f (U i))))
    (hcounit : ∀ i, IsIso (smallProetaleMorphism B
      ((smallProetaleBaseChange B T S f).obj (U i)).obj.left (U i).obj.left
      (pullback.fst (U i).obj.hom f)).adj.counit) :
    IsIso (smallProetaleMorphism B T S f).adj.counit :=
  smallProetaleMorphism_counit_isIso_of_coversTop_of_restrict B T S f hU fun F i =>
    isIso_smallProetaleRestrict_map_counit_app B
      ((smallProetaleBaseChange B T S f).obj (U i)).obj.hom
      (pullback.fst (U i).obj.hom f) f (U i).obj.hom (U i).property
      ((smallProetaleBaseChange B T S f).obj (U i)).property
      (isPullback_smallProetaleBaseChange B T S f (U i)) (hmate i) (hcounit i) F

end AlgebraicGeometry.ProEtale

end
