module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.CounitComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.MateCoherence

/-!
# Beck–Chevalley for small pro-étale sites: restriction to a localization

Let `f : T ⟶ S` be a morphism in a chosen big pro-étale site and let

```
T' --g'--> T
|          |
f'         f
v          v
S' --g-->  S
```

be cartesian with `g` and `g'` weakly étale. `AlgebraicGeometry.ProEtale.CounitComparison`
reduces Stacks 09AA to Stacks 09BL together with invertibility of
`AlgebraicGeometry.ProEtale.smallProetaleBaseChangeCounitMate`, the Beck–Chevalley comparison of
*inverse* images across this square. That comparison is defined as a mate, and a mate of an
isomorphism need not be an isomorphism, so its invertibility is not formal. This file proves it.

The input is that restriction along a weakly étale morphism `j` — which by
`AlgebraicGeometry.ProEtale.SiteLocalization` is restriction to a localization of the small
pro-étale site — is itself a left adjoint, namely a left adjoint of the direct image along `j`:
this is `AlgebraicGeometry.ProEtale.smallProetaleRestrict_adj`, and it identifies restriction with
the inverse image of the geometric morphism attached to `j`
(`AlgebraicGeometry.ProEtale.smallProetaleRestrictIsoInverseImage`). All four functors in the
square of topoi are then left adjoints, so `CategoryTheory.iterated_mateEquiv_conjugateEquiv_symm`
applies: taking mates twice is conjugation, and conjugation of a natural transformation of left
adjoints preserves and reflects invertibility. Consequently the Beck–Chevalley comparison of
inverse images is invertible as soon as the Beck–Chevalley comparison of the two *composite
direct images*, `AlgebraicGeometry.ProEtale.smallProetaleBaseChangePushforwardMate`, is
invertible.

The point of this reduction is that the inverse image functors of
`AlgebraicGeometry.ProEtale.smallProetaleMorphism` are obtained by a choice of exact left adjoint
and are therefore accessible only through their adjunctions, whereas the direct images are
pushforwards along explicit base-change functors of sites. The reduced statement is a statement
about iterated base change in the site, with no topos theory in it, and it is proved by
descending twice: to the small pro-étale sites, where
`AlgebraicGeometry.ProEtale.smallProetaleSiteBaseChangeMate` is the same mate taken in the
categories of sites rather than of sheaves, and from there to the big pro-étale slices, where all
four functors of the square are post-composition functors `CategoryTheory.Over.map` and the
comparison `CategoryTheory.overPullbackBeckChevalley` is a conjugate of an isomorphism. The three
coherence statements that make those two descents legitimate are in
`StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.MateCoherence`.

## Main definitions

* `CategoryTheory.overPullbackBeckChevalley`: the Beck–Chevalley comparison of the two composite
  base-change functors on slices, as the iterated mate of
  `CategoryTheory.overMapCommSquare`.
* `AlgebraicGeometry.ProEtale.smallProetaleRestrict_adj`: restriction along a weakly étale
  morphism `j` is left adjoint to the direct image along `j`.
* `AlgebraicGeometry.ProEtale.smallProetaleRestrictIsoInverseImage`: restriction along `j` is the
  inverse image of the geometric morphism attached to `j`.
* `AlgebraicGeometry.ProEtale.smallProetaleSiteBaseChangeMate`: the Beck–Chevalley comparison of
  the two composite base-change functors of small pro-étale sites, as the mate of
  `AlgebraicGeometry.ProEtale.smallProetaleComposeBaseChangeIso`.
* `AlgebraicGeometry.ProEtale.smallProetaleBaseChangePushforwardMate`: the Beck–Chevalley
  comparison of the two composite direct images across the square, as the mate of
  `AlgebraicGeometry.ProEtale.smallProetaleComposeBaseChangePushforwardIso` with respect to the
  two restriction adjunctions.

## Main results

* `CategoryTheory.isIso_overPullbackBeckChevalley`: Beck–Chevalley holds for base change on
  slices. Only commutativity of the square is used, not cartesianness.
* `AlgebraicGeometry.ProEtale.isIso_smallProetaleSiteBaseChangeMate`: Beck–Chevalley holds for
  iterated base change of small pro-étale sites.
* `AlgebraicGeometry.ProEtale.isIso_smallProetaleBaseChangePushforwardMate`: Beck–Chevalley holds
  for the two composite direct images.
* `AlgebraicGeometry.ProEtale.isIso_smallProetaleBaseChangeCounitMate`: Beck–Chevalley holds for
  the two composite inverse images. This is the hypothesis `hmate` of
  `AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop_of_baseChange`.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop_of_counit`: that
  theorem with its Beck–Chevalley hypothesis discharged.

## What this supplies for Stacks 09AA, and what it does not

No `stacks` attribute is attached to any declaration here, and neither 09AA nor 09BL becomes
available.

What this file adds to `AlgebraicGeometry.ProEtale.CounitComparison` is the second of the two
inputs listed there: the Beck–Chevalley hypothesis `hmate` of
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop_of_baseChange` is
discharged, by `AlgebraicGeometry.ProEtale.isIso_smallProetaleBaseChangeCounitMate`, and the
resulting unconditional statement is
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop_of_counit`.

What remains between that statement and 09AA is exactly the first input: **Stacks 09BL**, the
affine case, which is absent from the library. It supplies the hypothesis `hcounit`, invertibility
of the counit of the direct-image adjunction along the base-changed morphism `T ×_S U ⟶ U` for `U`
a member of an affine open cover. So after this file 09AA is 09BL plus proved results, and 09BL is
untouched here; in particular no tag may be placed on the strength of this reduction.

## Implementation notes

The mate calculus cannot prove the invertibility of the comparison of inverse images from the
given isomorphism of direct images directly, and this is not an accident of the present setup.
All four of the comparisons
```
f_* ∘ j_S^* ≅ j_T^* ∘ f'_*        (the given isomorphism)
f'^{-1} ∘ j_S^* ⟶ j_T^* ∘ f^{-1}  (inverse images: the goal)
j_{T*} ∘ f_* ⟶ f'_* ∘ j_{S*}      (composite direct images)
j_{T!} ∘ f'^{-1} ⟶ f^{-1} ∘ j_{S!} (lower shriek)
```
are mates or conjugates of one another, and by
`CategoryTheory.iterated_mateEquiv_conjugateEquiv` the composite of the two mate operations is
conjugation, which does preserve and reflect invertibility; but each single mate operation does
not, and the goal is one single mate away from the given isomorphism. Both of the two remaining
candidates — the composite direct images and the lower shriek — are therefore genuinely
equivalent reformulations rather than consequences. The comparison of composite direct images is
the better target only because both of its sides are pushforwards along explicit base-change
functors of sites, whereas the inverse images and the lower shriek functors are not.

That comparison is then proved invertible by descending along those pushforwards. Both descents
are instances of a coherence statement for mates, proved in
`StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.MateCoherence`: from sheaves to sites,
`CategoryTheory.mateEquiv_sheafPushforwardContinuousNatTrans`, since
`AlgebraicGeometry.ProEtale.smallProetaleRestrict_adj` is built by
`CategoryTheory.Adjunction.sheafPushforwardContinuous`; and from the small sites to the big
slices, `CategoryTheory.mateEquiv_restrictFullyFaithful_app`, since
`AlgebraicGeometry.ProEtale.smallProetaleCompose_adj` is built by
`CategoryTheory.Adjunction.restrictFullyFaithful`. On the big slices all four functors of the
square are left adjoints and the mate calculus closes the argument, cartesianness entering only
through `CategoryTheory.mateEquiv_overMapCommSquare`.

## References

* [Stacks Project, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 0F61](https://stacks.math.columbia.edu/tag/0F61)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

section OverBeckChevalley

variable {C : Type*} [Category C] [Limits.HasPullbacks C] {T' T S' S : C}
  (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S) (hw : g' ≫ f = f' ≫ g)

/-- **Beck–Chevalley for the pullback functors on slices.** For a commuting square
`g' ≫ f = f' ≫ g` in a category with pullbacks, the comparison of the two composites of base
change on slices, obtained from `CategoryTheory.overMapCommSquare` by taking mates twice with
respect to the four adjunctions `CategoryTheory.Over.mapPullbackAdj`. -/
def overPullbackBeckChevalley :
    Over.pullback g ⋙ Over.pullback f' ⟶ Over.pullback f ⋙ Over.pullback g' :=
  mateEquiv (Over.mapPullbackAdj g) (Over.mapPullbackAdj g')
    (mateEquiv (Over.mapPullbackAdj f') (Over.mapPullbackAdj f)
      (TwoSquare.mk _ _ _ _ (overMapCommSquare g' f' f g hw).hom))

/-- The Beck–Chevalley comparison of the pullback functors on slices is invertible: all four
functors of the square `CategoryTheory.overMapCommSquare` are left adjoints, so taking mates
twice is conjugation (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), and the conjugate of
an isomorphism is an isomorphism. Note that only commutativity of the square is used, not
cartesianness. -/
instance isIso_overPullbackBeckChevalley :
    IsIso (overPullbackBeckChevalley g' f' f g hw) := by
  have key := iterated_mateEquiv_conjugateEquiv (Over.mapPullbackAdj f')
    (Over.mapPullbackAdj f) (Over.mapPullbackAdj g') (Over.mapPullbackAdj g)
    (TwoSquare.mk _ _ _ _ (overMapCommSquare g' f' f g hw).hom)
  refine Eq.mpr (congrArg IsIso key) ?_
  exact inferInstance

end OverBeckChevalley

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

section Restrict

variable (B : BigProetaleSite.{u}) {Z T : B.Scheme} (j : Z ⟶ T)
  (hj : WeaklyEtale (B.inclusion.map j))

/-- **Restriction to a localization is a left adjoint.** Restriction of small pro-étale sheaves of
sets along composition with a weakly étale morphism `j : Z ⟶ T` is left adjoint to the direct
image along `j`. This is the sheaf-level shadow of
`AlgebraicGeometry.ProEtale.smallProetaleCompose_adj`: composition with `j` is left adjoint to
base change along `j` already as functors of sites, and both are continuous. -/
def smallProetaleRestrict_adj :
    smallProetaleRestrict B j hj ⊣ (smallProetaleMorphism B Z T j).pushforward := by
  letI : (smallProetaleBaseChange B Z T j).IsContinuous
      (SmallProetale.topology B T.obj T.property)
      (SmallProetale.topology B Z.obj Z.property) :=
    (smallProetaleBaseChange_isMorphismOfSites B Z T j).toIsContinuous
  exact (smallProetaleCompose_adj B j hj).sheafPushforwardContinuous
    (SmallProetale.topology B Z.obj Z.property)
    (SmallProetale.topology B T.obj T.property)

/-- **Restriction to a localization is the inverse image.** For `j : Z ⟶ T` weakly étale,
restriction of small pro-étale sheaves of sets along composition with `j` agrees with the inverse
image of the geometric morphism attached to `j`, both being left adjoint to the direct image along
`j`. The inverse image is obtained from
`AlgebraicGeometry.ProEtale.smallProetaleBaseChange_isMorphismOfSites` by a choice of exact left
adjoint, so this is the only available description of it. -/
def smallProetaleRestrictIsoInverseImage :
    smallProetaleRestrict B j hj ≅ (smallProetaleMorphism B Z T j).inverseImage :=
  Adjunction.leftAdjointUniq (smallProetaleRestrict_adj B j hj)
    (smallProetaleMorphism B Z T j).adj

end Restrict

section SiteSquare

variable (B : BigProetaleSite.{u}) {T' T S' S : B.Scheme} (g' : T' ⟶ T) (f' : T' ⟶ S')
  (f : T ⟶ S) (g : S' ⟶ S)
  (hg : WeaklyEtale (B.inclusion.map g)) (hg' : WeaklyEtale (B.inclusion.map g'))

/-- `AlgebraicGeometry.ProEtale.smallProetaleCompose_adj` as a restriction, along the inclusions
of the two small pro-étale sites into the big slices, of the adjunction
`CategoryTheory.Over.mapPullbackAdj` between post-composition and base change on big slices. The
two commutation isomorphisms are identities, because both the composition functor and the
base-change functor of small sites are lifts through a full subcategory of the corresponding
functor of big slices. -/
theorem smallProetaleCompose_adj_eq {Z W : B.Scheme} (j : Z ⟶ W)
    (hj : WeaklyEtale (B.inclusion.map j)) :
    smallProetaleCompose_adj B j hj =
      (Over.mapPullbackAdj j).restrictFullyFaithful
        (Functor.FullyFaithful.ofFullyFaithful
          (SmallProetale.inclusion B Z.obj Z.property))
        (Functor.FullyFaithful.ofFullyFaithful
          (SmallProetale.inclusion B W.obj W.property))
        (Iso.refl _) (Iso.refl _) := rfl

/-- The square of site functors `AlgebraicGeometry.ProEtale.smallProetaleComposeBaseChangeIso`
and the square of big-slice functors `CategoryTheory.overPullbackBaseChangeIso` have the same
components: the former is obtained from the latter by cancelling the fully faithful inclusion of
the small pro-étale site of `T` into the big slice over `T`. -/
theorem smallProetaleComposeBaseChangeIso_inv_app_map (h : IsPullback g' f' f g)
    (V : SmallProetale B S'.obj S'.property) :
    (SmallProetale.inclusion B T.obj T.property).map
        ((smallProetaleComposeBaseChangeIso B g' f' f g hg hg' h).inv.app V) =
      (overPullbackBaseChangeIso g' f' f g h).inv.app
        ((SmallProetale.inclusion B S'.obj S'.property).obj V) := by
  simp only [smallProetaleComposeBaseChangeIso, Functor.fullyFaithfulCancelRight_inv_app]
  rw [Functor.map_preimage]
  exact Eq.trans (Category.id_comp (obj := BigProetaleOver B T.obj T.property)
    ((Functor.isoWhiskerLeft (SmallProetale.inclusion B S'.obj S'.property)
      (overPullbackBaseChangeIso g' f' f g h)).inv.app V)) rfl

/-- **The Beck–Chevalley comparison of iterated base change of small pro-étale sites.** For a
cartesian square with weakly étale horizontal arrows, the mate of
`AlgebraicGeometry.ProEtale.smallProetaleComposeBaseChangeIso` with respect to the two adjunctions
`AlgebraicGeometry.ProEtale.smallProetaleCompose_adj`: a comparison of base change along
`S ⟵ S' ⟵ T'` with base change along `S ⟵ T ⟵ T'`, as functors between small pro-étale sites.
This is the site-level shadow of
`AlgebraicGeometry.ProEtale.smallProetaleBaseChangePushforwardMate`. -/
def smallProetaleSiteBaseChangeMate (h : IsPullback g' f' f g) :
    smallProetaleBaseChange B S' S g ⋙ smallProetaleBaseChange B T' S' f' ⟶
      smallProetaleBaseChange B T S f ⋙ smallProetaleBaseChange B T' T g' :=
  mateEquiv (smallProetaleCompose_adj B g hg) (smallProetaleCompose_adj B g' hg')
    (TwoSquare.mk _ _ _ _ (smallProetaleComposeBaseChangeIso B g' f' f g hg hg' h).inv)

/-- **Beck–Chevalley for iterated base change of small pro-étale sites.** The comparison
`AlgebraicGeometry.ProEtale.smallProetaleSiteBaseChangeMate` is invertible.

The inclusions of the small pro-étale sites into the big slices are fully faithful, so they
reflect invertibility, and by `CategoryTheory.mateEquiv_restrictFullyFaithful_app` the image of
each component of this mate under the inclusion is the corresponding component of the mate of
`CategoryTheory.overPullbackBaseChangeIso` on big slices. By
`CategoryTheory.mateEquiv_overMapCommSquare` — the step that uses cartesianness of the square —
that mate is `CategoryTheory.overPullbackBeckChevalley`, which is invertible. -/
instance isIso_smallProetaleSiteBaseChangeMate (h : IsPullback g' f' f g) :
    IsIso (smallProetaleSiteBaseChangeMate B g' f' f g hg hg' h) := by
  have hbig : IsIso (mateEquiv (Over.mapPullbackAdj g) (Over.mapPullbackAdj g')
      (TwoSquare.mk _ _ _ _ (overPullbackBaseChangeIso g' f' f g h).inv)) := by
    rw [← congrArg (mateEquiv (Over.mapPullbackAdj g) (Over.mapPullbackAdj g'))
      (mateEquiv_overMapCommSquare g' f' f g h)]
    exact isIso_overPullbackBeckChevalley g' f' f g h.w
  have key := mateEquiv_restrictFullyFaithful_app
    (iC := SmallProetale.inclusion B S'.obj S'.property)
    (iD := SmallProetale.inclusion B S.obj S.property)
    (iE := SmallProetale.inclusion B T'.obj T'.property)
    (iF := SmallProetale.inclusion B T.obj T.property)
    (L₁ := smallProetaleCompose B g hg) (R₁ := smallProetaleBaseChange B S' S g)
    (L₂ := smallProetaleCompose B g' hg') (R₂ := smallProetaleBaseChange B T' T g')
    (G := smallProetaleBaseChange B T' S' f') (H := smallProetaleBaseChange B T S f)
    (G' := Over.pullback f') (H' := Over.pullback f)
    (Functor.FullyFaithful.ofFullyFaithful _) (Functor.FullyFaithful.ofFullyFaithful _)
    (Functor.FullyFaithful.ofFullyFaithful _) (Functor.FullyFaithful.ofFullyFaithful _)
    (Over.mapPullbackAdj g) (Over.mapPullbackAdj g')
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (smallProetaleComposeBaseChangeIso B g' f' f g hg hg' h).inv
    (overPullbackBaseChangeIso g' f' f g h).inv
    (fun V => comp_comp_eq_comp_comp_of_eq_id
      (smallProetaleComposeBaseChangeIso_inv_app_map B g' f' f g hg hg' h V)
      ((Over.map g').map_id _) rfl ((Over.pullback f).map_id _) rfl)
  simp only [smallProetaleSiteBaseChangeMate, smallProetaleCompose_adj_eq]
  refine (NatTrans.isIso_iff_isIso_app _).2 (fun V => ?_)
  refine (isIso_iff_of_reflects_iso _ (SmallProetale.inclusion B T'.obj T'.property)).1 ?_
  exact isIso_of_comp_comp_eq_comp_comp _ (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hbig _)
    ((Over.pullback f').map_id _) rfl ((Over.pullback g').map_id _) rfl (key V)

/-- `AlgebraicGeometry.ProEtale.smallProetaleComposeBaseChangePushforwardIso` is the pushforward
to sheaves of the square of site functors
`AlgebraicGeometry.ProEtale.smallProetaleComposeBaseChangeIso`. The two composition isomorphisms
it is built from are identities, pushforward along a composite of continuous functors being the
composite of the pushforwards. -/
theorem smallProetaleComposeBaseChangePushforwardIso_hom (h : IsPullback g' f' f g) :
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
    (smallProetaleComposeBaseChangePushforwardIso B g' f' f g hg hg' h).hom =
      Functor.sheafPushforwardContinuousNatTrans
        (smallProetaleComposeBaseChangeIso B g' f' f g hg hg' h).inv (Type (u + 1))
        (SmallProetale.topology B S'.obj S'.property)
        (SmallProetale.topology B T.obj T.property) := rfl

end SiteSquare

section Square

variable (B : BigProetaleSite.{u}) {T' T S' S : B.Scheme} (g' : T' ⟶ T) (f' : T' ⟶ S')
  (f : T ⟶ S) (g : S' ⟶ S)
  (hg : WeaklyEtale (B.inclusion.map g)) (hg' : WeaklyEtale (B.inclusion.map g'))

/-- **The Beck–Chevalley comparison of composite direct images.** For a cartesian square with
weakly étale horizontal arrows, the mate of
`AlgebraicGeometry.ProEtale.smallProetaleComposeBaseChangePushforwardIso` with respect to the two
restriction adjunctions `AlgebraicGeometry.ProEtale.smallProetaleRestrict_adj`: a comparison of
the direct image along `T' ⟶ T ⟶ S` with the direct image along `T' ⟶ S' ⟶ S`. Unlike the
comparison of inverse images, both sides here are restriction functors along explicit
base-change functors of sites. -/
def smallProetaleBaseChangePushforwardMate (h : IsPullback g' f' f g) :
    (smallProetaleMorphism B T' T g').pushforward ⋙
        (smallProetaleMorphism B T S f).pushforward ⟶
      (smallProetaleMorphism B T' S' f').pushforward ⋙
        (smallProetaleMorphism B S' S g).pushforward :=
  mateEquiv (smallProetaleRestrict_adj B g' hg') (smallProetaleRestrict_adj B g hg)
    (TwoSquare.mk _ _ _ _
      (smallProetaleComposeBaseChangePushforwardIso B g' f' f g hg hg' h).hom)

/-- **Beck–Chevalley for the composite direct images.** The comparison
`AlgebraicGeometry.ProEtale.smallProetaleBaseChangePushforwardMate` of the two composite direct
images across the square is invertible.

Both of its sides are pushforwards along base-change functors of sites, and by
`CategoryTheory.mateEquiv_sheafPushforwardContinuousNatTrans` the comparison itself is the
pushforward of the site-level comparison
`AlgebraicGeometry.ProEtale.smallProetaleSiteBaseChangeMate`, which is invertible. -/
theorem isIso_smallProetaleBaseChangePushforwardMate (h : IsPullback g' f' f g) :
    IsIso (smallProetaleBaseChangePushforwardMate B g' f' f g hg hg' h) := by
  have key : ∀ {Z W : B.Scheme} (j : Z ⟶ W), (smallProetaleBaseChange B Z W j).IsContinuous
      (SmallProetale.topology B W.obj W.property) (SmallProetale.topology B Z.obj Z.property) :=
    fun j => (smallProetaleBaseChange_isMorphismOfSites B _ _ j).toIsContinuous
  have e := mateEquiv_sheafPushforwardContinuousNatTrans
    (adj₁ := smallProetaleCompose_adj B g hg) (adj₂ := smallProetaleCompose_adj B g' hg')
    (A := Type (u + 1))
    (SmallProetale.topology B S'.obj S'.property)
    (SmallProetale.topology B S.obj S.property)
    (SmallProetale.topology B T'.obj T'.property)
    (SmallProetale.topology B T.obj T.property)
    (smallProetaleComposeBaseChangeIso B g' f' f g hg hg' h).inv
  have := Functor.isContinuous_comp (smallProetaleBaseChange B S' S g)
    (smallProetaleBaseChange B T' S' f')
    (SmallProetale.topology B S.obj S.property)
    (SmallProetale.topology B S'.obj S'.property)
    (SmallProetale.topology B T'.obj T'.property)
  have := Functor.isContinuous_comp (smallProetaleBaseChange B T S f)
    (smallProetaleBaseChange B T' T g')
    (SmallProetale.topology B S.obj S.property)
    (SmallProetale.topology B T.obj T.property)
    (SmallProetale.topology B T'.obj T'.property)
  have hsite : IsIso ((mateEquiv (smallProetaleCompose_adj B g hg)
      (smallProetaleCompose_adj B g' hg')
      (TwoSquare.mk _ _ _ _
        (smallProetaleComposeBaseChangeIso B g' f' f g hg hg' h).inv))) :=
    isIso_smallProetaleSiteBaseChangeMate B g' f' f g hg hg' h
  exact Eq.mpr (congrArg IsIso e) (isIso_sheafPushforwardContinuousNatTrans _ _ _)

/-- **Beck–Chevalley for inverse images.** The Beck–Chevalley comparison
`AlgebraicGeometry.ProEtale.smallProetaleBaseChangeCounitMate` of inverse images across the square
is invertible. This is the hypothesis `hmate` of
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop_of_baseChange`.

All four functors of the square of topoi are left adjoints — the two inverse images by
construction, and the two restrictions by
`AlgebraicGeometry.ProEtale.smallProetaleRestrict_adj` — so the comparison of inverse images, a
mate of the comparison of direct images, is obtained from the comparison of composite direct
images by taking mates twice, which by
`CategoryTheory.iterated_mateEquiv_conjugateEquiv_symm` is conjugation with respect to the two
composite adjunctions; and conjugation reflects invertibility. -/
theorem isIso_smallProetaleBaseChangeCounitMate (h : IsPullback g' f' f g) :
    IsIso (smallProetaleBaseChangeCounitMate B g' f' f g hg hg' h) := by
  have := isIso_smallProetaleBaseChangePushforwardMate B g' f' f g hg hg' h
  have e1 : (mateEquiv (smallProetaleRestrict_adj B g' hg')
        (smallProetaleRestrict_adj B g hg)).symm
      (smallProetaleBaseChangePushforwardMate B g' f' f g hg hg' h) =
      TwoSquare.mk _ _ _ _
        (smallProetaleComposeBaseChangePushforwardIso B g' f' f g hg hg' h).hom :=
    (mateEquiv (smallProetaleRestrict_adj B g' hg')
      (smallProetaleRestrict_adj B g hg)).symm_apply_apply _
  have e2 : (mateEquiv (smallProetaleMorphism B T S f).adj
        (smallProetaleMorphism B T' S' f').adj).symm
      ((mateEquiv (smallProetaleRestrict_adj B g' hg')
        (smallProetaleRestrict_adj B g hg)).symm
        (smallProetaleBaseChangePushforwardMate B g' f' f g hg hg' h)) =
      smallProetaleBaseChangeCounitMate B g' f' f g hg hg' h :=
    congrArg (mateEquiv (smallProetaleMorphism B T S f).adj
      (smallProetaleMorphism B T' S' f').adj).symm e1
  have e3 := e2.symm.trans (iterated_mateEquiv_conjugateEquiv_symm
    (smallProetaleMorphism B T S f).adj (smallProetaleMorphism B T' S' f').adj
    (smallProetaleRestrict_adj B g hg) (smallProetaleRestrict_adj B g' hg')
    (smallProetaleBaseChangePushforwardMate B g' f' f g hg hg' h))
  refine Eq.mpr (congrArg IsIso e3) ?_
  exact inferInstanceAs (IsIso ((conjugateEquiv
    ((smallProetaleMorphism B T S f).adj.comp (smallProetaleRestrict_adj B g' hg'))
    ((smallProetaleRestrict_adj B g hg).comp
      (smallProetaleMorphism B T' S' f').adj)).symm
    (smallProetaleBaseChangePushforwardMate B g' f' f g hg hg' h)))

end Square

/-- **Stacks 09AA from Stacks 09BL.** The counit of the direct-image adjunction along `f` on
small pro-étale sheaves of sets is invertible as soon as, over the members `U i` of a family
covering the final object of the small pro-étale site of `S`, the counit of the direct-image
adjunction along the base-changed morphism is invertible. This is
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop_of_baseChange` with
its Beck–Chevalley hypothesis discharged by
`AlgebraicGeometry.ProEtale.isIso_smallProetaleBaseChangeCounitMate`. -/
theorem smallProetaleMorphism_counit_isIso_of_coversTop_of_counit (B : BigProetaleSite.{u})
    (T S : B.Scheme) (f : T ⟶ S) {ι : Type*}
    {U : ι → SmallProetale B S.obj S.property}
    (hU : (SmallProetale.topology B S.obj S.property).CoversTop U)
    (hcounit : ∀ i, IsIso (smallProetaleMorphism B
      ((smallProetaleBaseChange B T S f).obj (U i)).obj.left (U i).obj.left
      (pullback.fst (U i).obj.hom f)).adj.counit) :
    IsIso (smallProetaleMorphism B T S f).adj.counit :=
  smallProetaleMorphism_counit_isIso_of_coversTop_of_baseChange B T S f hU
    (fun i => isIso_smallProetaleBaseChangeCounitMate B
      ((smallProetaleBaseChange B T S f).obj (U i)).obj.hom
      (pullback.fst (U i).obj.hom f) f (U i).obj.hom (U i).property
      ((smallProetaleBaseChange B T S f).obj (U i)).property
      (isPullback_smallProetaleBaseChange B T S f (U i))) hcounit

end AlgebraicGeometry.ProEtale

end

