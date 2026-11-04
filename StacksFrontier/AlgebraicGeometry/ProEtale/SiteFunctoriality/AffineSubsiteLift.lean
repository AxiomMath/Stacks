module

public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.SubsiteLiftComparison

/-!
# Small pro-étale base change computed by a cocontinuous lift between subsites

Let `f : T ⟶ S` be a morphism in a chosen big pro-étale site `B`, and suppose given

* full subsites `(C₁, J₁)` and `(C₂, J₂)` of the small pro-étale sites of `T` and of `S`,
  inserted by continuous functors `u₁` and `u₂` whose restriction functors on sheaves of
  `Type (u + 1)` are *equivalences*;
* a cocontinuous functor `l : C₁ ⥤ C₂` with a continuous right adjoint `b : C₂ ⥤ C₁`,
  compatibly with small pro-étale base change along `f`, in the sense that
  `u₂ ⋙ smallProetaleBaseChange B T S f ≅ b ⋙ u₁`.

Then the morphism of topoi `AlgebraicGeometry.ProEtale.smallProetaleMorphism` attached to `f`
is the one attached to `l`: its inverse image is the sheafified restriction along `l ⋙ u₂`,
and if `l` is fully faithful then the direct image along `f` is fully faithful and the counit
of the direct-image adjunction is invertible.

## Main results

All in the namespace `AlgebraicGeometry.ProEtale`:

* `smallProetaleMorphism_inverseImageRestrictionIso_of_cocontinuousLift`:
  the inverse-image formula.
* `smallProetaleMorphism_pushforward_fullyFaithful_of_cocontinuousLift`:
  full faithfulness of the direct image.
* `smallProetaleMorphism_counit_isIso_of_cocontinuousLift`:
  invertibility of the counit.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 098T](https://stacks.math.columbia.edu/tag/098T)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) {T S : B.Scheme} (f : T ⟶ S)
  {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  {u₁ : C₁ ⥤ SmallProetale B T.obj T.property}
  {u₂ : C₂ ⥤ SmallProetale B S.obj S.property}
  {l : C₁ ⥤ C₂} {b : C₂ ⥤ C₁}
  [u₁.IsContinuous J₁ (SmallProetale.topology B T.obj T.property)]
  [u₂.IsContinuous J₂ (SmallProetale.topology B S.obj S.property)]
  [l.IsCocontinuous J₁ J₂] [b.IsContinuous J₂ J₁]
  [∀ F : C₁ᵒᵖ ⥤ Type (u + 1), l.op.HasPointwiseRightKanExtension F]
  [(u₁.sheafPushforwardContinuous (Type (u + 1)) J₁
      (SmallProetale.topology B T.obj T.property)).IsEquivalence]
  [(u₂.sheafPushforwardContinuous (Type (u + 1)) J₂
      (SmallProetale.topology B S.obj S.property)).IsEquivalence]

/-- **The inverse-image formula, from the subsite data.** The inverse image
along `f` on small pro-étale sheaves of sets, restricted to the subsite `C₁` of the small
pro-étale site of `T`, is the sheafification of the restriction along `l ⋙ u₂` of a sheaf on
the small pro-étale site of `S`. -/
noncomputable def smallProetaleMorphism_inverseImageRestrictionIso_of_cocontinuousLift
    [HasWeakSheafify J₁ (Type (u + 1))] (adj : l ⊣ b)
    (e : u₂ ⋙ smallProetaleBaseChange B T S f ≅ b ⋙ u₁) :
    (smallProetaleMorphism B T S f).inverseImage ⋙
        u₁.sheafPushforwardContinuous (Type (u + 1)) J₁
          (SmallProetale.topology B T.obj T.property) ≅
      (l ⋙ u₂).sheafPullbackCocontinuous (Type (u + 1)) J₁
        (SmallProetale.topology B S.obj S.property) :=
  letI := (smallProetaleBaseChange_isMorphismOfSites B T S f).toIsContinuous
  sheafPullbackIsoOfCocontinuousLift (Type (u + 1)) J₁ J₂
    (SmallProetale.topology B T.obj T.property)
    (SmallProetale.topology B S.obj S.property)
    (smallProetaleMorphism B T S f).adj adj e

include J₁ J₂ in
/-- **Full faithfulness of the direct image, from the subsite data.** If the cocontinuous lift
`l` is fully faithful, the direct image along `f` on small pro-étale sheaves of sets is fully
faithful. -/
theorem smallProetaleMorphism_pushforward_fullyFaithful_of_cocontinuousLift
    [l.Full] [l.Faithful] (adj : l ⊣ b)
    (e : u₂ ⋙ smallProetaleBaseChange B T S f ≅ b ⋙ u₁) :
    Nonempty (smallProetaleMorphism B T S f).pushforward.FullyFaithful :=
  let := (smallProetaleBaseChange_isMorphismOfSites B T S f).toIsContinuous
  ⟨fullyFaithfulSheafPushforwardContinuousOfCocontinuousLift (Type (u + 1)) J₁ J₂
    (SmallProetale.topology B T.obj T.property)
    (SmallProetale.topology B S.obj S.property) adj e⟩

include J₁ J₂ in
/-- **Invertibility of the direct-image counit, from the subsite data.** If the cocontinuous
lift `l` is fully faithful, the counit of the direct-image adjunction along `f` on small
pro-étale sheaves of sets is a natural isomorphism. -/
theorem smallProetaleMorphism_counit_isIso_of_cocontinuousLift
    [l.Full] [l.Faithful] (adj : l ⊣ b)
    (e : u₂ ⋙ smallProetaleBaseChange B T S f ≅ b ⋙ u₁) :
    IsIso (smallProetaleMorphism B T S f).adj.counit :=
  let := (smallProetaleBaseChange_isMorphismOfSites B T S f).toIsContinuous
  isIso_counit_of_cocontinuousLift (Type (u + 1)) J₁ J₂
    (SmallProetale.topology B T.obj T.property)
    (SmallProetale.topology B S.obj S.property)
    (smallProetaleMorphism B T S f).adj adj e

end AlgebraicGeometry.ProEtale
