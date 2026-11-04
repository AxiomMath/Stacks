module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBaseChangeLimitUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundedSetBaseChangeTransferUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonDescentBaseChange
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent

public import StacksFrontier.CategoryTheory.Sites.Descent.OfBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentIntegralSurjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentIntegralSurjectiveGeneral

/-!
# The dévissage of effective descent for small étale sheaves

Let `f : X ⟶ Y` be a morphism of a big étale site and let `g : Z ⟶ Y` be a surjective integral
morphism or a surjective proper morphism. [Stacks, Tag 0GF1] says that if descent of small étale
sheaves is effective along the base changes `X ×_Y Z ⟶ Z` and `X ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z` of `f`,
then it is effective along `f`.

The source calls this a formal consequence of [Stacks, Tag 0GEZ] and [Stacks, Tag 0GF0]. The
formal part is `Pseudofunctor.isEquivalence_toDescentData_of_baseChange_unconditional`, which
needs, besides effective descent along `g` and its base changes, one more input: over the triple
product `Z ×_Y Z ×_Y Z`, the inverse images along the base changes of `f` must be jointly faithful
on the morphisms `pr₁^* G ⟶ pr₃^* G`. That does not follow from the hypotheses for a general
pseudofunctor. For small étale sheaves it follows from faithfulness over `Z` by base change for
the projection `pr₁ : Z ×_Y Z ×_Y Z ⟶ Z`, which is integral, respectively proper, together with
`g`: this is `smallEtaleSheaf_eq_of_map_eq_of_isIso_baseChange`, and it is where the base change
theorems [Stacks, Tag 0EYP] and [Stacks, Tag 0A3U] that the source proofs of [Stacks, Tag 0GEZ]
and [Stacks, Tag 0GF0] use enter a second time.

## Main results

* `isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_baseChange`: the dévissage for a
  family `f`, granted effective descent along `g` and its base changes and base change for the
  projection of the triple product.
* `isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_surjective_integral`: the integral
  branch, unconditionally.
* `isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_surjective_proper`: the proper
  branch, granted [Stacks, Tag 0A3U].
* `smallEtaleSheafDescentFunctor_isEquivalence_of_devissage_of_surjective_integral`: the integral
  branch of [Stacks, Tag 0GF1] in the form of the source, for one morphism `f`.
* `smallEtaleSheafDescentFunctor_isEquivalence_of_devissage_of_surjective_proper`: the proper
  branch of [Stacks, Tag 0GF1] for one morphism `f`, granted [Stacks, Tag 0A3U].
* `smallEtaleSheafDescentFunctor_isEquivalence_of_devissage`: **both branches of
  [Stacks, Tag 0GF1]**, granted [Stacks, Tag 0A3U] for the proper one.

## References

* [Stacks Project, Tag 0GF1](https://stacks.math.columbia.edu/tag/0GF1)
* [Stacks Project, Tag 0GEZ](https://stacks.math.columbia.edu/tag/0GEZ)
* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

universe t u

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

section TripleProduct

variable {ι : Type t} {X : ι → B.Scheme} {Y Z : B.Scheme} (f : ∀ i, X i ⟶ Y) (g : Z ⟶ Y)

/-- The first projection `Z ×_Y Z ×_Y Z ⟶ Z` of the triple product, for a single morphism `g`. -/
local notation "𝔮" => tripleProj₁ (fun _ : Unit ↦ g) () () ()

/-- The base change `X i ×_Y (Z ×_Y Z ×_Y Z) ⟶ X i ×_Y Z` of the first projection of the triple
product. -/
noncomputable abbrev tripleBaseChangeProj (i : ι) :
    pullback (f i) (𝔮 ≫ g) ⟶ pullback (f i) g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ 𝔮)
    (pullback.condition.trans (Category.assoc _ _ _).symm)

/-- The composite of `tripleBaseChangeProj` with the second projection `X i ×_Y Z ⟶ Z` is the
second projection `X i ×_Y (Z ×_Y Z ×_Y Z) ⟶ Z ×_Y Z ×_Y Z` followed by the first projection of
the triple product. -/
lemma tripleBaseChangeProj_snd (i : ι) :
    tripleBaseChangeProj B f g i ≫ pullback.snd (f i) g =
      pullback.snd (f i) (𝔮 ≫ g) ≫ 𝔮 :=
  pullback.lift_snd _ _ _

/-- The square formed by the first projection of the triple product and the base change of `f`
is cartesian. -/
lemma isPullback_tripleBaseChangeProj (i : ι) :
    IsPullback (pullback.snd (f i) (𝔮 ≫ g)) (tripleBaseChangeProj B f g i)
      (𝔮) (pullback.snd (f i) g) := by
  refine IsPullback.flip (IsPullback.of_right ?_ (tripleBaseChangeProj_snd B f g i)
    (IsPullback.of_hasPullback (f i) g))
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback (f i) (𝔮 ≫ g)

/-- **Joint faithfulness over the triple product, from base change.** If `F.toDescentData` is
faithful along the base change `{X i ×_Y Z ⟶ Z}` of `f` along `g`, and the base change morphism
for the first projection `pr₁ : Z ×_Y Z ×_Y Z ⟶ Z` against the projections `X i ×_Y Z ⟶ Z` is
invertible, then two morphisms `pr₁^* G ⟶ N` which agree after inverse image along every
`X i ×_Y (Z ×_Y Z ×_Y Z) ⟶ Z ×_Y Z ×_Y Z` are equal. -/
theorem smallEtaleSheaf_eq_of_map_eq_of_isIso_baseChange
    [((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun i ↦ pullback.snd (f i) g)).Faithful]
    (hbc : ∀ i M, IsIso ((smallEtaleBaseChangeNatTransUniv.{u, 0} B
      (pullback.snd (f i) (𝔮 ≫ g)) (tripleBaseChangeProj B f g i) (𝔮)
      (pullback.snd (f i) g) (isPullback_tripleBaseChangeProj B f g i).w).app M))
    (G : (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.obj (.mk (.op Z)))
    (N : (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.obj
      (.mk (.op (pullback (pullback.snd g g) (pullback.fst g g)))))
    (x y : ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map
      (𝔮).op.toLoc).toFunctor.obj G ⟶ N)
    (h : ∀ i, ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map
        (pullback.snd (f i) (𝔮 ≫ g)).op.toLoc).toFunctor.map x =
      ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map
        (pullback.snd (f i) (𝔮 ≫ g)).op.toLoc).toFunctor.map y) :
    x = y := by
  let adj := smallEtaleSheafPseudofunctorAdjunctionGeneral B (𝔮)
  refine adj.homEquiv _ _ |>.injective (eq_of_toDescentData_faithful
    (fun i ↦ pullback.snd (f i) g) fun i ↦ ?_)
  let β := (mateEquiv adj
    (smallEtaleSheafPseudofunctorAdjunctionGeneral B (tripleBaseChangeProj B f g i))
    (Pseudofunctor.commSqTwoSquare (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor
      (isPullback_tripleBaseChangeProj B f g i).w)).natTrans
  have : ∀ M, Mono (β.app M) := fun M ↦ by
    have hβ : β = smallEtaleBaseChangeNatTransUniv.{u, 0} B _ _ _ _
        (isPullback_tripleBaseChangeProj B f g i).w :=
      mateEquiv_commSqTwoSquare_smallEtaleSheafPullbackSystem B _ _ _ _ _
    rw [hβ]
    exact @IsIso.mono_of_iso _ _ _ _ _ (hbc i M)
  exact Adjunction.map_homEquiv_eq_of_map_eq adj _ _ _ β (h i)

end TripleProduct

section Devissage

variable {ι : Type t} {X : ι → B.Scheme} {Y Z : B.Scheme} (f : ∀ i, X i ⟶ Y) (g : Z ⟶ Y)

/-- The first projection `Z ×_Y Z ×_Y Z ⟶ Z` of the triple product, for a single morphism `g`. -/
local notation "𝔮" => tripleProj₁ (fun _ : Unit ↦ g) () () ()

/-- **The dévissage of effective descent for small étale sheaves, from base change.** Let
`f i : X i ⟶ Y` be a family and `g : Z ⟶ Y` a morphism of a big étale site such that descent of
small étale sheaves is effective along `g` and along each of its base changes, and such that the
base change morphism for the first projection of `Z ×_Y Z ×_Y Z` against the base change of `f`
is invertible. If descent is effective along `{X i ×_Y Z ⟶ Z}` and along
`{X i ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z}`, it is effective along `f`. -/
theorem isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_baseChange
    (hg : ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun _ : Unit ↦ g)).IsEquivalence)
    (hgT : ∀ ⦃T : B.Scheme⦄ (t : T ⟶ Y),
      ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun _ : Unit ↦ pullback.fst t g)).IsEquivalence)
    (hbc : ∀ i M, IsIso ((smallEtaleBaseChangeNatTransUniv.{u, 0} B
      (pullback.snd (f i) (𝔮 ≫ g)) (tripleBaseChangeProj B f g i) (𝔮)
      (pullback.snd (f i) g) (isPullback_tripleBaseChangeProj B f g i).w).app M))
    (hZ : ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun i ↦ pullback.snd (f i) g)).IsEquivalence)
    (hZZ : ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun i ↦ pullback.snd (f i) (pullback.fst g g ≫ g))).IsEquivalence) :
    ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData f).IsEquivalence :=
  isEquivalence_toDescentData_of_baseChange_unconditional f (fun _ : Unit ↦ g) hg
    (fun _ t ↦ have := hgT t; ⟨Functor.FullyFaithful.ofFullyFaithful _⟩) (fun _ ↦ hZ)
    (fun _ _ ↦ ⟨Functor.FullyFaithful.ofFullyFaithful _⟩)
    fun _ _ _ G _ x y h ↦ smallEtaleSheaf_eq_of_map_eq_of_isIso_baseChange B f g hbc G _ x y h

/-- The first projection of the triple product of a morphism of a big étale site is a composite
of two base changes of it. -/
lemma inclusion_map_tripleProj₁ :
    B.inclusion.map (𝔮) =
      B.inclusion.map (pullback.fst (pullback.snd g g) (pullback.fst g g)) ≫
        B.inclusion.map (pullback.fst g g) :=
  B.inclusion.map_comp _ _

variable {g} in
/-- A property of morphisms of schemes stable under base change and composition, enjoyed by `g`,
is enjoyed by the base change of `g` along any morphism. -/
lemma inclusion_map_baseChange_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (hP : P (B.inclusion.map g)) ⦃T : B.Scheme⦄ (t : T ⟶ Y) :
    P (B.inclusion.map (pullback.fst t g)) := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  exact MorphismProperty.of_isPullback (P := P)
    (B.inclusion.map_isPullback (IsPullback.of_hasPullback t g).flip) hP

variable {g} in
/-- A property of morphisms of schemes stable under base change and composition, enjoyed by `g`,
is enjoyed by the first projection of its triple product. -/
lemma inclusion_map_tripleProj₁_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] (hP : P (B.inclusion.map g)) :
    P (B.inclusion.map (𝔮)) := by
  have h₁ : P (B.inclusion.map (pullback.fst g g)) :=
    inclusion_map_baseChange_of_isStableUnderBaseChange B P hP g
  rw [inclusion_map_tripleProj₁]
  exact P.comp_mem _ _
    (inclusion_map_baseChange_of_isStableUnderBaseChange B P h₁ (pullback.snd g g)) h₁

/-- **The integral branch of the dévissage of [Stacks, Tag 0GF1], for a family.** Let
`f i : X i ⟶ Y` be a family and `g : Z ⟶ Y` a surjective integral morphism of a big étale site.
If descent of small étale sheaves is effective along `{X i ×_Y Z ⟶ Z}` and along
`{X i ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z}`, it is effective along `f`. -/
theorem isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_surjective_integral
    [Surjective (B.inclusion.map g)] [IsIntegralHom (B.inclusion.map g)]
    (hZ : ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun i ↦ pullback.snd (f i) g)).IsEquivalence)
    (hZZ : ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun i ↦ pullback.snd (f i) (pullback.fst g g ≫ g))).IsEquivalence) :
    ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData f).IsEquivalence := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  refine isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_baseChange B f g
    ((isEquivalence_smallEtaleSheafDescentFunctor_iff_general B g).1
      (smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_integral_unconditional B g))
    (fun T t ↦ ?_) (fun i M ↦ ?_) hZ hZZ
  · have : Surjective (B.inclusion.map (pullback.fst t g)) :=
      inclusion_map_baseChange_of_isStableUnderBaseChange B @Surjective ‹_› t
    have : IsIntegralHom (B.inclusion.map (pullback.fst t g)) :=
      inclusion_map_baseChange_of_isStableUnderBaseChange B @IsIntegralHom ‹_› t
    exact (isEquivalence_smallEtaleSheafDescentFunctor_iff_general B _).1
      (smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_integral_unconditional B _)
  · have : IsIntegralHom (B.inclusion.map (𝔮)) :=
      inclusion_map_tripleProj₁_of_isStableUnderBaseChange B @IsIntegralHom ‹_›
    exact isIso_smallEtaleBaseChangeNatTrans_of_isIntegralHom_univ.{0} B _ _ _ _
      (B.inclusion.map_isPullback (isPullback_tripleBaseChangeProj B f g i)) _ M

/-- **The proper branch of the dévissage of [Stacks, Tag 0GF1], for a family, granted
[Stacks, Tag 0A3U].** Let `f i : X i ⟶ Y` be a family and `g : Z ⟶ Y` a surjective proper
morphism of a big étale site. Granted the proper base change theorem for sheaves of sets, if
descent of small étale sheaves is effective along `{X i ×_Y Z ⟶ Z}` and along
`{X i ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z}`, it is effective along `f`. -/
theorem isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_surjective_proper
    [Surjective (B.inclusion.map g)] [IsProper (B.inclusion.map g)]
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (hZ : ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun i ↦ pullback.snd (f i) g)).IsEquivalence)
    (hZZ : ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun i ↦ pullback.snd (f i) (pullback.fst g g ≫ g))).IsEquivalence) :
    ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData f).IsEquivalence := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  refine isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_baseChange B f g
    ((isEquivalence_smallEtaleSheafDescentFunctor_iff_general B g).1
      (smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange B g
        h0A3U))
    (fun T t ↦ ?_) (fun i M ↦ ?_) hZ hZZ
  · have : Surjective (B.inclusion.map (pullback.fst t g)) :=
      inclusion_map_baseChange_of_isStableUnderBaseChange B @Surjective ‹_› t
    have : IsProper (B.inclusion.map (pullback.fst t g)) :=
      inclusion_map_baseChange_of_isStableUnderBaseChange B @IsProper ‹_› t
    exact (isEquivalence_smallEtaleSheafDescentFunctor_iff_general B _).1
      (smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange B _
        h0A3U)
  · have hp : IsProper (B.inclusion.map (𝔮)) :=
      inclusion_map_tripleProj₁_of_isStableUnderBaseChange B @IsProper ‹_›
    have := SmallEtale.isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange_general
      B (𝔮) (pullback.snd (f i) g) (pullback.snd (f i) (𝔮 ≫ g))
      (tripleBaseChangeProj B f g i) (isPullback_tripleBaseChangeProj B f g i).w
      (h0A3U _ _ _ _ (B.inclusion.map_isPullback (isPullback_tripleBaseChangeProj B f g i)) hp)
    infer_instance

end Devissage

section SingleMorphism

variable {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Z ⟶ Y)

/-- **The integral branch of [Stacks, Tag 0GF1].** Let `f : X ⟶ Y` be a morphism and
`g : Z ⟶ Y` a surjective integral morphism of a big étale site. If the functors from small étale
sheaves on `Z` to descent data for `{X ×_Y Z ⟶ Z}` and from small étale sheaves on `Z ×_Y Z` to
descent data for `{X ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z}` are equivalences of categories, then so is the
functor from small étale sheaves on `Y` to descent data for `{X ⟶ Y}`. -/
theorem smallEtaleSheafDescentFunctor_isEquivalence_of_devissage_of_surjective_integral
    [Surjective (B.inclusion.map g)] [IsIntegralHom (B.inclusion.map g)]
    (hZ : (smallEtaleSheafDescentFunctorGeneral B (pullback.snd f g)).IsEquivalence)
    (hZZ : (smallEtaleSheafDescentFunctorGeneral B
      (pullback.snd f (pullback.fst g g ≫ g))).IsEquivalence) :
    (smallEtaleSheafDescentFunctorGeneral B f).IsEquivalence :=
  (isEquivalence_smallEtaleSheafDescentFunctor_iff_general B f).2
    (isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_surjective_integral B
      (fun _ : Unit ↦ f) g ((isEquivalence_smallEtaleSheafDescentFunctor_iff_general B _).1 hZ)
      ((isEquivalence_smallEtaleSheafDescentFunctor_iff_general B _).1 hZZ))

/-- **The proper branch of [Stacks, Tag 0GF1], granted [Stacks, Tag 0A3U].** Let `f : X ⟶ Y` be a
morphism and `g : Z ⟶ Y` a surjective proper morphism of a big étale site. Granted the proper
base change theorem for sheaves of sets, if the functors from small étale sheaves on `Z` to
descent data for `{X ×_Y Z ⟶ Z}` and from small étale sheaves on `Z ×_Y Z` to descent data for
`{X ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z}` are equivalences of categories, then so is the functor from small
étale sheaves on `Y` to descent data for `{X ⟶ Y}`. -/
theorem smallEtaleSheafDescentFunctor_isEquivalence_of_devissage_of_surjective_proper
    [Surjective (B.inclusion.map g)] [IsProper (B.inclusion.map g)]
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (hZ : (smallEtaleSheafDescentFunctorGeneral B (pullback.snd f g)).IsEquivalence)
    (hZZ : (smallEtaleSheafDescentFunctorGeneral B
      (pullback.snd f (pullback.fst g g ≫ g))).IsEquivalence) :
    (smallEtaleSheafDescentFunctorGeneral B f).IsEquivalence :=
  (isEquivalence_smallEtaleSheafDescentFunctor_iff_general B f).2
    (isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_surjective_proper B
      (fun _ : Unit ↦ f) g h0A3U
      ((isEquivalence_smallEtaleSheafDescentFunctor_iff_general B _).1 hZ)
      ((isEquivalence_smallEtaleSheafDescentFunctor_iff_general B _).1 hZZ))

/-- **[Stacks, Tag 0GF1], granted [Stacks, Tag 0A3U].** Let `f : X ⟶ Y` be a morphism and let
`g : Z ⟶ Y` be a surjective integral morphism or a surjective proper morphism of a big étale site.
If the functors from small étale sheaves on `Z` to descent data for `{X ×_Y Z ⟶ Z}` and from small
étale sheaves on `Z ×_Y Z` to descent data for `{X ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z}` are equivalences of
categories, then so is the functor from small étale sheaves on `Y` to descent data for `{X ⟶ Y}`.

The hypothesis `h0A3U` is the proper base change theorem for sheaves of sets, [Stacks, Tag 0A3U];
it is used only in the proper branch. The integral branch is
`smallEtaleSheafDescentFunctor_isEquivalence_of_devissage_of_surjective_integral`, which needs no
such hypothesis. -/
theorem smallEtaleSheafDescentFunctor_isEquivalence_of_devissage
    (hg : (Surjective (B.inclusion.map g) ∧ IsIntegralHom (B.inclusion.map g)) ∨
      (Surjective (B.inclusion.map g) ∧ IsProper (B.inclusion.map g)))
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (hZ : (smallEtaleSheafDescentFunctorGeneral B (pullback.snd f g)).IsEquivalence)
    (hZZ : (smallEtaleSheafDescentFunctorGeneral B
      (pullback.snd f (pullback.fst g g ≫ g))).IsEquivalence) :
    (smallEtaleSheafDescentFunctorGeneral B f).IsEquivalence := by
  rcases hg with ⟨_, _⟩ | ⟨_, _⟩
  · exact smallEtaleSheafDescentFunctor_isEquivalence_of_devissage_of_surjective_integral B f g
      hZ hZZ
  · exact smallEtaleSheafDescentFunctor_isEquivalence_of_devissage_of_surjective_proper B f g
      h0A3U hZ hZZ

end SingleMorphism

end AlgebraicGeometry

end
