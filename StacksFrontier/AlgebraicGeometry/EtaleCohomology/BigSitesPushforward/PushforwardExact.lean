module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BigSitesPushforward.AlmostCocontinuousPullback
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousFunctors
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExistence
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.QuasiMorphism

/-!
# Direct image on big sites for a closed immersion

Let `f : X ⟶ Y` be a closed immersion and let `τ` be the syntomic, the smooth or the étale
topology. Direct image along `f` commutes with coequalizers and pushouts on sheaves of sets on
the big `τ`-site, and is exact on abelian sheaves there.

## Main results

* `AlgebraicGeometry.bigSyntomicPushforward_preservesConnectedColimits`,
  `AlgebraicGeometry.bigSmoothPushforward_preservesConnectedColimits` and
  `AlgebraicGeometry.bigEtalePushforward_preservesConnectedColimits` are the sheaf-of-sets
  statement, with the two shapes the source names spelled out separately in
  `AlgebraicGeometry.bigSyntomicPushforward_preservesPushouts`,
  `AlgebraicGeometry.bigSyntomicPushforward_preservesCoequalizers` and their smooth and étale
  counterparts.
* `AlgebraicGeometry.bigSyntomicPushforward_isExact` is the abelian syntomic case.
* `AlgebraicGeometry.bigSmoothPushforward_isExact` is the abelian smooth case.
* `AlgebraicGeometry.bigEtalePushforward_isExact` is the abelian étale case.

## Implementation notes

For each topology, direct image is restriction along the base-change functor `Over.pullback f`,
of sheaves of sets for the first group of results and of abelian sheaves for the second.
Exactness means preservation of finite limits and finite colimits. The schemes are objects of a
chosen bounded big site, as in the preceding big-site morphism constructions.

The sheaf-of-sets statements are the general form of the source's citation, Stacks Project,
Tag 04BA, namely Stacks Project, Tag 04B9, which is stated for an arbitrary pair of sites, so
they are obtained directly from the almost cocontinuity of base change. They are stated for an
arbitrary connected shape with colimits of sets, which contains both of the source's two named
cases: pushouts are `CategoryTheory.Limits.WalkingSpan`-shaped colimits and coequalizers are
`CategoryTheory.Limits.WalkingParallelPair`-shaped ones, and both shapes are connected.

The abelian exactness criterion, by contrast, is stated for sites that are small categories, so
those three cases are transported through the `ULiftHom` equivalence, which replaces a category
in `Type (u + 1)` with `Category.{u}` by an equivalent small one. Almost cocontinuity transfers
along that equivalence because both of its functors are cover preserving, and the pushforward
transports back by the induced equivalence of sheaf categories.

## References

* [Stacks Project, Tag 04C4](https://stacks.math.columbia.edu/tag/04C4)
* [Stacks Project, Tag 04B9](https://stacks.math.columbia.edu/tag/04B9)
* [Stacks Project, Tag 04BA](https://stacks.math.columbia.edu/tag/04BA)
* [Stacks Project, Tag 04C3](https://stacks.math.columbia.edu/tag/04C3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u t t'

namespace AlgebraicGeometry


private theorem almostLift
    {C : Type (u + 1)} [Category.{u} C]
    {D : Type (u + 1)} [Category.{u} D]
    {J : GrothendieckTopology.{u, u + 1} C} {K : GrothendieckTopology.{u, u + 1} D}
    (v : C ⥤ D) (ha : IsAlmostCocontinuous v J K) :
    let eC : C ≌ ULiftHom.{u + 1} C := ULiftHom.equiv
    let eD : D ≌ ULiftHom.{u + 1} D := ULiftHom.equiv
    let J' := eC.inverse.inducedTopology J
    let K' := eD.inverse.inducedTopology K
    IsAlmostCocontinuous (eC.inverse ⋙ v ⋙ eD.functor) J' K' := by
  intro eC eD J' K'
  have : eC.functor.IsDenseSubsite J J' := inferInstance
  have : eD.functor.IsDenseSubsite K K' := inferInstance
  intro U S hS
  have hS₀ : (S.functorPushforward eD.inverse) ∈ K (v.obj (eC.inverse.obj U)) :=
    ((eD.toAdjunction.isCocontinuous_iff_coverPreserving K K').1 inferInstance).cover_preserve hS
  obtain ⟨T, hT, hTmem⟩ := ha (eC.inverse.obj U) hS₀
  refine ⟨T.functorPushforward eC.functor,
    (Functor.IsDenseSubsite.coverPreserving J J' eC.functor).cover_preserve hT, ?_⟩
  rintro V f ⟨Z, g, k, hg, hfac⟩
  have hg₁ : T (eC.inverse.map f) := by
    rw [hfac]
    exact T.downward_closed hg (eC.inverse.map k)
  rcases hTmem (eC.inverse.map f) hg₁ with hempty | hS1
  · left
    have h := (Functor.IsDenseSubsite.coverPreserving K K' eD.functor).cover_preserve hempty
    rwa [Sieve.functorPushforward_bot] at h
  · right
    change (S.functorPushforward eD.inverse) (v.map (eC.inverse.map f)) at hS1
    show S (eD.functor.map (v.map (eC.inverse.map f)))
    have hS2 : S (eD.functor.map (v.map (eC.inverse.map f)) ≫
        eD.counit.app (eD.functor.obj (v.obj (eC.inverse.obj U)))) :=
      (Sieve.mem_functorPushforward_inverse (e := eD)
        (X := eD.functor.obj (v.obj (eC.inverse.obj U)))
        (f := v.map (eC.inverse.map f))).mp hS1
    have hc : eD.counit.app (eD.functor.obj (v.obj (eC.inverse.obj U))) =
        𝟙 (eD.functor.obj (v.obj (eC.inverse.obj U))) := rfl
    rwa [hc, Category.comp_id] at hS2

open Functor in
private theorem exactSmallify
    {C : Type (u + 1)} [Category.{u} C]
    {D : Type (u + 1)} [Category.{u} D]
    {J : GrothendieckTopology.{u, u + 1} C} {K : GrothendieckTopology.{u, u + 1} D}
    {v : C ⥤ D} {L : D ⥤ C} (adj : L ⊣ v)
    [v.IsContinuous J K] (ha : IsAlmostCocontinuous v J K) :
    QuasiMorphismOfSites.IsExact
      (v.sheafPushforwardContinuous Ab.{u + 1} J K) := by
  let eC : C ≌ ULiftHom.{u + 1} C := ULiftHom.equiv
  let eD : D ≌ ULiftHom.{u + 1} D := ULiftHom.equiv
  let J' := eC.inverse.inducedTopology J
  let K' := eD.inverse.inducedTopology K
  let v' : ULiftHom.{u + 1} C ⥤ ULiftHom.{u + 1} D := eC.inverse ⋙ v ⋙ eD.functor
  have : eC.inverse.IsContinuous J' J := inferInstance
  have : eD.functor.IsContinuous K K' := inferInstance
  have : (eC.inverse ⋙ v).IsContinuous J' K :=
    Functor.isContinuous_comp eC.inverse v J' J K
  have hv' : v'.IsContinuous J' K' :=
    Functor.isContinuous_comp (eC.inverse ⋙ v) eD.functor J' K K'
  have adj' : eD.inverse ⋙ L ⋙ eC.functor ⊣ v' := by
    dsimp [v']
    exact eD.symm.toAdjunction.comp (adj.comp eC.toAdjunction)
  have hm' : _root_.IsMorphismOfSites.{u + 1} v' J' K' :=
    { toIsContinuous := hv'
      hasExactLeftAdjoint := ⟨v'.sheafPullback (Type (u + 1)) J' K',
        ⟨v'.sheafAdjunctionContinuous (Type (u + 1)) J' K'⟩,
        (adj'.isMorphismOfSites_of_isLeftAdjoint (J := K') (K := J')).preservesFiniteLimits⟩ }
  have hG := exactFunctor_sheafPushforwardContinuous_of_isAlmostCocontinuous_of_smallCategory
    hm' (almostLift v ha)
  let EC := eC.sheafCongr J J' Ab.{u + 1}
  let ED := eD.sheafCongr K K' Ab.{u + 1}
  let P := v.sheafPushforwardContinuous Ab.{u + 1} J K
  let P' := v'.sheafPushforwardContinuous Ab.{u + 1} J' K'
  have hpush : ED.inverse ⋙ P ⋙ EC.functor ≅ P' := by
    dsimp [ED, EC, P, P', v']
    exact Functor.isoWhiskerLeft (eD.sheafCongr K K' Ab.{u + 1}).inverse
      (Functor.sheafPushforwardContinuousComp eC.inverse v Ab.{u + 1} J' J K) ≪≫
      Functor.sheafPushforwardContinuousComp (eC.inverse ⋙ v) eD.functor Ab.{u + 1} J' K K'
  have hpush₂ : ED.inverse ⋙ P ≅ P' ⋙ EC.inverse := Iso.isoCompInverse hpush
  have htransport : ED.functor ⋙ P' ⋙ EC.inverse ≅ P :=
    (Iso.isoInverseComp (G := ED.symm) hpush₂).symm
  have : PreservesFiniteLimits P' := ((exactFunctor_iff P').mp hG).1
  have : PreservesFiniteColimits P' := ((exactFunctor_iff P').mp hG).2
  show PreservesFiniteLimits P ∧ PreservesFiniteColimits P
  exact ⟨preservesFiniteLimits_of_natIso htransport,
    preservesFiniteColimits_of_natIso htransport⟩

/-! ### Sheaves of sets: coequalizers and pushouts -/

/-- **Stacks Project, Tag 04C4, part (1).** Direct image of sheaves of sets by a closed immersion
of big syntomic sites preserves colimits of every connected shape whose colimits of sets exist.

This is Stacks Project, Tag 04B9 — the general form of the Tag 04BA that the source cites — fed
the almost cocontinuity of base change supplied by Stacks Project, Tag 04C3. No passage to an
equivalent small site is needed, Tag 04B9 being stated for an arbitrary pair of sites. -/
@[stacks 04C4 "pushforward_coequalizers_pushouts"]
public theorem bigSyntomicPushforward_preservesConnectedColimits
    (B : AlgebraicGeometry.BigSyntomicSite.{u}) {X Y : B.category} (f : X ⟶ Y)
    [IsClosedImmersion (B.inclusion.map f)]
    (I : Type t) [Category.{t'} I] [IsConnected I] [HasColimitsOfShape I (Type (u + 1))] :
    PreservesColimitsOfShape I
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicGeometry.BigSyntomicOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigSyntomicOver.topology B X.1 X.2)) := by
  have : HasWeakSheafify (AlgebraicGeometry.BigSyntomicOver.topology B Y.1 Y.2)
      (Type (u + 1)) := inferInstance
  have : HasWeakSheafify (AlgebraicGeometry.BigSyntomicOver.topology B X.1 X.2)
      (Type (u + 1)) := inferInstance
  have : (AlgebraicGeometry.BigSyntomicOver.topology B X.1 X.2).WEqualsLocallyBijective
      (Type (u + 1)) := inferInstance
  exact Functor.preservesColimitsOfShape_sheafPushforwardContinuous_of_isAlmostCocontinuous
    (Over.pullback f) _ _ (AlgebraicGeometry.bigSyntomicPullback_isAlmostCocontinuous B f) I

/-- **Stacks Project, Tag 04C4, part (1): pushouts.** Direct image of sheaves of sets by a closed
immersion of big syntomic sites commutes with pushouts, `WalkingSpan` being a connected shape. -/
@[stacks 04C4 "pushforward_coequalizers_pushouts"]
public theorem bigSyntomicPushforward_preservesPushouts
    (B : AlgebraicGeometry.BigSyntomicSite.{u}) {X Y : B.category} (f : X ⟶ Y)
    [IsClosedImmersion (B.inclusion.map f)] :
    PreservesColimitsOfShape WalkingSpan
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicGeometry.BigSyntomicOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigSyntomicOver.topology B X.1 X.2)) :=
  bigSyntomicPushforward_preservesConnectedColimits B f WalkingSpan

/-- **Stacks Project, Tag 04C4, part (1): coequalizers.** Direct image of sheaves of sets by a
closed immersion of big syntomic sites commutes with coequalizers, `WalkingParallelPair` being a
connected shape. -/
@[stacks 04C4 "pushforward_coequalizers_pushouts"]
public theorem bigSyntomicPushforward_preservesCoequalizers
    (B : AlgebraicGeometry.BigSyntomicSite.{u}) {X Y : B.category} (f : X ⟶ Y)
    [IsClosedImmersion (B.inclusion.map f)] :
    PreservesColimitsOfShape WalkingParallelPair
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicGeometry.BigSyntomicOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigSyntomicOver.topology B X.1 X.2)) :=
  bigSyntomicPushforward_preservesConnectedColimits B f WalkingParallelPair

/-- **Stacks Project, Tag 04C4, part (1).** Direct image of sheaves of sets by a closed immersion
of big smooth sites preserves colimits of every connected shape whose colimits of sets exist. -/
@[stacks 04C4 "pushforward_coequalizers_pushouts"]
public theorem bigSmoothPushforward_preservesConnectedColimits
    (B : AlgebraicGeometry.BigSmoothSite.{u}) {X Y : B.category} (f : X ⟶ Y)
    [IsClosedImmersion ((ObjectProperty.ι _).map f)]
    (I : Type t) [Category.{t'} I] [IsConnected I] [HasColimitsOfShape I (Type (u + 1))] :
    PreservesColimitsOfShape I
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicGeometry.BigSmoothOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigSmoothOver.topology B X.1 X.2)) := by
  have : HasWeakSheafify (AlgebraicGeometry.BigSmoothOver.topology B Y.1 Y.2)
      (Type (u + 1)) := inferInstance
  have : HasWeakSheafify (AlgebraicGeometry.BigSmoothOver.topology B X.1 X.2)
      (Type (u + 1)) := inferInstance
  have : (AlgebraicGeometry.BigSmoothOver.topology B X.1 X.2).WEqualsLocallyBijective
      (Type (u + 1)) := inferInstance
  exact Functor.preservesColimitsOfShape_sheafPushforwardContinuous_of_isAlmostCocontinuous
    (Over.pullback f) _ _ (AlgebraicGeometry.bigSmoothPullback_isAlmostCocontinuous B f) I

/-- **Stacks Project, Tag 04C4, part (1): pushouts.** Direct image of sheaves of sets by a closed
immersion of big smooth sites commutes with pushouts. -/
@[stacks 04C4 "pushforward_coequalizers_pushouts"]
public theorem bigSmoothPushforward_preservesPushouts
    (B : AlgebraicGeometry.BigSmoothSite.{u}) {X Y : B.category} (f : X ⟶ Y)
    [IsClosedImmersion ((ObjectProperty.ι _).map f)] :
    PreservesColimitsOfShape WalkingSpan
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicGeometry.BigSmoothOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigSmoothOver.topology B X.1 X.2)) :=
  bigSmoothPushforward_preservesConnectedColimits B f WalkingSpan

/-- **Stacks Project, Tag 04C4, part (1): coequalizers.** Direct image of sheaves of sets by a
closed immersion of big smooth sites commutes with coequalizers. -/
@[stacks 04C4 "pushforward_coequalizers_pushouts"]
public theorem bigSmoothPushforward_preservesCoequalizers
    (B : AlgebraicGeometry.BigSmoothSite.{u}) {X Y : B.category} (f : X ⟶ Y)
    [IsClosedImmersion ((ObjectProperty.ι _).map f)] :
    PreservesColimitsOfShape WalkingParallelPair
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicGeometry.BigSmoothOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigSmoothOver.topology B X.1 X.2)) :=
  bigSmoothPushforward_preservesConnectedColimits B f WalkingParallelPair

/-- **Stacks Project, Tag 04C4, part (1).** Direct image of sheaves of sets by a closed immersion
of big étale sites preserves colimits of every connected shape whose colimits of sets exist. -/
@[stacks 04C4 "pushforward_coequalizers_pushouts"]
public theorem bigEtalePushforward_preservesConnectedColimits
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsClosedImmersion (B.inclusion.map f)]
    (I : Type t) [Category.{t'} I] [IsConnected I] [HasColimitsOfShape I (Type (u + 1))] :
    PreservesColimitsOfShape I
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicGeometry.BigEtaleOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigEtaleOver.topology B X.1 X.2)) := by
  have : HasWeakSheafify (AlgebraicGeometry.BigEtaleOver.topology B Y.1 Y.2)
      (Type (u + 1)) := inferInstance
  have : HasWeakSheafify (AlgebraicGeometry.BigEtaleOver.topology B X.1 X.2)
      (Type (u + 1)) := inferInstance
  have : (AlgebraicGeometry.BigEtaleOver.topology B X.1 X.2).WEqualsLocallyBijective
      (Type (u + 1)) := inferInstance
  exact Functor.preservesColimitsOfShape_sheafPushforwardContinuous_of_isAlmostCocontinuous
    (Over.pullback f) _ _ (AlgebraicGeometry.bigEtalePullback_isAlmostCocontinuous B f) I

/-- **Stacks Project, Tag 04C4, part (1): pushouts.** Direct image of sheaves of sets by a closed
immersion of big étale sites commutes with pushouts. -/
@[stacks 04C4 "pushforward_coequalizers_pushouts"]
public theorem bigEtalePushforward_preservesPushouts
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsClosedImmersion (B.inclusion.map f)] :
    PreservesColimitsOfShape WalkingSpan
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicGeometry.BigEtaleOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigEtaleOver.topology B X.1 X.2)) :=
  bigEtalePushforward_preservesConnectedColimits B f WalkingSpan

/-- **Stacks Project, Tag 04C4, part (1): coequalizers.** Direct image of sheaves of sets by a
closed immersion of big étale sites commutes with coequalizers. -/
@[stacks 04C4 "pushforward_coequalizers_pushouts"]
public theorem bigEtalePushforward_preservesCoequalizers
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsClosedImmersion (B.inclusion.map f)] :
    PreservesColimitsOfShape WalkingParallelPair
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicGeometry.BigEtaleOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigEtaleOver.topology B X.1 X.2)) :=
  bigEtalePushforward_preservesConnectedColimits B f WalkingParallelPair

/-! ### Abelian sheaves: exactness -/

/-- Direct image of abelian sheaves by a closed immersion of big syntomic sites is exact. -/
@[stacks 04C4 "abelian_pushforward_exact"]
public theorem bigSyntomicPushforward_isExact
    (B : AlgebraicGeometry.BigSyntomicSite.{u}) {X Y : B.category} (f : X ⟶ Y)
    [IsClosedImmersion (B.inclusion.map f)] :
    QuasiMorphismOfSites.IsExact
      ((Over.pullback f).sheafPushforwardContinuous Ab.{u + 1}
        (AlgebraicGeometry.BigSyntomicOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigSyntomicOver.topology B X.1 X.2)) := by
  exact exactSmallify (Over.mapPullbackAdj f)
    (AlgebraicGeometry.bigSyntomicPullback_isAlmostCocontinuous B f)

/-- Direct image of abelian sheaves by a closed immersion of big smooth sites is exact. -/
@[stacks 04C4 "abelian_pushforward_exact"]
public theorem bigSmoothPushforward_isExact
    (B : AlgebraicGeometry.BigSmoothSite.{u}) {X Y : B.category} (f : X ⟶ Y)
    [IsClosedImmersion ((ObjectProperty.ι _).map f)] :
    QuasiMorphismOfSites.IsExact
      ((Over.pullback f).sheafPushforwardContinuous Ab.{u + 1}
        (AlgebraicGeometry.BigSmoothOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigSmoothOver.topology B X.1 X.2)) := by
  exact exactSmallify (Over.mapPullbackAdj f)
    (AlgebraicGeometry.bigSmoothPullback_isAlmostCocontinuous B f)

/-- Direct image of abelian sheaves by a closed immersion of big étale sites is exact. -/
@[stacks 04C4 "abelian_pushforward_exact"]
public theorem bigEtalePushforward_isExact
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsClosedImmersion (B.inclusion.map f)] :
    QuasiMorphismOfSites.IsExact
      ((Over.pullback f).sheafPushforwardContinuous Ab.{u + 1}
        (AlgebraicGeometry.BigEtaleOver.topology B Y.1 Y.2)
        (AlgebraicGeometry.BigEtaleOver.topology B X.1 X.2)) := by
  exact exactSmallify (Over.mapPullbackAdj f)
    (AlgebraicGeometry.bigEtalePullback_isAlmostCocontinuous B f)

end AlgebraicGeometry
