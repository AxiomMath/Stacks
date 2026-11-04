module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.BigProetaleMorphism
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousComp
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismCriteria
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change between small pro-étale sites

Let `f : T ⟶ S` be a morphism in a chosen big pro-étale site. Pulling a weakly étale
`S`-scheme back along `f` gives a weakly étale `T`-scheme, so base change is a functor from the
small pro-étale site of `S` to that of `T`. It is a morphism of sites, and therefore represents
a geometric morphism of the small pro-étale topoi.

The file then records how the morphisms of topoi attached to `f` relate: base change commutes
with the inclusion of the small site into the big slice, both as a square of site functors and
as a square of direct images, and the small-site morphism factors through the inclusion of
`T`, big base change, and the projection back to the small site of `S`.

## Main definitions

* `AlgebraicGeometry.ProEtale.smallProetaleBaseChange` — base change on small pro-étale sites.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism` — the induced morphism of topoi.

## Main results

* `AlgebraicGeometry.ProEtale.smallProetaleBaseChange_isMorphismOfSites` — base change is a
  morphism of sites.
* `AlgebraicGeometry.ProEtale.smallProetalePushforward_obj` — its direct image on sections.
* `AlgebraicGeometry.ProEtale.smallProetaleBaseChange_comp_inclusion` and
  `AlgebraicGeometry.ProEtale.bigSmallProetalePushforwardCommIso` — the commuting square, on
  site functors and on direct images.
* `AlgebraicGeometry.ProEtale.inclusionBigBaseChangePushforwardIso`,
  `AlgebraicGeometry.ProEtale.smallProetaleMorphismFactorizationIso` and
  `AlgebraicGeometry.ProEtale.smallProetaleMorphismInclusionFactorizationIso` — the
  factorizations.

## Implementation notes

Base change is the restriction of `CategoryTheory.Over.pullback` to weakly étale objects,
obtained by lifting it along the full subcategory inclusion;
`AlgebraicGeometry.ProEtale.smallProetaleBaseChange_comp_inclusion` records that the lift
composed with the inclusion is slice pullback on the nose, and every preservation property is
transported across that equality.

Equalities of geometric morphisms are expressed as canonical natural isomorphisms of their
direct-image functors, which retains naturality in the sheaf and in the object. Being a
morphism of sites requires an exact left adjoint, which the general theory supplies for a
representably flat functor between *small* sites; the small pro-étale categories have their
objects and their morphisms in different universes, so the statement is transported along
`CategoryTheory.equivSmallModel` in each variable and then carried back, which is what the four
`rootMorphismOfSites_of_*` helpers do.

## References

* [Stacks Project, Tag 098T](https://stacks.math.columbia.edu/tag/098T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- Base change of a weakly étale object over `S` along `f`, regarded as an
object of the small pro-étale site over `T`. -/
@[stacks 098T "part (2), base-change functor"]
public noncomputable def smallProetaleBaseChange :
    SmallProetale B S.obj S.property ⥤ SmallProetale B T.obj T.property := by
  refine (IsWeaklyEtaleOver B T.obj T.property).lift
    (SmallProetale.inclusion B S.obj S.property ⋙ Over.pullback f) ?_
  intro X
  change WeaklyEtale (B.inclusion.map (pullback.snd X.obj.hom f))
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback X.obj.hom f).map B.inclusion) X.property

/-- Small-site base change followed by inclusion is big-slice base change
following inclusion, including its action on morphisms. -/
@[stacks 098T "part (3), site square"]
public theorem smallProetaleBaseChange_comp_inclusion :
    smallProetaleBaseChange B T S f ⋙ SmallProetale.inclusion B T.obj T.property =
      SmallProetale.inclusion B S.obj S.property ⋙ Over.pullback f := rfl

private lemma preservesPullbacks_baseChange :
    PreservesLimitsOfShape WalkingCospan (smallProetaleBaseChange B T S f) := by
  let : PreservesLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B S.obj S.property) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B S.obj S.property ⋙ Over.pullback f) := inferInstance
  have e : (SmallProetale.inclusion B S.obj S.property ⋙ Over.pullback f) ≅
      (smallProetaleBaseChange B T S f ⋙
        SmallProetale.inclusion B T.obj T.property) :=
    eqToIso (smallProetaleBaseChange_comp_inclusion B T S f).symm
  let := preservesLimitsOfShape_of_natIso (J := WalkingCospan) e
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (smallProetaleBaseChange B T S f) (SmallProetale.inclusion B T.obj T.property)

private lemma coverPreserving_smallProetaleBaseChange :
    CoverPreserving (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property)
      (smallProetaleBaseChange B T S f) := by
  let : HasPullbacks (SmallProetale B S.obj S.property) := inferInstance
  let := preservesPullbacks_baseChange B T S f
  apply coverPreserving_of_generators
    (smallProetaleBaseChange B T S f) (SmallProetale.precoverage B S.obj S.property)
    (SmallProetale.topology B T.obj T.property)
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := (SmallProetale.mem_precoverage_iff B S.obj S.property).1 hR
  rw [← PreZeroHypercover.sieve₀_map]
  apply Precoverage.generate_mem_toGrothendieck
  apply (SmallProetale.mem_precoverage_iff B T.obj T.property).2
  refine ⟨E.map (smallProetaleBaseChange B T S f), rfl, ?_⟩
  show B.covering _
  rw [B.covering_iff]
  refine ⟨isProetaleCovering_overPullback B f
      (E.map (SmallProetale.inclusion B S.obj S.property)) hE.1, ?_⟩
  simpa only [PreZeroHypercover.map, ← Functor.comp_obj, ← Functor.comp_map,
    smallProetaleBaseChange_comp_inclusion] using hE.2

private lemma preservesTerminal_baseChange :
    PreservesLimit (Functor.empty.{0} (SmallProetale B S.obj S.property))
      (smallProetaleBaseChange B T S f) := by
  let I := SmallProetale.inclusion B S.obj S.property
  have : PreservesLimit (Functor.empty.{0} (SmallProetale B S.obj S.property))
      (I ⋙ Over.pullback f) := inferInstance
  let e : I ⋙ Over.pullback f ≅ smallProetaleBaseChange B T S f ⋙
      SmallProetale.inclusion B T.obj T.property :=
    eqToIso (smallProetaleBaseChange_comp_inclusion B T S f).symm
  let := preservesLimit_of_natIso (Functor.empty.{0} _) e
  exact preservesLimit_of_reflects_of_preserves
    (smallProetaleBaseChange B T S f) (SmallProetale.inclusion B T.obj T.property)

private instance smallProetaleBaseChange_isContinuous :
    Functor.IsContinuous (smallProetaleBaseChange B T S f)
      (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property) := by
  let F := smallProetaleBaseChange B T S f
  let : HasPullbacks (SmallProetale B S.obj S.property) := inferInstance
  let : HasTerminal (SmallProetale B S.obj S.property) :=
    (smallIdentity_isTerminal B S.obj S.property).hasTerminal
  let : HasFiniteLimits (SmallProetale B S.obj S.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesLimitsOfShape WalkingCospan F := preservesPullbacks_baseChange B T S f
  let : PreservesLimit (Functor.empty.{0} (SmallProetale B S.obj S.property)) F :=
    preservesTerminal_baseChange B T S f
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) F :=
    preservesLimitsOfShape_pempty_of_preservesTerminal F
  let : PreservesFiniteLimits F :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks F
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  exact Functor.isContinuous_iff_coverPreserving.2
    (coverPreserving_smallProetaleBaseChange B T S f)

section MorphismOfSites

universe u₁ u₂ v₁ v₂

end MorphismOfSites

/-- Base change on small pro-étale sites is continuous and defines a morphism
of sites. -/
@[stacks 098T "part (2), morphism of sites"]
public instance smallProetaleBaseChange_isMorphismOfSites :
    _root_.IsMorphismOfSites.{u + 1} (smallProetaleBaseChange B T S f)
      (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property) := by
  let F := smallProetaleBaseChange B T S f
  let C := SmallProetale B S.obj S.property
  let D := SmallProetale B T.obj T.property
  let J := SmallProetale.topology B S.obj S.property
  let K := SmallProetale.topology B T.obj T.property
  let : Functor.IsContinuous F J K := smallProetaleBaseChange_isContinuous B T S f
  let : HasPullbacks C := inferInstance
  let : HasTerminal C := (smallIdentity_isTerminal B S.obj S.property).hasTerminal
  let : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesLimitsOfShape WalkingCospan F := preservesPullbacks_baseChange B T S f
  let : PreservesLimit (Functor.empty.{0} C) F := preservesTerminal_baseChange B T S f
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) F :=
    preservesLimitsOfShape_pempty_of_preservesTerminal F
  let : PreservesFiniteLimits F :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks F
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let eC := equivSmallModel.{u + 1} C
  let eD := equivSmallModel.{u + 1} D
  let J' := eC.inverse.inducedTopology J
  let K' := eD.inverse.inducedTopology K
  let F' := eC.inverse ⋙ F ⋙ eD.functor
  have : eC.inverse.IsContinuous J' J := inferInstance
  have : eC.functor.IsContinuous J J' := inferInstance
  have : eD.functor.IsContinuous K K' := inferInstance
  have : eD.inverse.IsContinuous K' K := inferInstance
  have : (eC.inverse ⋙ F).IsContinuous J' K :=
    Functor.isContinuous_comp eC.inverse F J' J K
  have : F'.IsContinuous J' K' :=
    Functor.isContinuous_comp (eC.inverse ⋙ F) eD.functor J' K K'
  have : RepresentablyFlat F' := inferInstance
  have hF' : F'.IsMorphismOfSites J' K' :=
    Functor.isMorphismOfSites_of_representablyFlat F' J' K'
  have hF'root : _root_.IsMorphismOfSites.{u + 1} F' J' K' :=
    rootMorphismOfSites_of_small F' J' K' hF'
  have hC : _root_.IsMorphismOfSites.{u + 1} eC.functor J J' :=
    rootMorphismOfSites_of_equivalence eC J J'
  have hD : _root_.IsMorphismOfSites.{u + 1} eD.inverse K' K :=
    rootMorphismOfSites_of_equivalence_inverse eD K K'
  have hMid : _root_.IsMorphismOfSites.{u + 1} (F' ⋙ eD.inverse) J' K :=
    isMorphismOfSites_comp K K' J' F' eD.inverse
  have hAll : _root_.IsMorphismOfSites.{u + 1} (eC.functor ⋙ (F' ⋙ eD.inverse)) J K :=
    isMorphismOfSites_comp K J' J eC.functor (F' ⋙ eD.inverse)
  let i : eC.functor ⋙ (F' ⋙ eD.inverse) ≅ F := by
    dsimp [F']
    refine NatIso.ofComponents (fun X => ?_) ?_
    · exact (eD.unitIso.app (F.obj (eC.inverse.obj (eC.functor.obj X)))).symm ≪≫
        F.mapIso (eC.unitIso.app X).symm
    · intro X Y g
      simp
  exact rootMorphismOfSites_of_iso i.symm J K hAll

/-- The geometric morphism induced by small pro-étale base change. -/
@[stacks 098T "part (2), morphism of topoi"]
public noncomputable def smallProetaleMorphism :
    MorphismOfTopoi
      (Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1)))
      (Sheaf (SmallProetale.topology B S.obj S.property) (Type (u + 1))) :=
  let h := smallProetaleBaseChange_isMorphismOfSites B T S f
  letI := h.toIsContinuous
  let L := Classical.choose h.hasExactLeftAdjoint
  let hL := Classical.choose_spec h.hasExactLeftAdjoint
  { pushforward := (smallProetaleBaseChange B T S f).sheafPushforwardContinuous
      (Type (u + 1)) (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property)
    inverseImage := L
    adj := Classical.choice hL.1
    preservesFiniteLimits := hL.2 }

/-- The direct image evaluates a sheaf on the base change of the test object. -/
@[stacks 098T "part (2), direct-image formula"]
public theorem smallProetalePushforward_obj
    (F : Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1)))
    (U : SmallProetale B S.obj S.property) :
    ((smallProetaleMorphism B T S f).pushforward.obj F).obj.obj (Opposite.op U) =
      F.obj.obj (Opposite.op ((smallProetaleBaseChange B T S f).obj U)) :=
  Functor.sheafPushforwardContinuous_obj_obj_obj
    (smallProetaleBaseChange B T S f) (Type (u + 1))
    (SmallProetale.topology B S.obj S.property)
    (SmallProetale.topology B T.obj T.property) F (Opposite.op U)

/-- The inclusion `i_f` agrees with `f_big ∘ i_T`, naturally on sheaves. -/
@[stacks 098T "part (1)"]
public noncomputable def inclusionBigBaseChangePushforwardIso :
    (smallProetaleToBigProetaleMorphism B T S f).pushforward ≅
      (smallProetaleToBigProetaleMorphism B T T (𝟙 T)).pushforward ⋙
        (bigProetaleMorphism B T S f).pushforward := by
  let J := SmallProetale.topology B T.obj T.property
  let K := BigProetaleOver.topology B T.obj T.property
  let L := BigProetaleOver.topology B S.obj S.property
  let F := smallProetaleToBigProetaleFunctor B T T (𝟙 T)
  let G := Over.map f
  let H := smallProetaleToBigProetaleFunctor B T S f
  letI : H.IsContinuous J L :=
    smallProetaleToBigProetaleFunctor_isContinuous B T S f
  have hsite : F ⋙ G = H := by
    dsimp [F, G, H, smallProetaleToBigProetaleFunctor]
    rw [Over.mapId_eq]
    rfl
  let hF := F.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) J K
  let hH := H.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) J L
  let hG := G.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) K L
  let hInv :
      (smallProetaleToBigProetaleMorphism B T S f).inverseImage ≅
        (bigProetaleMorphism B T S f).inverseImage ⋙
          (smallProetaleToBigProetaleMorphism B T T (𝟙 T)).inverseImage :=
    hH ≪≫
      (Functor.sheafPushforwardContinuousComp' (F := F) (G := G) (FG := H)
        (eqToIso hsite) (Type (u + 1)) J K L).symm ≪≫
      (Functor.isoWhiskerRight hG.symm _ ≪≫ Functor.isoWhiskerLeft _ hF.symm)
  exact (conjugateIsoEquiv
    (smallProetaleToBigProetaleMorphism B T S f).adj
    ((bigProetaleMorphism B T S f).adj.comp
      (smallProetaleToBigProetaleMorphism B T T (𝟙 T)).adj)) hInv.symm

/-- The square of small- and big-site morphisms commutes on direct images. -/
@[stacks 098T "part (3), topos square",
  stacks 0F60 "(f_big)_* F restricted to S_proet is (f_small)_* of F restricted to T_proet"]
public noncomputable def bigSmallProetalePushforwardCommIso :
    (bigProetaleToSmallProetaleMorphism B T.obj T.property).pushforward ⋙
        (smallProetaleMorphism B T S f).pushforward ≅
      (bigProetaleMorphism B T S f).pushforward ⋙
        (bigProetaleToSmallProetaleMorphism B S.obj S.property).pushforward := by
  let F := smallProetaleBaseChange B T S f
  let I_T := SmallProetale.inclusion B T.obj T.property
  let I_S := SmallProetale.inclusion B S.obj S.property
  let P := Over.pullback f
  let Js := SmallProetale.topology B S.obj S.property
  let Jt := SmallProetale.topology B T.obj T.property
  let Kt := BigProetaleOver.topology B T.obj T.property
  let Ks := BigProetaleOver.topology B S.obj S.property
  letI : I_T.IsContinuous Jt Kt :=
    (smallProetaleInclusion_isMorphismOfSites B T.obj T.property).toIsContinuous
  letI : I_S.IsContinuous Js Ks :=
    (smallProetaleInclusion_isMorphismOfSites B S.obj S.property).toIsContinuous
  letI : P.IsContinuous Ks Kt := inferInstance
  letI : (F ⋙ I_T).IsContinuous Js Kt :=
    Functor.isContinuous_comp F I_T Js Jt Kt
  letI : (I_S ⋙ P).IsContinuous Js Kt :=
    Functor.isContinuous_comp I_S P Js Ks Kt
  let hBig := (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso
    (J := Kt) (K := Ks) (Type (u + 1))
  exact F.sheafPushforwardContinuousComp I_T (Type (u + 1)) Js Jt Kt ≪≫
    Functor.sheafPushforwardContinuousIso
      (eqToIso (smallProetaleBaseChange_comp_inclusion B T S f))
      (Type (u + 1)) Js Kt ≪≫
    (I_S.sheafPushforwardContinuousComp P (Type (u + 1)) Js Ks Kt).symm ≪≫
    Functor.isoWhiskerRight hBig.symm
      (bigProetaleToSmallProetaleMorphism B S.obj S.property).pushforward

/-- The small morphism factors through `i_T`, big base change, and `π_S`. -/
@[stacks 098T "part (4), factorization through big base change"]
public noncomputable def smallProetaleMorphismFactorizationIso :
    (smallProetaleMorphism B T S f).pushforward ≅
      (smallProetaleToBigProetaleMorphism B T T (𝟙 T)).pushforward ⋙
        (bigProetaleMorphism B T S f).pushforward ⋙
          (bigProetaleToSmallProetaleMorphism B S.obj S.property).pushforward := by
  let iT := (smallProetaleToBigProetaleMorphism B T T (𝟙 T)).pushforward
  let piT := (bigProetaleToSmallProetaleMorphism B T.obj T.property).pushforward
  let fSmall := (smallProetaleMorphism B T S f).pushforward
  let fBig := (bigProetaleMorphism B T S f).pushforward
  let piS := (bigProetaleToSmallProetaleMorphism B S.obj S.property).pushforward
  exact (Functor.leftUnitor fSmall).symm ≪≫
    (Functor.isoWhiskerRight
      (projectionCompInclusionPushforwardIso B T.obj T.property) fSmall).symm ≪≫
    Functor.associator iT piT fSmall ≪≫
    Functor.isoWhiskerLeft iT (bigSmallProetalePushforwardCommIso B T S f) ≪≫
    (Functor.associator iT fBig piS).symm

/-- Equivalently, the small morphism is `π_S ∘ i_f`. -/
@[stacks 098T "part (4), factorization through i_f"]
public noncomputable def smallProetaleMorphismInclusionFactorizationIso :
    (smallProetaleMorphism B T S f).pushforward ≅
      (smallProetaleToBigProetaleMorphism B T S f).pushforward ⋙
        (bigProetaleToSmallProetaleMorphism B S.obj S.property).pushforward :=
  smallProetaleMorphismFactorizationIso B T S f ≪≫
    Functor.isoWhiskerRight (inclusionBigBaseChangePushforwardIso B T S f).symm
      (bigProetaleToSmallProetaleMorphism B S.obj S.property).pushforward

/-- The functor on small pro-étale sites induced by composing with a weakly étale `f`, left
adjoint to base change along `f`. -/
def smallProetaleMap {T T' : B.Scheme} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f)] :
    SmallProetale B T'.obj T'.property ⥤ SmallProetale B T.obj T.property := by
  refine (IsWeaklyEtaleOver B T.obj T.property).lift
    (SmallProetale.inclusion B T'.obj T'.property ⋙ Over.map f) ?_
  intro U
  change WeaklyEtale (B.inclusion.map (U.obj.hom ≫ f))
  rw [CategoryTheory.Functor.map_comp]
  have := U.property
  infer_instance

/-- Composition with `f` is left adjoint to base change along `f`. -/
def smallProetaleMapPullbackAdjunction {T T' : B.Scheme} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f)] :
    smallProetaleMap B f ⊣ smallProetaleBaseChange B T' T f :=
  (Over.mapPullbackAdj f).restrictFullyFaithful
    (IsWeaklyEtaleOver B T'.obj T'.property).fullyFaithfulι
    (IsWeaklyEtaleOver B T.obj T.property).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- Composition with a weakly étale `f` is continuous for the small pro-étale topologies. -/
theorem smallProetaleMap_isContinuous {T T' : B.Scheme} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f)] :
    (smallProetaleMap B f).IsContinuous
      (SmallProetale.topology B T'.obj T'.property)
      (SmallProetale.topology B T.obj T.property) := by
  let e : smallProetaleToBigProetaleFunctor B T T (𝟙 T) ≅
      SmallProetale.inclusion B T.obj T.property :=
    Functor.isoWhiskerLeft _ (Over.mapId T) ≪≫ Functor.rightUnitor _
  have hi : (SmallProetale.inclusion B T.obj T.property).IsCocontinuous
      (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B T.obj T.property) :=
    Functor.IsCocontinuous.of_iso e
  have hcomp : (smallProetaleMap B f ⋙
      SmallProetale.inclusion B T.obj T.property).IsContinuous
      (SmallProetale.topology B T'.obj T'.property)
      (BigProetaleOver.topology B T.obj T.property) := by
    show (smallProetaleToBigProetaleFunctor B T' T f).IsContinuous _ _
    infer_instance
  have hc := CoverPreserving.of_comp_of_isCocontinuous
    (SmallProetale.topology B T'.obj T'.property)
    (SmallProetale.topology B T.obj T.property)
    (SmallProetale.inclusion B T.obj T.property)
    (CoverPreserving.of_isContinuous (F := smallProetaleMap B f ⋙
      SmallProetale.inclusion B T.obj T.property)
      (SmallProetale.topology B T'.obj T'.property)
      (BigProetaleOver.topology B T.obj T.property))
  have hp : PreservesLimitsOfShape WalkingCospan
      (smallProetaleMap B f ⋙ SmallProetale.toScheme B T.obj T.property) := by
    show PreservesLimitsOfShape WalkingCospan (SmallProetale.toScheme B T'.obj T'.property)
    infer_instance
  have hpres : PreservesLimitsOfShape WalkingCospan (smallProetaleMap B f) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (SmallProetale.toScheme B T.obj T.property)
  have hhyper : Functor.PreservesOneHypercovers.{u + 1} (smallProetaleMap B f)
      (SmallProetale.topology B T'.obj T'.property)
      (SmallProetale.topology B T.obj T.property) :=
    Functor.PreservesOneHypercovers.of_coverPreserving hc
  exact Functor.isContinuous_of_preservesOneHypercovers (smallProetaleMap B f) _ _

end AlgebraicGeometry.ProEtale

end
