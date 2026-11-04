module

public import Mathlib.CategoryTheory.Functor.Flat
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.LeftKanExtensionExactness
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksCore.Tactic.StacksAttribute

/-!
# The small pro-étale topos at the bottom of the big pro-étale topos

For a scheme in a chosen big pro-étale site, the inclusion of its small pro-étale site into the
big slice is a morphism of sites, and so defines a projection `π_S` of topoi running in the
opposite direction. The morphism of topoi attached to the identity of the scheme is a section
of that projection, and its inverse image is restriction to the small site.

## Main definitions

* `AlgebraicGeometry.ProEtale.bigProetaleToSmallProetaleMorphism` — the projection from the big
  pro-étale topos over a scheme to its small pro-étale topos.

## Main results

* `AlgebraicGeometry.ProEtale.smallProetaleInclusion_isMorphismOfSites` — the inclusion is a
  morphism of sites.
* `AlgebraicGeometry.ProEtale.smallProetaleInclusion_preservesTerminal` — together with
  `AlgebraicGeometry.ProEtale.smallProetaleInclusion_preservesPullbacks`, the finite-limit
  hypotheses of the bigger-site criterion.
* `AlgebraicGeometry.ProEtale.projectionCompInclusionPushforwardIso` — the composite of
  projection and inclusion is naturally the identity.
* `AlgebraicGeometry.ProEtale.inclusionInverseImageIsoProjectionPushforward` — inverse image
  along the inclusion is restriction to the small site.

## Implementation notes

The small-site inclusion is the full-subcategory inclusion of the big slice, so fullness and
faithfulness are inherited. The geometric inclusion `i_S` is literally
`AlgebraicGeometry.ProEtale.smallProetaleToBigProetaleMorphism` at the identity of `S`, not a
second copy of the construction; the displayed equality of geometric morphisms is expressed by
a natural isomorphism of their direct-image functors. The objectwise formula for inverse image
is the canonical restriction isomorphism
`CategoryTheory.Functor.sheafPullbackCocontinuousObjObjIso`.

Exactness of the left adjoint of the inclusion's pushforward is obtained from representable
flatness: left Kan extension along the opposite of the inclusion is computed pointwise by a
filtered colimit, and filtered colimits of types are exact.

## References

* [Stacks Project, Tag 098Q](https://stacks.math.columbia.edu/tag/098Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- NO `lanEvaluationIsoColimit` HERE. It stated exactly `CategoryTheory.lanEvaluationIsoColimit`
-- (`StacksFrontier/AlgebraicGeometry/Topologies/BigSites/LeftKanExtensionExactness.lean`:41),
-- which is public, imports only Mathlib, and is now imported.

private theorem smallProetaleInclusion_lan_preservesFiniteLimits
    [RepresentablyFlat (SmallProetale.inclusion B S hS)] :
    PreservesFiniteLimits ((SmallProetale.inclusion B S hS).op.lan :
      ((SmallProetale B S hS)ᵒᵖ ⥤ Type (u + 1)) ⥤
        (BigProetaleOver B S hS)ᵒᵖ ⥤ Type (u + 1)) := by
  let F := (SmallProetale.inclusion B S hS).op
  refine preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1} _ fun I _ _ =>
    preservesLimitsOfShape_of_evaluation _ I fun Y => ?_
  let : IsFiltered (CostructuredArrow F Y) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (SmallProetale.inclusion B S hS) Y.unop)
  exact preservesLimitsOfShape_of_natIso
    (CategoryTheory.lanEvaluationIsoColimit (Type (u + 1)) F Y).symm

/-- The inclusion carries the final object of the small pro-étale site to the
final object of the big pro-étale slice. -/
@[stacks 098Q "preservation of the final object"]
public instance smallProetaleInclusion_preservesTerminal :
    PreservesLimit (Functor.empty.{0} (SmallProetale B S hS))
      (SmallProetale.inclusion B S hS) := by
  apply preservesTerminal_of_iso (SmallProetale.inclusion B S hS)
  let i := SmallProetale.inclusion B S hS
  let e := (terminalIsTerminal (C := SmallProetale B S hS)).uniqueUpToIso
    (smallIdentity_isTerminal B S hS)
  have ht : IsTerminal (i.obj (smallIdentity B S hS)) := by
    simpa [i, SmallProetale.inclusion, smallIdentity] using
      (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (⟨S, hS⟩ : B.Scheme))))
  exact i.mapIso e ≪≫ ht.uniqueUpToIso (terminalIsTerminal (C := BigProetaleOver B S hS))

/-- The full inclusion defines a morphism of sites from the big pro-étale
slice to the small pro-étale site. -/
@[stacks 098Q "the morphism of sites"]
public instance smallProetaleInclusion_isMorphismOfSites :
    _root_.IsMorphismOfSites.{u + 1} (SmallProetale.inclusion B S hS)
      (SmallProetale.topology B S hS) (BigProetaleOver.topology B S hS) := by
  let v := smallProetaleToBigProetaleFunctor B (⟨S, hS⟩ : B.Scheme)
    (⟨S, hS⟩ : B.Scheme) (𝟙 (⟨S, hS⟩ : B.Scheme))
  have e : v = SmallProetale.inclusion B S hS := by
    dsimp [v, smallProetaleToBigProetaleFunctor]
    rw [Over.mapId_eq]
    rfl
  let : (SmallProetale.inclusion B S hS).IsContinuous
      (SmallProetale.topology B S hS) (BigProetaleOver.topology B S hS) :=
    e ▸ (smallProetaleToBigProetaleFunctor_isContinuous B (⟨S, hS⟩ : B.Scheme)
      (⟨S, hS⟩ : B.Scheme) (𝟙 (⟨S, hS⟩ : B.Scheme)))
  let : HasPullbacks (SmallProetale B S hS) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan (SmallProetale.inclusion B S hS) :=
    smallProetaleInclusion_preservesPullbacks B S hS
  have hterm : IsTerminal ((SmallProetale.inclusion B S hS).obj
      (smallIdentity B S hS)) := by
    simpa [SmallProetale.inclusion, smallIdentity] using
      (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (⟨S, hS⟩ : B.Scheme))))
  let : HasTerminal (SmallProetale B S hS) := (smallIdentity_isTerminal B S hS).hasTerminal
  let : HasFiniteLimits (SmallProetale B S hS) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SmallProetale.inclusion B S hS) :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal (SmallProetale.inclusion B S hS)
      (smallIdentity_isTerminal B S hS) hterm
  let : PreservesFiniteLimits (SmallProetale.inclusion B S hS) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks
      (SmallProetale.inclusion B S hS)
  let : RepresentablyFlat (SmallProetale.inclusion B S hS) :=
    flat_of_preservesFiniteLimits (SmallProetale.inclusion B S hS)
  let : (SmallProetale.inclusion B S hS).sheafPushforwardContinuous
      (Type (u + 1)) (SmallProetale.topology B S hS)
      (BigProetaleOver.topology B S hS) |>.IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (SmallProetale.inclusion B S hS) (Type (u + 1)) (SmallProetale.topology B S hS)
      (BigProetaleOver.topology B S hS)).isRightAdjoint
  let : PreservesFiniteLimits ((SmallProetale.inclusion B S hS).op.lan :
      ((SmallProetale B S hS)ᵒᵖ ⥤ Type (u + 1)) ⥤
        (BigProetaleOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
    smallProetaleInclusion_lan_preservesFiniteLimits B S hS
  refine { toIsContinuous := inferInstance, hasExactLeftAdjoint := ?_ }
  let L := (SmallProetale.inclusion B S hS).sheafPullback (Type (u + 1))
    (SmallProetale.topology B S hS) (BigProetaleOver.topology B S hS)
  refine ⟨L, ?_, ?_⟩
  · exact ⟨(SmallProetale.inclusion B S hS).sheafAdjunctionContinuous (Type (u + 1))
      (SmallProetale.topology B S hS) (BigProetaleOver.topology B S hS)⟩
  · exact Functor.sheafPullbackConstruction.preservesFiniteLimits
      (SmallProetale.inclusion B S hS) (Type (u + 1)) (SmallProetale.topology B S hS)
      (BigProetaleOver.topology B S hS)

/-- The geometric morphism `π_S` associated to the inclusion of the small
pro-étale site into the big pro-étale slice. -/
@[stacks 098Q "the projection of topoi",
  stacks 098R "restriction to the small pro-étale site is the pushforward along this projection"]
public noncomputable def bigProetaleToSmallProetaleMorphism :
    MorphismOfTopoi
      (Sheaf (BigProetaleOver.topology B S hS) (Type (u + 1)))
      (Sheaf (SmallProetale.topology B S hS) (Type (u + 1))) :=
  let h := smallProetaleInclusion_isMorphismOfSites B S hS
  letI := h.toIsContinuous
  let L := Classical.choose h.hasExactLeftAdjoint
  let hL := Classical.choose_spec h.hasExactLeftAdjoint
  { pushforward := (SmallProetale.inclusion B S hS).sheafPushforwardContinuous
      (Type (u + 1)) (SmallProetale.topology B S hS)
      (BigProetaleOver.topology B S hS)
    inverseImage := L
    adj := Classical.choice hL.1
    preservesFiniteLimits := hL.2 }

add_to_stacks 098Q "the inclusion i_S is i_id from 098P"
  AlgebraicGeometry.ProEtale.smallProetaleToBigProetaleMorphism

/-- The composite `π_S ∘ i_S` is naturally the identity of the small
pro-étale topos, with `i_S = i_{\mathrm{id}_S}`. -/
@[stacks 098Q "the section property"]
public noncomputable def projectionCompInclusionPushforwardIso :
    (smallProetaleToBigProetaleMorphism B
        (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
        (𝟙 (⟨S, hS⟩ : B.Scheme))).pushforward ⋙
      (bigProetaleToSmallProetaleMorphism B S hS).pushforward ≅
        𝟭 (Sheaf (SmallProetale.topology B S hS) (Type (u + 1))) := by
  let v := smallProetaleToBigProetaleFunctor B
    (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
    (𝟙 (⟨S, hS⟩ : B.Scheme))
  have e : v = SmallProetale.inclusion B S hS := by
    dsimp [v, smallProetaleToBigProetaleFunctor]
    rw [Over.mapId_eq]
    rfl
  letI : v.IsContinuous (SmallProetale.topology B S hS)
      (BigProetaleOver.topology B S hS) :=
    smallProetaleToBigProetaleFunctor_isContinuous B
      (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
      (𝟙 (⟨S, hS⟩ : B.Scheme))
  letI : v.IsCocontinuous (SmallProetale.topology B S hS)
      (BigProetaleOver.topology B S hS) :=
    smallProetaleToBigProetaleFunctor_isCocontinuous B
      (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
      (𝟙 (⟨S, hS⟩ : B.Scheme))
  letI : v.Full := by
    dsimp [v, smallProetaleToBigProetaleFunctor]
    infer_instance
  letI : v.Faithful := by
    dsimp [v, smallProetaleToBigProetaleFunctor]
    infer_instance
  letI : ∀ F : (SmallProetale B S hS)ᵒᵖ ⥤ Type (u + 1),
      v.op.HasPointwiseRightKanExtension F := by
    intro F
    infer_instance
  letI : IsIso (v.sheafAdjunctionCocontinuous (Type (u + 1))
      (SmallProetale.topology B S hS) (BigProetaleOver.topology B S hS)).counit :=
    Functor.isIso_sheafAdjunctionCocontinuous_counit v (Type (u + 1))
      (SmallProetale.topology B S hS) (BigProetaleOver.topology B S hS)
  let e' := Functor.sheafPushforwardContinuousIso (eqToIso e) (Type (u + 1))
    (SmallProetale.topology B S hS) (BigProetaleOver.topology B S hS)
  simpa [smallProetaleToBigProetaleMorphism,
    smallProetaleToBigProetaleFunctor,
    bigProetaleToSmallProetaleMorphism] using
    ((Functor.isoWhiskerLeft
      (v.sheafPushforwardCocontinuous (Type (u + 1))
        (SmallProetale.topology B S hS) (BigProetaleOver.topology B S hS)) e'.symm).trans
      (asIso (v.sheafAdjunctionCocontinuous (Type (u + 1))
        (SmallProetale.topology B S hS) (BigProetaleOver.topology B S hS)).counit))

/-- Inverse image along `i_S` is naturally restriction to the small
pro-étale site, equivalently direct image along `π_S`. -/
@[stacks 098Q "inverse image is restriction"]
public noncomputable def inclusionInverseImageIsoProjectionPushforward :
    (smallProetaleToBigProetaleMorphism B
        (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
        (𝟙 (⟨S, hS⟩ : B.Scheme))).inverseImage ≅
      (bigProetaleToSmallProetaleMorphism B S hS).pushforward := by
  let v := smallProetaleToBigProetaleFunctor B
    (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
    (𝟙 (⟨S, hS⟩ : B.Scheme))
  have e : v = SmallProetale.inclusion B S hS := by
    dsimp [v, smallProetaleToBigProetaleFunctor]
    rw [Over.mapId_eq]
    rfl
  letI : v.IsContinuous (SmallProetale.topology B S hS)
      (BigProetaleOver.topology B S hS) :=
    smallProetaleToBigProetaleFunctor_isContinuous B
      (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
      (𝟙 (⟨S, hS⟩ : B.Scheme))
  letI : v.IsCocontinuous (SmallProetale.topology B S hS)
      (BigProetaleOver.topology B S hS) :=
    smallProetaleToBigProetaleFunctor_isCocontinuous B
      (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
      (𝟙 (⟨S, hS⟩ : B.Scheme))
  let e' := Functor.sheafPushforwardContinuousIso (eqToIso e) (Type (u + 1))
    (SmallProetale.topology B S hS) (BigProetaleOver.topology B S hS)
  simpa [smallProetaleToBigProetaleMorphism,
    smallProetaleToBigProetaleFunctor,
    bigProetaleToSmallProetaleMorphism] using
    ((v.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
        (Type (u + 1)) (SmallProetale.topology B S hS)
        (BigProetaleOver.topology B S hS)).trans e')

end AlgebraicGeometry.ProEtale

end
