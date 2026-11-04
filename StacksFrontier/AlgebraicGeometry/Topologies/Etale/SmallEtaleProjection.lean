module

public import Mathlib.CategoryTheory.Functor.Flat
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.LeftKanExtensionExactness
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# The small étale topos as a retract of the big étale topos

For a scheme `S` in a big étale site, the inclusion of its small étale site into the big étale
slice over `S` is a morphism of sites in the *opposite* direction: it is continuous with an
exact left adjoint. It therefore defines a projection of topoi

`π_S : Sh((Sch/S)_ét) ⟶ Sh(S_ét)`

and the geometric morphism `i_S` of the previous section — the one attached to the identity of
`S` — is a section of it. Consequently inverse image along `i_S` is nothing but restriction to
the small étale site, that is, direct image along `π_S`.

So the small étale topos sits inside the big one as a retract, and sheaf cohomology computed on
the small site agrees with the restriction of the big-site computation.

## Main definitions

* `AlgebraicGeometry.bigEtaleToSmallEtaleMorphism` — the projection `π_S` from the big étale
  topos over `S` to its small étale topos.

## Main results

* `AlgebraicGeometry.smallEtaleInclusion_isMorphismOfSites` — the small-site inclusion is a
  morphism of sites.
* `AlgebraicGeometry.projectionCompInclusionPushforwardIso` — `π_S ∘ i_S` is naturally the
  identity of the small étale topos, so `i_S` is a section of `π_S`.
* `AlgebraicGeometry.inclusionInverseImageIsoProjectionPushforward` — inverse image along
  `i_S` is naturally restriction to the small étale site.

## Implementation notes

The small-site inclusion is the full-subcategory inclusion, so its fullness and faithfulness
come for free. The geometric inclusion `i_S` is literally the morphism `i_{𝟙_S}` of the
preceding section rather than a second copy of it; `Over.mapId_eq` is what identifies the two
functors, and the isomorphisms of functors below express equality of geometric morphisms up to
the canonical natural identifications.

Being a morphism of sites needs an exact left adjoint for the inclusion, which is where the
work is. The left adjoint is the sheaf pullback, and its exactness is reduced to left exactness
of the presheaf-level left Kan extension. That in turn holds because, the inclusion being
representably flat, each comma category `CostructuredArrow` is filtered, so the Kan extension
is a filtered colimit of representables, evaluated pointwise — and filtered colimits of types
commute with finite limits. `lanEvaluationIsoColimit` is that pointwise description.

Representable flatness itself follows from the inclusion preserving finite limits, which holds
because the small étale category has a final object and fibre products and the inclusion
preserves both.

## References

* [Stacks Project, Lemma 34.4.4 (Tag 021G)](https://stacks.math.columbia.edu/tag/021G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private theorem smallEtaleInclusion_lan_preservesFiniteLimits
    [RepresentablyFlat (SmallEtale.inclusion B S hS)] :
    PreservesFiniteLimits ((SmallEtale.inclusion B S hS).op.lan :
      ((SmallEtale B S hS)ᵒᵖ ⥤ Type (u + 1)) ⥤
        (BigEtaleOver B S hS)ᵒᵖ ⥤ Type (u + 1)) := by
  let F := (SmallEtale.inclusion B S hS).op
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
  intro I _ _
  apply preservesLimitsOfShape_of_evaluation _ I
  intro Y
  have : IsFiltered (CostructuredArrow F Y) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (SmallEtale.inclusion B S hS) Y.unop)
  exact preservesLimitsOfShape_of_natIso
    (lanEvaluationIsoColimit (Type (u + 1)) F Y).symm

/-- The full inclusion of the small étale site defines a morphism of sites
from the big étale slice to the small étale site. -/
@[stacks 021G "the morphism of sites"]
public instance smallEtaleInclusion_isMorphismOfSites :
    _root_.IsMorphismOfSites.{u + 1} (SmallEtale.inclusion B S hS)
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS) := by
  let v := smallEtaleToBigEtaleFunctor B (B.obj S hS) (B.obj S hS)
    (𝟙 (B.obj S hS))
  have e : v = SmallEtale.inclusion B S hS := by
    dsimp [v, smallEtaleToBigEtaleFunctor]
    rw [Over.mapId_eq]
    rfl
  have : (SmallEtale.inclusion B S hS).IsContinuous
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS) := by
    exact e ▸ (smallEtaleToBigEtaleFunctor_isContinuous B
      (B.obj S hS) (B.obj S hS) (𝟙 (B.obj S hS)))
  have : HasPullbacks (SmallEtale B S hS) := inferInstance
  have hterm : IsTerminal ((SmallEtale.inclusion B S hS).obj
      (SmallEtale.final B S hS)) := by
    simpa [SmallEtale.inclusion, SmallEtale.final] using
      (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj S hS))))
  have : HasTerminal (SmallEtale B S hS) :=
    (SmallEtale.finalIsTerminal B S hS).hasTerminal
  have : HasFiniteLimits (SmallEtale B S hS) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SmallEtale.inclusion B S hS) :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal
      (SmallEtale.inclusion B S hS)
      (SmallEtale.finalIsTerminal B S hS) hterm
  have : PreservesFiniteLimits (SmallEtale.inclusion B S hS) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks (SmallEtale.inclusion B S hS)
  have : RepresentablyFlat (SmallEtale.inclusion B S hS) :=
    flat_of_preservesFiniteLimits (SmallEtale.inclusion B S hS)
  have : (SmallEtale.inclusion B S hS).sheafPushforwardContinuous
      (Type (u + 1)) (SmallEtale.topology B S hS)
      (BigEtaleOver.topology B S hS) |>.IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (SmallEtale.inclusion B S hS) (Type (u + 1))
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)).isRightAdjoint
  have : PreservesFiniteLimits ((SmallEtale.inclusion B S hS).op.lan :
      ((SmallEtale B S hS)ᵒᵖ ⥤ Type (u + 1)) ⥤
        (BigEtaleOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
    smallEtaleInclusion_lan_preservesFiniteLimits B S hS
  refine { toIsContinuous := inferInstance, hasExactLeftAdjoint := ?_ }
  let L := (SmallEtale.inclusion B S hS).sheafPullback (Type (u + 1))
    (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
  refine ⟨L, ?_, ?_⟩
  · exact ⟨(SmallEtale.inclusion B S hS).sheafAdjunctionContinuous
      (Type (u + 1))
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)⟩
  · exact Functor.sheafPullbackConstruction.preservesFiniteLimits
      (SmallEtale.inclusion B S hS) (Type (u + 1))
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)

/-- The geometric morphism `π_S` associated to the inclusion of the small
étale site into the big étale slice. -/
@[stacks 021G "the projection of topoi"]
public noncomputable def bigEtaleToSmallEtaleMorphism :
    MorphismOfTopoi
      (Sheaf (BigEtaleOver.topology B S hS) (Type (u + 1)))
      (Sheaf (SmallEtale.topology B S hS) (Type (u + 1))) :=
  let h := smallEtaleInclusion_isMorphismOfSites B S hS
  have := h.toIsContinuous
  let L := Classical.choose h.hasExactLeftAdjoint
  let hL := Classical.choose_spec h.hasExactLeftAdjoint
  { pushforward := (SmallEtale.inclusion B S hS).sheafPushforwardContinuous
      (Type (u + 1)) (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
    inverseImage := L
    adj := Classical.choice hL.1
    preservesFiniteLimits := hL.2 }

/-- The composite `π_S ∘ i_S` is naturally the identity of the small étale
topos, where `i_S` is the geometric morphism attached to `𝟙_S`. -/
@[stacks 021G "the section property"]
public noncomputable def projectionCompInclusionPushforwardIso :
    (smallEtaleToBigEtaleMorphism B (B.obj S hS) (B.obj S hS)
        (𝟙 (B.obj S hS))).pushforward ⋙
      (bigEtaleToSmallEtaleMorphism B S hS).pushforward ≅
        𝟭 (Sheaf (SmallEtale.topology B S hS) (Type (u + 1))) := by
  let v := smallEtaleToBigEtaleFunctor B (B.obj S hS) (B.obj S hS)
    (𝟙 (B.obj S hS))
  have e : v = SmallEtale.inclusion B S hS := by
    dsimp [v, smallEtaleToBigEtaleFunctor]
    rw [Over.mapId_eq]
    rfl
  have : v.IsContinuous (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS) :=
    smallEtaleToBigEtaleFunctor_isContinuous B
      (B.obj S hS) (B.obj S hS) (𝟙 (B.obj S hS))
  have : v.IsCocontinuous (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS) :=
    smallEtaleToBigEtaleFunctor_isCocontinuous B
      (B.obj S hS) (B.obj S hS) (𝟙 (B.obj S hS))
  have : v.Full := by
    dsimp [v, smallEtaleToBigEtaleFunctor]
    infer_instance
  have : v.Faithful := by
    dsimp [v, smallEtaleToBigEtaleFunctor]
    infer_instance
  have : ∀ F : (SmallEtale B S hS)ᵒᵖ ⥤ Type (u + 1),
      v.op.HasPointwiseRightKanExtension F := by
    intro F
    infer_instance
  have : IsIso (v.sheafAdjunctionCocontinuous (Type (u + 1))
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)).counit :=
    Functor.isIso_sheafAdjunctionCocontinuous_counit v (Type (u + 1))
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
  let e' := Functor.sheafPushforwardContinuousIso (eqToIso e) (Type (u + 1))
    (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
  simpa [smallEtaleToBigEtaleMorphism,
    smallEtaleToBigEtaleFunctor, bigEtaleToSmallEtaleMorphism] using
    ((Functor.isoWhiskerLeft
      (v.sheafPushforwardCocontinuous (Type (u + 1))
        (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)) e'.symm).trans
      (asIso (v.sheafAdjunctionCocontinuous (Type (u + 1))
        (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)).counit))

/-- Inverse image along `i_S` is naturally restriction to the small étale
site, equivalently direct image along `π_S`. -/
@[stacks 021G "inverse image is restriction",
  stacks 04BT "restriction to the small étale site, i.e. `i_S^{-1} = π_{S,*}`"]
public noncomputable def inclusionInverseImageIsoProjectionPushforward :
    (smallEtaleToBigEtaleMorphism B (B.obj S hS) (B.obj S hS)
        (𝟙 (B.obj S hS))).inverseImage ≅
      (bigEtaleToSmallEtaleMorphism B S hS).pushforward := by
  let v := smallEtaleToBigEtaleFunctor B (B.obj S hS) (B.obj S hS)
    (𝟙 (B.obj S hS))
  have e : v = SmallEtale.inclusion B S hS := by
    dsimp [v, smallEtaleToBigEtaleFunctor]
    rw [Over.mapId_eq]
    rfl
  have : v.IsContinuous (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS) :=
    smallEtaleToBigEtaleFunctor_isContinuous B
      (B.obj S hS) (B.obj S hS) (𝟙 (B.obj S hS))
  have : v.IsCocontinuous (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS) :=
    smallEtaleToBigEtaleFunctor_isCocontinuous B
      (B.obj S hS) (B.obj S hS) (𝟙 (B.obj S hS))
  let e' := Functor.sheafPushforwardContinuousIso (eqToIso e) (Type (u + 1))
    (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
  simpa [smallEtaleToBigEtaleMorphism,
    smallEtaleToBigEtaleFunctor, bigEtaleToSmallEtaleMorphism] using
    ((v.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
        (Type (u + 1)) (SmallEtale.topology B S hS)
        (BigEtaleOver.topology B S hS)).trans e')

end AlgebraicGeometry
