module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelEtaleSquareCohomology
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base-change square of Stacks 0EYL's levels, in the library's étale cohomology

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelEtaleSquareCohomology.lean` proves
the index-naturality clause of Stacks 03Q6 as a square of Leray edge morphisms
(`Stacks.EtaleCohomology.TransitionBaseChange.edge_levelEtaleSquare`) between right derived
sections over an object of a level. This file renames those groups as the library's étale
cohomology `Stacks.EtaleCohomology.etaleCohomologyFunctor` of the stages, which is the spelling
the registrations of Stacks 03Q6 use.

Two things are needed for that and are supplied here.

* The direct image along a transition morphism of the stages preserves injective abelian sheaves.
  `edge_levelEtaleSquare` carries this as an instance hypothesis; it is *derived* here, from the
  left exactness of the inverse image on abelian sheaves of the small étale sites
  (`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`, Stacks 04BH) and
  `Stacks.Cohomology.SheafifiedHigherDirectImage.preservesInjectiveObjects_pushforwardOfContinuous`
  (Stacks 015Z). The existing
  `Stacks.EtaleCohomology.smallEtalePushforwardAb_preservesInjectiveObjects` is for the bare
  `Scheme` spelling of the small étale site and does not apply to the `BigEtaleSite`-indexed one
  the colimits development works in, so the left-exactness input is instantiated again at that
  spelling; nothing is restated.
* The renaming itself: restriction to a level followed by sections over an object `V` of the level
  *is* sections over `(levelEtale E i).obj V` on the small étale site of the stage
  (`Stacks.Cohomology.BiggerSiteGlobal.sheafSections_comp_sheafPushforwardContinuous`, an equality
  of functors), so when that object is terminal the right derived functors of the composite are
  the étale cohomology of the stage by
  `Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH`.

## Main results

* `Stacks.EtaleCohomology.TransitionBaseChange.preservesInjectiveObjects_stagePush` — **the direct
  image along a transition morphism of the stages preserves injective abelian sheaves**, in the
  spelling instance search consumes.
* `Stacks.EtaleCohomology.TransitionBaseChange.isTerminal_levelEtale_obj` — the image in the
  small étale site of the stage of a terminal object of a level is terminal, for an **affine**
  stage.
* `Stacks.EtaleCohomology.TransitionBaseChange.sectionsRightDerivedIsoEtaleCohomology` — **the
  renaming.** The right derived functors of restriction-to-the-level followed by sections over `V`
  are `H^p_étale(X_i, -)`, whenever `(levelEtale E i).obj V` is terminal in the small étale site of
  the stage.
* `Stacks.EtaleCohomology.TransitionBaseChange.levelEtaleCohomologyIso` — the comparison between
  the derived sections of a level and the étale cohomology of its stage, **as an isomorphism**: the
  edge morphism of `isIso_edge_levelEtaleRestrict` followed by the renaming.
* `Stacks.EtaleCohomology.TransitionBaseChange.stageEtaleCohomologyMap` — **the transition map on
  the étale cohomology of the stages** determined by a transition `a : i ⟶ j` and a map
  `ψ : 𝒢ⱼ ⟶ (Xᵢ ⟶ Xⱼ)_* 𝒢ᵢ`. The library has no `etaleCohomologyFunctor`-level functoriality in
  this `ψ`-shape — `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` (Stacks 09ZI) is in the
  inverse-image shape `H^q(X, F) ⟶ H^q(Y, i⁻¹F)` — so it is defined here, as the map induced by
  `ψ` followed by the edge morphism of the direct image, read across the renaming.
* `Stacks.EtaleCohomology.TransitionBaseChange.levelEtaleCohomologyIso_naturality` — **the
  index-naturality of Stacks 03Q6 in the étale-cohomology spelling.** The transition map of the
  derived sections of the levels, followed by `levelEtaleCohomologyIso` at the lower index, is
  `levelEtaleCohomologyIso` at the upper index followed by `stageEtaleCohomologyMap`. Since
  `levelEtaleCohomologyIso` is an isomorphism, this makes the object-by-object identification an
  isomorphism of *diagrams* for that comparison.

## What is and is not proved

The comparison whose naturality is proved here is the Leray edge morphism of
`StacksFrontier/Algebra/Homology/RightDerivedEdge.lean`, built from injective resolutions, composed
with `rightDerivedSectionsIsoFunctorH`. The object-by-object identification registered for Stacks
03Q6 uses instead
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCohomologyFunctorIsoEtaleCohomology`, built
from `Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` and so from the
`Ext`-transport of Stacks 015Z along the adjunction `g_! ⊣ g⁻¹`. No declaration in this library
relates the two comparisons.

Half of a relation is available, and is
`Stacks.Cohomology.RightDerivedEdge.edge_app_eq_compRightDerivedNatIso_inv_app` in
`StacksFrontier/Algebra/Homology/RightDerivedEdgeVersusCompositeComparison.lean`: for an exact `P`
preserving injectives the edge morphism is the inverse of
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, which is the engine of
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp`. It is only half, because the `Ext`-side
comparison actually used is `extFunctorObjIsoCompOfIsoOfAcyclic`, whose engine is instead
`ModuleSheafCohomology.extComparisonIso` — the universality of δ-functors of Stacks 010T and 010U,
which this library equips with no computation on an injective resolution and no pinning lemma at
all — and which is read through the degree-split definitions
`ModuleSheafCohomology.extFunctorObjIsoRightDerived` and
`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`, for whose degree-zero and
positive-degree branches this library claims no compatibility (see the implementation note of
`extFunctorObjIsoRightDerived`). Closing that remainder is new homological algebra. So the
naturality below is for the edge comparison and not for that one.

The terminality of `(levelEtale E i).obj V` in the small étale site of the stage is a hypothesis,
not a conclusion: the image of a terminal object of the level is `X_i / X_i`, which is an object of
the *affine* étale site, and it is terminal in the small étale site only when `X_i` is affine
(`AlgebraicGeometry.preservesTerminal_smallAffineEtaleInclusion`). `isTerminal_levelEtale_obj`
discharges it in that case.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.RightDerivedEdge

universe v u

namespace AlgebraicGeometry

/-- **The inverse image on abelian sheaves of the small étale sites of a big étale site is left
exact.** This is `Stacks.EtaleCohomology.smallEtaleAbSheafPullback_preservesFiniteLimits` — Stacks
04BH for the small étale site — at the `BigEtaleSite`-indexed spelling
`AlgebraicGeometry.SmallEtale` of that site, where the general left-exactness statement
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits` applies verbatim: the small étale site
has fibre products and equalizers, base change preserves them, and the left Kan extension along
base change is pointwise. -/
public theorem preservesFiniteLimits_smallEtaleBaseChange_sheafPullback_ab
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) :
    PreservesFiniteLimits
      ((smallEtaleBaseChange B f).sheafPullback Ab.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)) :=
  have : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange B f) Ab.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)) :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1, u, u, u + 1, u + 1}
      (smallEtaleBaseChange B f) (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)
  preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange B f) Ab.{u + 1}
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).symm

/-- **The direct image on abelian sheaves of the small étale sites of a big étale site preserves
injective objects.** It is the right adjoint of the inverse image, which is left exact by
`preservesFiniteLimits_smallEtaleBaseChange_sheafPullback_ab` and in particular preserves
monomorphisms; this is Stacks 015Z in the form
`Stacks.Cohomology.SheafifiedHigherDirectImage.preservesInjectiveObjects_pushforwardOfContinuous`.

`Stacks.EtaleCohomology.smallEtalePushforwardAb_preservesInjectiveObjects` is the same statement
for the bare `Scheme` spelling of the small étale site; the two sites are different categories, so
neither implies the other. -/
@[sga "4½ Arcata 2.3.3"]
public theorem preservesInjectiveObjects_smallEtaleBaseChange_sheafPushforward_ab
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous Ab.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).PreservesInjectiveObjects :=
  have := preservesFiniteLimits_smallEtaleBaseChange_sheafPullback_ab B f
  Stacks.Cohomology.SheafifiedHigherDirectImage.preservesInjectiveObjects_pushforwardOfContinuous
    Ab.{u + 1} (smallEtaleBaseChange B f)

end AlgebraicGeometry

namespace Stacks.EtaleCohomology.TransitionBaseChange

open AlgebraicGeometry
open Stacks.EtaleCohomology.BaseChangeAlgebraSystem

attribute [local instance] hasSheafify_smallEtale enoughInjectives_smallEtale hasExt_smallEtale

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : AlgebraicGeometry.BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  (E : AffineEtaleSiteColimit D c B hD hX)
  [hcont : ∀ i : E.system.I,
    (levelEtale E i).IsContinuous (E.system.J i) (stageTopology E i)]

attribute [local instance] isContinuous_transition isContinuous_stageBaseChange
  isContinuous_transition_comp_levelEtale isContinuous_levelEtale_comp_stageBaseChange
  isContinuous_transition_comp isContinuous_stageBaseChange_comp

/-- **The direct image along a transition morphism of the stages preserves injective abelian
sheaves**, in the spelling instance search consumes. This is
`AlgebraicGeometry.preservesInjectiveObjects_smallEtaleBaseChange_sheafPushforward_ab` at the
transition morphism; the restatement is needed because that statement names the topologies of
`(B.obj (D.obj _) _).obj` while `stageTopology` names those of `D.obj (stage E _)`, which are
definitionally equal but not interchangeable for instance search — exactly as for
`isContinuous_stageBaseChange`.

This discharges the instance hypothesis
`[(stagePush E Ab a).PreservesInjectiveObjects]` of
`Stacks.EtaleCohomology.TransitionBaseChange.edge_levelEtaleSquare`. -/
public theorem preservesInjectiveObjects_stagePush {i j : E.system.I} (a : i ⟶ j) :
    (stagePush E Ab.{max u v + 1} a).PreservesInjectiveObjects :=
  preservesInjectiveObjects_smallEtaleBaseChange_sheafPushforward_ab B (stageMap E a)

/-- **The image in the small étale site of the stage of a terminal object of a level is terminal,
when the stage is affine.** A level is the small *affine* étale site of its stage through the
equivalence of Stacks 0EYL, so the image of its terminal object is `X_i / X_i`; that object is
terminal in the small étale site exactly when it is an object of the affine étale site, which is
what `AlgebraicGeometry.preservesTerminal_smallAffineEtaleInclusion` asks for and what the
affineness of `X_i` supplies.

This is the hypothesis of `sectionsRightDerivedIsoEtaleCohomology` discharged, and the affineness
is not removable: for a non-affine stage the image of a terminal object of the level is not
terminal in the small étale site of the stage, and the derived sections over it are not the étale
cohomology of the stage in any degree. -/
public def isTerminal_levelEtale_obj (i : E.system.I)
    [AlgebraicGeometry.IsAffine (D.obj (stage E i))]
    (V : E.system.C i) (hV : IsTerminal V) : IsTerminal ((levelEtale E i).obj V) :=
  haveI := AlgebraicGeometry.preservesTerminal_smallAffineEtaleInclusion B
    (S := ⟨D.obj (stage E i), hD (stage E i)⟩)
  (hV.isTerminalObj (E.levelEquiv i).functor).isTerminalObj
    (AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj (stage E i)) (hD (stage E i)))

/-! ### The renaming -/

section Renaming

variable (i : E.system.I)
  [HasSheafify (E.system.J i) Ab.{max u v + 1}]
  [HasInjectiveResolutions (Sheaf (E.system.J i) Ab.{max u v + 1})]

/-- **The right derived functors of restriction to a level followed by sections over `V` are the
étale cohomology of the stage**, whenever the image of `V` in the small étale site of the stage is
terminal.

Restriction along a continuous functor followed by sections over `V` *is* sections over the image
of `V` (`Stacks.Cohomology.BiggerSiteGlobal.sheafSections_comp_sheafPushforwardContinuous`, an
equality of functors), so this is
`Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH` on the small étale site of the
stage and nothing else; in particular `Stacks.EtaleCohomology.etaleCohomologyFunctor` is
`CategoryTheory.Sheaf.functorH` of that site by definition.

This is the renaming that `Stacks.EtaleCohomology.TransitionBaseChange.edge_levelEtaleSquare`
needs in order to be read in the spelling the registrations of Stacks 03Q6 use. -/
public def sectionsRightDerivedIsoEtaleCohomology (V : E.system.C i)
    (hV : IsTerminal ((levelEtale E i).obj V)) (p : ℕ) :
    (levelEtaleRestrict E Ab.{max u v + 1} i ⋙
        (sheafSections (E.system.J i) Ab.{max u v + 1}).obj (op V)).rightDerived p ≅
      Stacks.EtaleCohomology.etaleCohomologyFunctor B
        ⟨D.obj (stage E i), hD (stage E i)⟩ p :=
  Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH
    (stageTopology E i) ((levelEtale E i).obj V) hV p

variable [(levelEtaleRestrict E Ab.{max u v + 1} i).IsEquivalence]

/-- **The comparison between the derived sections of a level and the étale cohomology of its
stage is an isomorphism.** It is the edge morphism of
`Stacks.EtaleCohomology.TransitionBaseChange.isIso_edge_levelEtaleRestrict` followed by the
renaming `sectionsRightDerivedIsoEtaleCohomology`.

This is the object-by-object identification of the groups of the cohomology diagram of Stacks
09YQ with étale cohomology groups of the stages, for the edge comparison; its naturality in the
index is `levelEtaleCohomologyIso_naturality`. -/
public def levelEtaleCohomologyIso (V : E.system.C i)
    (hV : IsTerminal ((levelEtale E i).obj V)) (p : ℕ)
    (M : Sheaf (stageTopology E i) Ab.{max u v + 1}) :
    ((((sheafSections (E.system.J i) Ab.{max u v + 1}).obj (op V)).rightDerived p).obj
        ((levelEtaleRestrict E Ab.{max u v + 1} i).obj M)) ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B
        ⟨D.obj (stage E i), hD (stage E i)⟩ p).obj M :=
  haveI := isIso_edge_levelEtaleRestrict E i
    ((sheafSections (E.system.J i) Ab.{max u v + 1}).obj (op V)) p M
  asIso ((edge (levelEtaleRestrict E Ab.{max u v + 1} i)
      ((sheafSections (E.system.J i) Ab.{max u v + 1}).obj (op V)) p).app M) ≪≫
    (sectionsRightDerivedIsoEtaleCohomology E i V hV p).app M

/-- The forward map of `levelEtaleCohomologyIso` is the edge morphism of the restriction to the
level followed by the forward map of `sectionsRightDerivedIsoEtaleCohomology`. -/
@[simp]
public theorem levelEtaleCohomologyIso_hom (V : E.system.C i)
    (hV : IsTerminal ((levelEtale E i).obj V)) (p : ℕ)
    (M : Sheaf (stageTopology E i) Ab.{max u v + 1}) :
    (levelEtaleCohomologyIso E i V hV p M).hom =
      (edge (levelEtaleRestrict E Ab.{max u v + 1} i)
          ((sheafSections (E.system.J i) Ab.{max u v + 1}).obj (op V)) p).app M ≫
        (sectionsRightDerivedIsoEtaleCohomology E i V hV p).hom.app M :=
  rfl

end Renaming

/-! ### The square, in the étale-cohomology spelling -/

section Square

variable {i j : E.system.I} (a : i ⟶ j)
  [HasSheafify (E.system.J i) Ab.{max u v + 1}] [HasSheafify (E.system.J j) Ab.{max u v + 1}]
  [HasInjectiveResolutions (Sheaf (E.system.J i) Ab.{max u v + 1})]
  [HasInjectiveResolutions (Sheaf (E.system.J j) Ab.{max u v + 1})]
  [(levelPush E Ab.{max u v + 1} a).PreservesInjectiveObjects]
  [(levelEtaleRestrict E Ab.{max u v + 1} i).PreservesInjectiveObjects]
  [(levelEtaleRestrict E Ab.{max u v + 1} j).PreservesInjectiveObjects]

attribute [local instance] preservesInjectiveObjects_stagePush

/-- `sectionsRightDerivedIsoEtaleCohomology` at the transition image of `V`, written at the
spelling the square of
`Stacks.EtaleCohomology.TransitionBaseChange.edge_levelEtaleSquare` produces: restriction to the
level `i`, then direct image along the transition of `a`, then sections over `V`. Direct image
along a continuous functor followed by sections over `V` is sections over the image of `V`
(`Stacks.Cohomology.BiggerSiteGlobal.sheafSections_comp_sheafPushforwardContinuous`), so the two
functors are the same; they are not the same *term*, and the crossing is isolated here rather than
inside a proof. -/
public def transitionSectionsRightDerivedIsoEtaleCohomology (V : E.system.C j)
    (hV' : IsTerminal ((levelEtale E i).obj ((E.system.u a).obj V))) (p : ℕ) :
    (levelEtaleRestrict E Ab.{max u v + 1} i ⋙ levelPush E Ab.{max u v + 1} a ⋙
        (sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)).rightDerived p ≅
      Stacks.EtaleCohomology.etaleCohomologyFunctor B
        ⟨D.obj (stage E i), hD (stage E i)⟩ p :=
  sectionsRightDerivedIsoEtaleCohomology E i ((E.system.u a).obj V) hV' p

/-- **The transition map on the étale cohomology of the stages.** For `a : i ⟶ j`, abelian sheaves
`𝒢ᵢ` and `𝒢ⱼ` on the small étale sites of the two stages and `ψ : 𝒢ⱼ ⟶ (Xᵢ ⟶ Xⱼ)_* 𝒢ᵢ`, this is
the map `H^p_étale(Xⱼ, 𝒢ⱼ) ⟶ H^p_étale(Xᵢ, 𝒢ᵢ)` induced by `ψ`: the map `ψ` induces on derived
sections, followed by the Leray edge morphism of the direct image along the transition morphism of
schemes, read across the pasted base-change square `levelEtaleSquare` and the renamings of both
ends.

The library has no `Stacks.EtaleCohomology.etaleCohomologyFunctor`-level functoriality in this
`ψ`-shape: `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` (Stacks 09ZI) is the
inverse-image shape `H^q(X, F) ⟶ H^q(Y, i⁻¹F)`, and
`Stacks.EtaleCohomology.ProperBaseChange.etaleCohomologyEndo` is a self-map of one scheme. So the
map is defined here. -/
public def stageEtaleCohomologyMap
    (𝒢i : Sheaf (stageTopology E i) Ab.{max u v + 1})
    (𝒢j : Sheaf (stageTopology E j) Ab.{max u v + 1})
    (ψ : 𝒢j ⟶ (stagePush E Ab.{max u v + 1} a).obj 𝒢i)
    (V : E.system.C j) (hV : IsTerminal ((levelEtale E j).obj V))
    (hV' : IsTerminal ((levelEtale E i).obj ((E.system.u a).obj V))) (p : ℕ) :
    (Stacks.EtaleCohomology.etaleCohomologyFunctor B
        ⟨D.obj (stage E j), hD (stage E j)⟩ p).obj 𝒢j ⟶
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B
        ⟨D.obj (stage E i), hD (stage E i)⟩ p).obj 𝒢i :=
  (sectionsRightDerivedIsoEtaleCohomology E j V hV p).inv.app 𝒢j ≫
    (((levelEtaleRestrict E Ab.{max u v + 1} j ⋙
        (sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)).rightDerived p).map ψ) ≫
      (edge (stagePush E Ab.{max u v + 1} a)
          (levelEtaleRestrict E Ab.{max u v + 1} j ⋙
            (sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p).app 𝒢i ≫
        (NatTrans.rightDerived (Functor.whiskerRight
            (levelEtaleSquare E Ab.{max u v + 1} a).inv
            ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V))) p).app 𝒢i ≫
          (transitionSectionsRightDerivedIsoEtaleCohomology E a V hV' p).hom.app 𝒢i

/-- **The index-naturality clause of Stacks 03Q6, in the étale-cohomology spelling.** The
transition map of the derived sections of the levels — which is the transition map of the
cohomology diagram of Stacks 09YP, by
`Stacks.WeakSites.ColimitSiteCohomology.CohomologyCocone.diagram_map_eq_edge_app` — followed by
the comparison with the étale cohomology of the stage at the lower index, is the comparison at the
upper index followed by `stageEtaleCohomologyMap`.

Since the comparison `levelEtaleCohomologyIso` is an isomorphism, this says that the
object-by-object identification of the groups of the cohomology diagram with the étale cohomology
groups of the stages is an isomorphism of *diagrams* — for the edge comparison. It is
`edge_levelEtaleSquare` with both ends renamed by
`sectionsRightDerivedIsoEtaleCohomology`; no new homological algebra enters. -/
public theorem levelEtaleCohomologyIso_naturality
    (𝒢i : Sheaf (stageTopology E i) Ab.{max u v + 1})
    (𝒢j : Sheaf (stageTopology E j) Ab.{max u v + 1})
    (ψ : 𝒢j ⟶ (stagePush E Ab.{max u v + 1} a).obj 𝒢i)
    (V : E.system.C j) (hV : IsTerminal ((levelEtale E j).obj V))
    (hV' : IsTerminal ((levelEtale E i).obj ((E.system.u a).obj V))) (p : ℕ) :
    ((((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)).rightDerived p).map
          ((levelEtaleRestrict E Ab.{max u v + 1} j).map ψ ≫
            (levelEtaleSquare E Ab.{max u v + 1} a).inv.app 𝒢i)) ≫
        (edge (levelPush E Ab.{max u v + 1} a)
            ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p).app
          ((levelEtaleRestrict E Ab.{max u v + 1} i).obj 𝒢i) ≫
          (edge (levelEtaleRestrict E Ab.{max u v + 1} i)
              (levelPush E Ab.{max u v + 1} a ⋙
                (sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p).app 𝒢i ≫
            (transitionSectionsRightDerivedIsoEtaleCohomology E a V hV' p).hom.app 𝒢i =
      ((edge (levelEtaleRestrict E Ab.{max u v + 1} j)
            ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p).app 𝒢j ≫
          (sectionsRightDerivedIsoEtaleCohomology E j V hV p).hom.app 𝒢j) ≫
        stageEtaleCohomologyMap E a 𝒢i 𝒢j ψ V hV hV' p := by
  have h := congrArg
    (fun z => z ≫ (transitionSectionsRightDerivedIsoEtaleCohomology E a V hV' p).hom.app 𝒢i)
    (edge_levelEtaleSquare E a 𝒢i 𝒢j ψ V p)
  rw [stageEtaleCohomologyMap]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simpa only [Category.assoc] using h

end Square

end Stacks.EtaleCohomology.TransitionBaseChange

end
