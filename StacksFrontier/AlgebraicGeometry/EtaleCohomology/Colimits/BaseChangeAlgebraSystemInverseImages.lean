module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSystem

/-!
# The system of sheaves of Stacks 03Q6, constructed as inverse images of one sheaf

Stacks 03Q6 does not take an arbitrary system of abelian sheaves on the levels
`Y_i = Z_i ×_T X` of the system of base changes: it takes `𝒢_i = (Y_i ⟶ X)^{-1} ℱ` for a single
abelian sheaf `ℱ` on `X`. This file constructs that system.

The levels of the system of base changes come with projections `Y_i ⟶ X`, compatible with the
transitions, because the system is built inside the category of schemes over `X`: it is
`(Z ⋙ Over.pullback X.hom) ⋙ Over.forget X.left`, so the structure morphisms of the over-objects
assemble into a cocone on `baseChange T X Z` with vertex `X`. Feeding that cocone to
`Stacks.EtaleCohomology.inverseImageSystem` gives the system of inverse images.

## Main definitions

* `baseChangeCoconeToX` — the cocone on the system of base changes with vertex `X`, whose legs
  are the projections `Y_i = Z_i ×_T X ⟶ X`.
* `baseChangeInverseImageSystem` — **the system `𝒢_i = (Y_i ⟶ X)^{-1} ℱ` of Stacks 03Q6,
  constructed from a single abelian sheaf `ℱ` on `X`.**

## Implementation notes

No affineness is used here, of `X` or of anything else, and the index is only a preordered type:
the construction is the one Stacks 0EZL describes, run at the cocone of projections.

The system lands on the **small étale** sites of the levels, which is where the inverse image of
abelian sheaves exists without hypotheses. The colimit statement of Stacks 03Q6 in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/BaseChangeAlgebraSystemCohomology.lean`
takes instead an `InverseSystemOfFiniteSites.AbelianSheafSystem` on the levels of the site system
of Stacks 0EYL, which are small models of the small *affine* étale sites of the `Y_i`. The
transport of this system onto those levels is
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.bcLevelInverseImageSystem` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/StageProjectionBaseChangeCoherence.lean`.
It is assembled from:

1. **Base change on the small affine étale site**, for affine `S` and `T`:
   `AlgebraicGeometry.smallAffineEtaleBaseChange`, its continuity
   `AlgebraicGeometry.smallAffineEtaleBaseChange_isContinuous` and its pseudofunctoriality
   `AlgebraicGeometry.smallAffineEtaleBaseChangeId` and
   `AlgebraicGeometry.smallAffineEtaleBaseChangeComp`.
2. **The identification of the transition functor with base change**, on the small étale site
   (the small affine étale site is a dense subsite of it):
   `Stacks.EtaleCohomology.TransitionBaseChange.transitionIso`, with its coherence laws
   `Stacks.EtaleCohomology.TransitionBaseChange.transitionIso_id_hom_app` and
   `.transitionIso_comp_hom_app` in
   `StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/TransitionBaseChangeCoherence.lean`.
3. **The passage to the small étale site of `X`** through the level equivalence
   (`AffineLimitCohomology.restrictToLevel`), the affine-to-étale equivalence of Stacks 04HR
   (`BaseChangeAlgebraSystem.restrictToAffineEtale`) and the comparison of the bounded small
   étale site with Mathlib's (`AlgebraicGeometry.SmallEtale.sheafEquiv`), each commuting with
   base change: `AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`,
   `Stacks.EtaleCohomology.AffineLimitCohomology.levelPushforwardBaseChangeIso` and
   `AlgebraicGeometry.SmallAffineEtale.inclusionPushforwardBaseChangeIso` in
   `StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelBaseChangeComparison.lean`, with
   the identity and composition laws of their pasting, `levelEtaleSquare_id_inv_app` and
   `levelEtaleSquare_comp_inv_app`, in `LevelEtaleSquareCoherence.lean`.
4. **The pseudofunctor coherence of `AlgebraicGeometry.smallEtaleBaseChange`** along the
   projections `Y_i ⟶ X`, the unit and associativity laws of Stacks 021J's
   `AlgebraicGeometry.smallEtaleBaseChange_compIso` read on sheaves:
   `Stacks.EtaleCohomology.TransitionBaseChange.projSquare_id_inv_app` and
   `.projSquare_comp_inv_app`.

The left adjoints of the direct images along the projections and their adjunctions remain
arguments there, as everywhere in this development.

## References

* [Stacks 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem

open Stacks.EtaleCohomology

variable {I : Type u} [Preorder I] (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)

/-- **The cocone on the system of base changes with vertex `X`.** The system of base changes is
built inside the category of schemes over `X`, so the structure morphisms of its levels —
the projections `Y_i = Z_i ×_T X ⟶ X` — are compatible with the transition morphisms and form a
cocone. -/
def baseChangeCoconeToX : Cocone (baseChange T X Z) :=
  Limits.Cocone.whisker (Z ⋙ Over.pullback X.hom) (Over.forgetCocone X.left)

/-- The vertex of `baseChangeCoconeToX` is `X`. -/
theorem baseChangeCoconeToX_pt : (baseChangeCoconeToX T X Z).pt = X.left := rfl

/-- The leg of `baseChangeCoconeToX` at `i` is the projection `Z_i ×_T X ⟶ X`. -/
theorem baseChangeCoconeToX_ι_app (i : Iᵒᵖ) :
    (baseChangeCoconeToX T X Z).ι.app i = Limits.pullback.snd (Z.obj i).hom X.hom :=
  rfl

/-- **The system of sheaves of Stacks 03Q6, constructed.** For a single abelian sheaf `ℱ` on the
small étale site of `X`, the inverse images `𝒢_i = (Y_i ⟶ X)^{-1} ℱ` along the projections of the
system of base changes, together with the cocycle condition, form a system of sheaves on
`baseChange T X Z` in the sense of Stacks 0EZL. This is the system the source of Stacks 03Q6
takes its cohomology of.

No affineness of `X`, of `T` or of the `Z_i` is used.

This is a partial form of [Stacks, Tag 03Q6]; the registered statement is
`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`. -/
def baseChangeInverseImageSystem (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    EtaleSheafSystem (baseChange T X Z) Ab.{u + 1} :=
  inverseImageSystem (baseChange T X Z) (baseChangeCoconeToX T X Z) F

/-- The sheaf of `baseChangeInverseImageSystem` at the level `i` is the inverse image of `ℱ`
along the projection `Y_i ⟶ X`. -/
theorem baseChangeInverseImageSystem_obj
    (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) (i : Iᵒᵖ) :
    (baseChangeInverseImageSystem T X Z F).obj i =
      (smallEtalePullbackAb (Limits.pullback.snd (Z.obj i).hom X.hom)).obj F :=
  rfl

end Stacks.EtaleCohomology.BaseChangeAlgebraSystem

end
