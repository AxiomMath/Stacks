module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom.BaseChange

/-!
# The affine leaf of Stacks 09RI: its stages and its vertex are affine

In Situation 09RH let `g : W₀ ⟶ X₀` be a morphism onto the chosen stage.  The base change of
the situation along `g`, `AlgebraicGeometry.Space.DescentSituation.baseChangeSystem` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom/BaseChange.lean`, is the system
of fibre products `W_i = X_i ×_{X₀} W₀` over `W₀` with vertex `W = X ×_{X₀} W₀`, and its
colimit statement at an *affine* `W₀` is the leaf of the dévissage of Stacks 09RI (the
hypothesis `hleaf` of
`AlgebraicGeometry.Space.DescentSituation.isColim_of_affineBaseChange` in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomUnconditionalAffineReduction.lean`).

This file records the geometry of that leaf: **every stage and the vertex of the base-changed
system are affine algebraic spaces when `W₀` is.**  A stage is affine because the transition
morphism `X_i ⟶ X₀` is affine (the field
`AlgebraicGeometry.Space.DescentSituation.transition_affine` of Situation 09RH) and affineness
of a morphism is stable under base change (Stacks 03WI); the vertex is affine because the
projection `X ⟶ X₀` is affine, which is Stacks 07SF, part (1), and is where the size
hypothesis `#I < B.cutoff.ord.cof` enters.

That is what makes the leaf the place where the source's proof of Stacks 09RI invokes the
scheme-level Stacks 09RE: over an affine `W₀` the whole base-changed system consists of affine
algebraic spaces, so each of its members is representable by an affine object of the site and
carries a ring of global functions.

The same two statements are already in the tree for the base change
`AlgebraicGeometry.Space.DescentSituation.affinePointSituation` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssentialSurjectivityAffineModels.lean`
— `isAffineSpace_affinePointSituation_system` and `isAffineSpace_affinePointSituation_limitCone`,
the inputs of the affine case of Stacks 09RJ — but not for `baseChangeSystem`, which is the
spelling the dévissage of Stacks 09RI runs on, and not in the morphism form below.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.isAffineHom_baseChangeToBase`: the projection
  `W_i ⟶ W₀` is affine.
* `AlgebraicGeometry.Space.DescentSituation.isAffineHom_baseChangeLimitToBase`: the projection
  `W ⟶ W₀` is affine.
* `AlgebraicGeometry.Space.DescentSituation.isAffineSpace_baseChangeStage` and
  `isAffineSpace_baseChangeLimit`: over an affine `W₀` every stage and the vertex of the
  base-changed system are affine.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {W₀ : AlgebraicSpaces B S hS}
  (g : W₀ ⟶ D.stage D.base)

/-- **The projection `W_i = X_i ×_{X₀} W₀ ⟶ W₀` of a base-changed stage is affine.**  It is the
base change of the transition morphism `X_i ⟶ X₀` of Situation 09RH, which is affine, and
affineness of a morphism of algebraic spaces is stable under base change (Stacks 03WI). -/
theorem isAffineHom_baseChangeToBase (i : D.Stages) :
    IsAffineHom B S hS (baseChangeToBase g i).hom :=
  IsAffineHom.of_isPullback (IsPullback.of_hasPullback _ g.hom) (D.transition_affine _)

/-- **The projection `W = X ×_{X₀} W₀ ⟶ W₀` of the base-changed vertex is affine.**  It is the
base change of the projection `X ⟶ X₀` from the limit of Situation 09RH, which is affine by
Stacks 07SF, part (1), under the size hypothesis on the index. -/
theorem isAffineHom_baseChangeLimitToBase (hI : #I < B.cutoff.ord.cof) :
    IsAffineHom B S hS (baseChangeLimitToBase g).hom :=
  IsAffineHom.of_isPullback (IsPullback.of_hasPullback _ g.hom)
    (D.isAffineHom_limitCone_π hI (op D.base))

/-- **Over an affine `W₀` every stage of the base-changed system is an affine algebraic
space.** -/
theorem isAffineSpace_baseChangeStage (hW₀ : IsAffineSpace B S hS W₀.1) (i : D.Stages) :
    IsAffineSpace B S hS (baseChangeStage g i).1 :=
  IsAffineHom.isAffineSpace_source (isAffineHom_baseChangeToBase g i) hW₀

/-- **Over an affine `W₀` the vertex of the base-changed system is an affine algebraic
space.** -/
theorem isAffineSpace_baseChangeLimit (hW₀ : IsAffineSpace B S hS W₀.1)
    (hI : #I < B.cutoff.ord.cof) :
    IsAffineSpace B S hS (baseChangeLimit g).1 :=
  IsAffineHom.isAffineSpace_source (isAffineHom_baseChangeLimitToBase g hI) hW₀

end DescentSituation

end AlgebraicGeometry.Space

end
