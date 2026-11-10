module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelEtaleSquareCoherence
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemInverseImages
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.InverseImagesOfASingleSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.BiggerSiteGlobalCohomologySupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomologySupplement

/-! # The cocone of direct images along the projections to the vertex, and the system of sheaves

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelEtaleSquareCoherence.lean` proves
the identity and composition laws of the pasted base-change square of Stacks 0EYL's levels, and its
closing section names the one remaining input of Stacks 03Q6's system of sheaves: the pseudofunctor
coherence of `AlgebraicGeometry.smallEtaleBaseChange` along the legs of a cocone of schemes — the
unit and associativity laws of Stacks 021J's comparison, read on sheaves.

This file supplies that, and then assembles the system.

## Main definitions

In the namespace `Stacks.EtaleCohomology.TransitionBaseChange`, for a family of morphisms
`p i : X_i ⟶ V` compatible with the transition morphisms of the stages:

* `projRestrict` — direct image of sheaves along base change for `p i`, from the small étale site
  of `V` to the small étale site of `X_i`. This is the leg at `i` of the cocone of direct images.
* `projSquare` — **the comparison `(X_i ⟶ X_j)_* ⋙ (p_j)_* ≅ (p_i)_*`**, read on sheaves. It is
  restriction along `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`.
* `stageInverseImageTransition` — the transition map of the system `𝒢_i = (p_i)^{-1} ℱ` of inverse
  images of one sheaf on the small étale site of `V`, written in the direct-image direction.
* `levelTransition`, `levelTransitionAb` — the transition map of a system of sheaves on the stages
  carried onto the levels of the site system of Stacks 0EYL by `levelEtaleRestrict`.
* `levelSheafSystem` — a system of abelian sheaves on the stages, carried onto the levels as an
  `InverseSystemOfFiniteSites.AbelianSheafSystem`.
* `levelInverseImageSystem` — the same for the system of inverse images of a single sheaf.
* `coconeProj` — the leg of a cocone on `D`, read in the bounded category of the big étale site,
  with `stageMap_comp_coconeProj` its compatibility with the transitions.

In the namespace `Stacks.EtaleCohomology.AffineLimitCohomology`:

* `levelInverseImageSystem` — **the system of abelian sheaves on the levels of Stacks 0EYL that
  Stacks 03Q6 takes the cohomology of, constructed as the inverse images of a single abelian sheaf
  on the small étale site of the vertex of a cocone**, at the canonical system of Stacks 0EYL.

In the namespace `Stacks.EtaleCohomology.BaseChangeAlgebraSystem`:

* `bcLevelInverseImageSystem` — **the same at the diagram of base changes `Y_i = Z_i ×_T X` and
  the cocone of projections to `X`**: the `F` that the colimit statements of Stacks 03Q6 take as a
  datum. This is the clause of Stacks 03Q6 claimed here.

## Main results

* `projSquare_id_inv_app` and `projSquare_comp_inv_app` — **the two coherence laws of the cocone
  of direct images**, in exactly the `hid`/`hcomp` shape of
  `InverseSystemOfFiniteSites.inverseImageSystem`. They are the sheaf-level readings of
  `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_unit` and
  `..._hom_app_assoc`.
* `stageInverseImageTransition_id` and `stageInverseImageTransition_comp` — the identity and
  composition laws of the transition maps of `𝒢_i`, obtained from the two laws above by
  `CategoryTheory.PushforwardCocone.transitionPushforward_id` and `..._comp`.
* `levelTransition_id` and `levelTransition_comp` — the same after carrying the system onto the
  levels, which is where
  `Stacks.EtaleCohomology.TransitionBaseChange.levelEtaleSquare_id_inv_app`,
  `.levelEtaleSquare_comp_inv_app` and the naturality of `(levelEtaleSquare b).inv` enter.

## Implementation notes

Every isomorphism of sheaves here is restriction along an isomorphism of functors of sites, so
the calculus of `StacksFrontier/CategoryTheory/Sites/PushforwardContinuousCalculus.lean` reduces
each law to an equation of morphisms in the small étale site of `X_i`, and each such equation is
pinned by the projection `CategoryTheory.Limits.pullback.fst` through
`AlgebraicGeometry.SmallEtale.hom_ext_fst`. No new geometry is used: the two site-level equations
are the unit and associativity laws of Stacks 021J proved in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/TransitionBaseChangeCoherence.lean`.

The left adjoints of the legs and their adjunctions are arguments rather than constructed
functors, for the reason given in
`StacksFrontier/CategoryTheory/Sites/InverseSystem/InverseImagesOfASingleSheaf.lean`: a left adjoint
of a direct image is determined only up to isomorphism and each consumer carries its own
representative.

The cocone is presented by the family `p` of legs together with the compatibility `hp`, not as a
`CategoryTheory.Limits.Cocone`: that is the datum the laws use, and `coconeProj` together with
`stageMap_comp_coconeProj` produces it from a cocone on `D`.

No affineness is used for anything in the first three sections, and neither is the limit cone of
`E`. Both enter only in the two specialisations at the end, which are at the canonical system of
Stacks 0EYL and so need its limit cone and the affineness of the levels.

The coefficient universe of the two specialisations is written out as `Ab.{max u v + 1}` rather
than left as a free universe:
`Stacks.WeakSites.ColimitSiteCohomology.systemOfDirectImageMaps` asks for `Ab.{max u₁ v₁ w₁ t}`,
and a free `t` inside that `max` is a universe constraint Lean cannot solve.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)

Tags covered: 03Q6.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology.TransitionBaseChange

universe v' u' v u

open AlgebraicGeometry

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

variable (A : Type u') [Category.{v'} A] {V : B.Scheme}
  (p : ∀ i : E.system.I, B.obj (D.obj (stage E i)) (hD (stage E i)) ⟶ V)

omit [Nonempty I] [IsDirected I (· ≤ ·)] hcont in
/-- **Base change along a leg of the cocone is continuous**, in the spelling the statements below
need. As with `isContinuous_stageBaseChange`, `AlgebraicGeometry.smallEtaleBaseChange_isContinuous`
names the topologies of `(B.obj (D.obj _) _).obj` while the statements here carry
`D.obj (stage E _)`. -/
theorem isContinuous_projBaseChange (i : E.system.I) :
    (AlgebraicGeometry.smallEtaleBaseChange B (p i)).IsContinuous
      (AlgebraicGeometry.SmallEtale.topology B V.obj V.property) (stageTopology E i) :=
  AlgebraicGeometry.smallEtaleBaseChange_isContinuous B (p i)

attribute [local instance] isContinuous_projBaseChange

omit [Nonempty I] [IsDirected I (· ≤ ·)] hcont in
/-- A leg of the cocone followed by base change along a transition morphism is continuous: the
target of the comparison `projSquare`. -/
theorem isContinuous_projBaseChange_comp {i j : E.system.I} (a : i ⟶ j) :
    (AlgebraicGeometry.smallEtaleBaseChange B (p j) ⋙
        AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).IsContinuous
      (AlgebraicGeometry.SmallEtale.topology B V.obj V.property) (stageTopology E i) :=
  Functor.isContinuous_comp _ _ _ (stageTopology E j) _

attribute [local instance] isContinuous_projBaseChange_comp

/-- **Direct image of sheaves along base change for the leg `p i`.** This is the leg at `i` of the
cocone of direct images from the small étale sites of the `X_i` to the small étale site of the
vertex. -/
abbrev projRestrict (i : E.system.I) :
    Sheaf (stageTopology E i) A ⥤
      Sheaf (AlgebraicGeometry.SmallEtale.topology B V.obj V.property) A :=
  (AlgebraicGeometry.smallEtaleBaseChange B (p i)).sheafPushforwardContinuous A
    (AlgebraicGeometry.SmallEtale.topology B V.obj V.property) (stageTopology E i)

variable (hp : ∀ {i j : E.system.I} (a : i ⟶ j), stageMap E a ≫ p j = p i)

/-- **The comparison of the legs of the cocone of direct images with the transitions.** Direct
image along the transition morphism `X_i ⟶ X_j`, followed by the leg at `j`, is the leg at `i`.

This is `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` at the factorisation
`(X_i ⟶ X_j) ≫ (X_j ⟶ V) = (X_i ⟶ V)`, read on sheaves. -/
def projSquare {i j : E.system.I} (a : i ⟶ j) :
    stagePush E A a ⋙ projRestrict E A p j ≅ projRestrict E A p i :=
  Functor.sheafPushforwardContinuousComp'
    (AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso B _ _ _ (stageMap E a) (p j) (p i)
      (hp a)) A (AlgebraicGeometry.SmallEtale.topology B V.obj V.property)
    (stageTopology E j) (stageTopology E i)

omit [Nonempty I] [IsDirected I (· ≤ ·)] hcont in
/-- The presheaf component of the comparison. -/
theorem projSquare_inv_app_hom_app {i j : E.system.I} (a : i ⟶ j)
    (Z : Sheaf (stageTopology E i) A) (Y : (AlgebraicGeometry.SmallEtale B V.obj V.property)ᵒᵖ) :
    ((projSquare E A p hp a).inv.app Z).hom.app Y =
      Z.obj.map ((AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso B _ _ _ (stageMap E a)
        (p j) (p i) (hp a)).hom.app (Opposite.unop Y)).op := by
  rw [projSquare, Functor.sheafPushforwardContinuousComp'_inv_eq,
    Functor.sheafPushforwardContinuousIso_inv_app_hom_app]

omit [Nonempty I] [IsDirected I (· ≤ ·)] hcont in
/-- **The identity law of the cocone of direct images.** At an identity arrow the comparison is,
read across the identity comparison of the direct images along the transition morphisms of schemes,
the identity.

This is `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_unit` read on sheaves. -/
theorem projSquare_id_inv_app (i : E.system.I) (Z : Sheaf (stageTopology E i) A) :
    (projSquare E A p hp (𝟙 i)).inv.app Z =
      (projRestrict E A p i).map ((stagePushIdIso E A i).hom.app Z) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun Y => ?_))
  rw [projSquare_inv_app_hom_app,
    AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_unit B (stageMap E (𝟙 i))
      (stageMap_id E i) (p i) (hp (𝟙 i)) (Opposite.unop Y)]
  exact (stagePushIdIso_hom_app_hom_app E A i Z _).symm

omit [Nonempty I] [IsDirected I (· ≤ ·)] hcont in
/-- **The composition law of the cocone of direct images.** At a composite `a ≫ b` the comparison
is the comparison at `a` followed by the comparison at `b`, read across the composition comparison
of the direct images along the transition morphisms of schemes.

This is `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_assoc` read on sheaves. -/
theorem projSquare_comp_inv_app {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    (Z : Sheaf (stageTopology E i) A) :
    (projSquare E A p hp (a ≫ b)).inv.app Z =
      (projSquare E A p hp a).inv.app Z ≫
        (projSquare E A p hp b).inv.app ((stagePush E A a).obj Z) ≫
          (projRestrict E A p k).map ((stagePushCompIso E A a b).hom.app Z) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun Y => ?_))
  have key := (Iso.eq_inv_comp ((stageCompIso E a b).app _)).2
    (AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_assoc B
      (stageMap E a) (stageMap E b) (p k) (stageMap E (a ≫ b)) (stageMap_comp E a b).symm (p j)
      (hp b) (p i) (hp (a ≫ b)) (hp a) (Opposite.unop Y))
  refine (projSquare_inv_app_hom_app E A p hp (a ≫ b) Z Y).trans ?_
  rw [key, op_comp, op_comp, Functor.map_comp, Functor.map_comp, Category.assoc]
  exact (congrArg₂ (· ≫ ·) (projSquare_inv_app_hom_app E A p hp a Z Y)
    (congrArg₂ (· ≫ ·) (projSquare_inv_app_hom_app E A p hp b _ Y)
      (stagePushCompIso_hom_app_hom_app E A a b Z _))).symm

/-! ### The system of inverse images on the small étale sites of the stages -/

section InverseImages

variable {L : ∀ i : E.system.I,
    Sheaf (AlgebraicGeometry.SmallEtale.topology B V.obj V.property) A ⥤
      Sheaf (stageTopology E i) A}
  (adj : ∀ i : E.system.I, L i ⊣ projRestrict E A p i)
  (𝓕 : Sheaf (AlgebraicGeometry.SmallEtale.topology B V.obj V.property) A)

/-- **The transition map of the system of inverse images `𝒢_i = (p_i)^{-1} ℱ`, in the
direct-image direction.** -/
def stageInverseImageTransition {i j : E.system.I} (a : i ⟶ j) :
    (L j).obj 𝓕 ⟶ (stagePush E A a).obj ((L i).obj 𝓕) :=
  CategoryTheory.PushforwardCocone.transitionPushforward adj (projSquare E A p hp) 𝓕 a

omit [Nonempty I] [IsDirected I (· ≤ ·)] hcont in
/-- **The transition map of `𝒢` at an identity arrow is the canonical identification.** This is
`projSquare_id_inv_app` transposed. -/
theorem stageInverseImageTransition_id (i : E.system.I) :
    stageInverseImageTransition E A p hp adj 𝓕 (𝟙 i) =
      (stagePushIdIso E A i).hom.app ((L i).obj 𝓕) :=
  CategoryTheory.PushforwardCocone.transitionPushforward_id adj (fun i => stagePushIdIso E A i)
    (projSquare E A p hp) (projSquare_id_inv_app E A p hp) 𝓕 i

omit [Nonempty I] [IsDirected I (· ≤ ·)] hcont in
/-- **The transition maps of `𝒢` compose.** This is `projSquare_comp_inv_app` transposed. -/
theorem stageInverseImageTransition_comp {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    stageInverseImageTransition E A p hp adj 𝓕 (a ≫ b) =
      stageInverseImageTransition E A p hp adj 𝓕 b ≫
        (stagePush E A b).map (stageInverseImageTransition E A p hp adj 𝓕 a) ≫
          (stagePushCompIso E A a b).hom.app ((L i).obj 𝓕) :=
  CategoryTheory.PushforwardCocone.transitionPushforward_comp adj
    (fun a b => stagePushCompIso E A a b) (projSquare E A p hp)
    (fun a b Z => projSquare_comp_inv_app E A p hp a b Z) 𝓕 a b

end InverseImages

/-! ### Carrying a system of sheaves on the stages onto the levels -/

section Levels

variable (𝒢 : ∀ i : E.system.I, Sheaf (stageTopology E i) A)
  (ψ : ∀ {i j : E.system.I} (a : i ⟶ j), 𝒢 j ⟶ (stagePush E A a).obj (𝒢 i))

/-- **The transition map of a system of sheaves on the stages, carried onto the levels of the site
system of Stacks 0EYL.** The restriction of the given transition map, followed by the pasted
base-change square `levelEtaleSquare`. -/
def levelTransition {i j : E.system.I} (a : i ⟶ j) :
    (levelEtaleRestrict E A j).obj (𝒢 j) ⟶
      (levelPush E A a).obj ((levelEtaleRestrict E A i).obj (𝒢 i)) :=
  (levelEtaleRestrict E A j).map (ψ a) ≫ (levelEtaleSquare E A a).inv.app (𝒢 i)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **The identity law of the carried transition maps.** This is
`levelEtaleSquare_id_inv_app`. -/
theorem levelTransition_id (hψid : ∀ i : E.system.I, ψ (𝟙 i) = (stagePushIdIso E A i).hom.app (𝒢 i))
    (i : E.system.I) :
    levelTransition E A 𝒢 ψ (𝟙 i) =
      (levelPushIdIso E A i).hom.app ((levelEtaleRestrict E A i).obj (𝒢 i)) := by
  rw [levelTransition, hψid, levelEtaleSquare_id_inv_app E A i (𝒢 i)]

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **The composition law of the carried transition maps.** This is
`levelEtaleSquare_comp_inv_app` together with the naturality of `(levelEtaleSquare b).inv`, and
nothing else. -/
theorem levelTransition_comp
    (hψcomp : ∀ {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k),
      ψ (a ≫ b) = ψ b ≫ (stagePush E A b).map (ψ a) ≫ (stagePushCompIso E A a b).hom.app (𝒢 i))
    {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    levelTransition E A 𝒢 ψ (a ≫ b) =
      levelTransition E A 𝒢 ψ b ≫
        (levelPush E A b).map (levelTransition E A 𝒢 ψ a) ≫
          (levelPushCompIso E A a b).hom.app ((levelEtaleRestrict E A i).obj (𝒢 i)) := by
  simp only [levelTransition, hψcomp a b, Functor.map_comp, Category.assoc,
    levelEtaleSquare_comp_inv_app E A a b (𝒢 i)]
  rw [reassoc_of% (levelEtaleSquare E A b).inv.naturality (ψ a)]

end Levels

/-! ### The system of abelian sheaves on the levels

`Stacks.WeakSites.ColimitSiteCohomology.systemOfDirectImageMaps` asks for its data in the spelling
`abelianSheafPushforward`, `abelianSheafPushforwardIdIso`, `abelianSheafPushforwardCompIso`, which
are `levelPush`, `levelPushIdIso` and `levelPushCompIso` at abelian coefficients — the same terms
up to the `CategoryTheory.Functor.IsContinuous` arguments, which are propositions. The three
restatements below carry out that crossing, each in its own declaration so that no defeq check of
composed restriction functors happens inside a proof.
-/

section AbelianSystem

open InverseSystemOfFiniteSites

variable (𝒢 : ∀ i : E.system.I, Sheaf (stageTopology E i) (Ab.{max u v + 1}))
  (ψ : ∀ {i j : E.system.I} (a : i ⟶ j),
    𝒢 j ⟶ (stagePush E (Ab.{max u v + 1}) a).obj (𝒢 i))

/-- The carried transition map, in the spelling
`Stacks.WeakSites.ColimitSiteCohomology.systemOfDirectImageMaps` asks for. -/
def levelTransitionAb {i j : E.system.I} (a : i ⟶ j) :
    (levelEtaleRestrict E (Ab.{max u v + 1}) j).obj (𝒢 j) ⟶
      (abelianSheafPushforward.{v, v, max v (max u v + 1), max u v + 1} E.system a).obj
        ((levelEtaleRestrict E (Ab.{max u v + 1}) i).obj (𝒢 i)) :=
  levelTransition E (Ab.{max u v + 1}) 𝒢 ψ a

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- `levelTransition_id` in the spelling
`Stacks.WeakSites.ColimitSiteCohomology.systemOfDirectImageMaps` asks for. -/
theorem levelTransitionAb_id
    (hψid : ∀ i : E.system.I,
      ψ (𝟙 i) = (stagePushIdIso E (Ab.{max u v + 1}) i).hom.app (𝒢 i))
    (i : E.system.I) :
    levelTransitionAb E 𝒢 ψ (𝟙 i) =
      (abelianSheafPushforwardIdIso.{v, v, max v (max u v + 1), max u v + 1} E.system i).hom.app
        ((levelEtaleRestrict E (Ab.{max u v + 1}) i).obj (𝒢 i)) :=
  levelTransition_id E (Ab.{max u v + 1}) 𝒢 ψ hψid i

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- `levelTransition_comp` in the spelling
`Stacks.WeakSites.ColimitSiteCohomology.systemOfDirectImageMaps` asks for. -/
theorem levelTransitionAb_comp
    (hψcomp : ∀ {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k),
      ψ (a ≫ b) = ψ b ≫ (stagePush E (Ab.{max u v + 1}) b).map (ψ a) ≫
        (stagePushCompIso E (Ab.{max u v + 1}) a b).hom.app (𝒢 i))
    {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    levelTransitionAb E 𝒢 ψ (a ≫ b) =
      levelTransitionAb E 𝒢 ψ b ≫
        (abelianSheafPushforward.{v, v, max v (max u v + 1), max u v + 1} E.system b).map
            (levelTransitionAb E 𝒢 ψ a) ≫
          (abelianSheafPushforwardCompIso.{v, v, max v (max u v + 1), max u v + 1}
            E.system a b).hom.app
            ((levelEtaleRestrict E (Ab.{max u v + 1}) i).obj (𝒢 i)) :=
  levelTransition_comp E (Ab.{max u v + 1}) 𝒢 ψ hψcomp a b

/-- **A system of abelian sheaves on the stages, carried onto the levels of the site system of
Stacks 0EYL.** The restrictions `levelEtaleRestrict` of the given sheaves, with transition maps
the carried ones, form an `InverseSystemOfFiniteSites.AbelianSheafSystem` on the site system. -/
def levelSheafSystem
    (hψid : ∀ i : E.system.I,
      ψ (𝟙 i) = (stagePushIdIso E (Ab.{max u v + 1}) i).hom.app (𝒢 i))
    (hψcomp : ∀ {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k),
      ψ (a ≫ b) = ψ b ≫ (stagePush E (Ab.{max u v + 1}) b).map (ψ a) ≫
        (stagePushCompIso E (Ab.{max u v + 1}) a b).hom.app (𝒢 i)) :
    AbelianSheafSystem.{v, v, max v (max u v + 1), max u v + 1} E.system :=
  Stacks.WeakSites.ColimitSiteCohomology.systemOfDirectImageMaps.{v, v, max v (max u v + 1),
      max u v + 1} E.system
    (fun i => (levelEtaleRestrict E (Ab.{max u v + 1}) i).obj (𝒢 i))
    (fun a => levelTransitionAb E 𝒢 ψ a)
    (fun i => levelTransitionAb_id E 𝒢 ψ hψid i)
    (fun a b => levelTransitionAb_comp E 𝒢 ψ hψcomp a b)

/-! ### The system of inverse images of a single abelian sheaf, on the levels -/

section InverseImageSystem

variable {L : ∀ i : E.system.I,
    Sheaf (AlgebraicGeometry.SmallEtale.topology B V.obj V.property) (Ab.{max u v + 1}) ⥤
      Sheaf (stageTopology E i) (Ab.{max u v + 1})}
  (adj : ∀ i : E.system.I, L i ⊣ projRestrict E (Ab.{max u v + 1}) p i)

/-- **The system of abelian sheaves of Stacks 03Q6 on the levels of the site system of Stacks
0EYL, constructed as the inverse images of a single sheaf.** For an abelian sheaf `ℱ` on the small
étale site of the vertex of a cocone, the inverse images `𝒢_i = (p_i)^{-1} ℱ`, restricted to the
levels, with their cocycle condition, form an
`InverseSystemOfFiniteSites.AbelianSheafSystem` on the site system — the datum that the colimit
statements of Stacks 03Q6 take as given.

Everything in sight is produced and nothing assumed: the two cocycle conditions of the structure
are the transposes of `projSquare_id_inv_app` and `projSquare_comp_inv_app`, carried onto the
levels by `levelEtaleSquare_id_inv_app`, `levelEtaleSquare_comp_inv_app` and the naturality of
`(levelEtaleSquare b).inv`. -/
def levelInverseImageSystem
    (𝓕 : Sheaf (AlgebraicGeometry.SmallEtale.topology B V.obj V.property) (Ab.{max u v + 1})) :
    AbelianSheafSystem.{v, v, max v (max u v + 1), max u v + 1} E.system :=
  levelSheafSystem E (fun i => (L i).obj 𝓕)
    (fun a => stageInverseImageTransition E (Ab.{max u v + 1}) p hp adj 𝓕 a)
    (fun i => stageInverseImageTransition_id E (Ab.{max u v + 1}) p hp adj 𝓕 i)
    (fun a b => stageInverseImageTransition_comp E (Ab.{max u v + 1}) p hp adj 𝓕 a b)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The sheaf of the system at the level `i` is the restriction to that level of the inverse image
of `ℱ` along the leg `p i`. -/
theorem levelInverseImageSystem_obj
    (𝓕 : Sheaf (AlgebraicGeometry.SmallEtale.topology B V.obj V.property) (Ab.{max u v + 1}))
    (i : E.system.I) :
    (levelInverseImageSystem E p hp adj 𝓕).obj i =
      (levelEtaleRestrict E (Ab.{max u v + 1}) i).obj ((L i).obj 𝓕) :=
  rfl

end InverseImageSystem

end AbelianSystem

/-! ### The legs of a cocone of schemes -/

section CoconeLegs

variable (d : Limits.Cocone D) (hS : B.Contains d.pt)

/-- **The leg of a cocone on `D` at the stage of `i`, read in the bounded category of the big
étale site.** -/
def coconeProj (i : E.system.I) :
    B.obj (D.obj (stage E i)) (hD (stage E i)) ⟶ B.obj d.pt hS :=
  B.inclusion.preimage
    (X := B.obj (D.obj (stage E i)) (hD (stage E i))) (Y := B.obj d.pt hS)
    (d.ι.app (stage E i))

omit [Nonempty I] [IsDirected I (· ≤ ·)] hcont in
/-- The image of `coconeProj E d hS i` under the inclusion of the bounded category is the leg
`d.ι.app (stage E i)` of the cocone. -/
@[simp]
theorem inclusion_map_coconeProj (i : E.system.I) :
    B.inclusion.map (coconeProj E d hS i) = d.ι.app (stage E i) :=
  B.inclusion.map_preimage _

omit [Nonempty I] [IsDirected I (· ≤ ·)] hcont in
/-- **The legs of a cocone are compatible with the transition morphisms of the stages**, which is
the hypothesis `hp` of the comparison `projSquare`. -/
theorem stageMap_comp_coconeProj {i j : E.system.I} (a : i ⟶ j) :
    stageMap E a ≫ coconeProj E d hS j = coconeProj E d hS i := by
  refine B.inclusion.map_injective ?_
  rw [B.inclusion.map_comp, inclusion_map_stageMap, inclusion_map_coconeProj,
    inclusion_map_coconeProj]
  exact d.w (E.indexEquiv.functor.map a)

end CoconeLegs

end Stacks.EtaleCohomology.TransitionBaseChange

namespace Stacks.EtaleCohomology.AffineLimitCohomology

universe v u

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem InverseSystemOfFiniteSites
open Stacks.EtaleCohomology.TransitionBaseChange

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Limits.Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : Limits.IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  (d : Limits.Cocone D) (hS : B.Contains d.pt)

attribute [local instance] isContinuous_levelEtale

variable
  {L : ∀ i : (sys D c B hD hX hc).I,
    Sheaf (AlgebraicGeometry.SmallEtale.topology B d.pt hS) Ab.{max u v + 1} ⥤
      Sheaf (stageTopology (affineEtaleSiteColimit D c B hD hX hc) i) Ab.{max u v + 1}}
  (adj : ∀ i : (sys D c B hD hX hc).I,
    L i ⊣ projRestrict (affineEtaleSiteColimit D c B hD hX hc) Ab.{max u v + 1}
      (coconeProj (affineEtaleSiteColimit D c B hD hX hc) d hS) i)

/-- **The system of abelian sheaves on the levels of the site system of Stacks 0EYL, as the
inverse images of a single sheaf.** For a cocone `d` on the system of schemes — so every `X_i`
carries a morphism `p_i : X_i ⟶ S` to the vertex, compatibly with the transitions — and an abelian
sheaf `ℱ` on the small étale site of `S`, the inverse images `𝒢_i = p_i^{-1} ℱ`, restricted to the
levels, with their cocycle condition, form an `InverseSystemOfFiniteSites.AbelianSheafSystem` on
`Stacks.EtaleCohomology.AffineLimitCohomology.sys`.

This is `Stacks.EtaleCohomology.TransitionBaseChange.levelInverseImageSystem` at the canonical
system of Stacks 0EYL, where `isContinuous_levelEtale` discharges the continuity of the levels
read in the small étale sites. It is the datum the colimit statements of Stacks 03Q6 take as
given: feeding it to them replaces their abstract system of sheaves by the system of inverse
images of one sheaf. -/
def levelInverseImageSystem
    (𝓕 : Sheaf (AlgebraicGeometry.SmallEtale.topology B d.pt hS) Ab.{max u v + 1}) :
    AbelianSheafSystem.{v, v, max v (max u v + 1), max u v + 1} (sys D c B hD hX hc) :=
  TransitionBaseChange.levelInverseImageSystem (affineEtaleSiteColimit D c B hD hX hc)
    (coconeProj (affineEtaleSiteColimit D c B hD hX hc) d hS)
    (stageMap_comp_coconeProj (affineEtaleSiteColimit D c B hD hX hc) d hS) adj 𝓕

/-- The sheaf of the system at the level `i` is the restriction to that level of the inverse image
of `ℱ` along the leg `p i` of the cocone. -/
theorem levelInverseImageSystem_obj
    (𝓕 : Sheaf (AlgebraicGeometry.SmallEtale.topology B d.pt hS) Ab.{max u v + 1})
    (i : (sys D c B hD hX hc).I) :
    (levelInverseImageSystem D c B hD hX hc d hS adj 𝓕).obj i =
      (levelEtaleRestrict (affineEtaleSiteColimit D c B hD hX hc) Ab.{max u v + 1} i).obj
        ((L i).obj 𝓕) :=
  rfl

end Stacks.EtaleCohomology.AffineLimitCohomology

namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem

universe u

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem InverseSystemOfFiniteSites
open Stacks.EtaleCohomology.AffineLimitCohomology
open Stacks.EtaleCohomology.TransitionBaseChange

attribute [local instance] AffineLimitCohomology.isContinuous_levelEtale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (T : AlgebraicGeometry.Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
  [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
  (B : AlgebraicGeometry.BigEtaleSite.{u})
  (hD : ∀ i, B.Contains ((baseChange T X Z).obj i))
  (hY : B.Contains (systemLimitCone T X Z).pt)
  (hXB : B.Contains X.left)

/-- The colimit datum of Stacks 0EYL for the system of base changes, at the canonical limit. -/
abbrev bcColimitDatum :=
  affineEtaleSiteColimit.{u, u} (baseChange T X Z) (systemLimitCone T X Z) B hD hY
    (isLimitSystemLimitCone T X Z)

/-- The projection `Y_i = Z_i ×_T X ⟶ X` at the stage of a level, read in the bounded category of
the big étale site. This is `baseChangeCoconeToX` read through `coconeProj`. -/
abbrev bcProj (i : (sys.{u, u} (baseChange T X Z) (systemLimitCone T X Z) B hD hY
      (isLimitSystemLimitCone T X Z)).I) :
    B.obj ((baseChange T X Z).obj (stage (bcColimitDatum T X Z B hD hY) i))
        (hD (stage (bcColimitDatum T X Z B hD hY) i)) ⟶
      B.obj X.left hXB :=
  coconeProj (bcColimitDatum T X Z B hD hY) (baseChangeCoconeToX T X Z) hXB i

/-- **The system of abelian sheaves of Stacks 03Q6 on the levels of the site system of Stacks
0EYL, constructed as the inverse images of a single sheaf on `X`.** This is the datum that the
colimit statements of Stacks 03Q6 in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/BaseChangeAlgebraSystemCohomology.lean`
and its étale-cohomology counterpart in the same directory take as given: feeding this term to
their `F` replaces their abstract system of sheaves on the levels by the system
`𝒢_i = (Y_i ⟶ X)^{-1} ℱ` of Stacks 03Q6.

It is `Stacks.EtaleCohomology.AffineLimitCohomology.levelInverseImageSystem` at the cocone
`baseChangeCoconeToX` of projections to `X`.

This is a partial form of [Stacks, Tag 03Q6]; the registered statement is
`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`. -/
def bcLevelInverseImageSystem
    {L : ∀ i : (sys.{u, u} (baseChange T X Z) (systemLimitCone T X Z) B hD hY
        (isLimitSystemLimitCone T X Z)).I,
      Sheaf (AlgebraicGeometry.SmallEtale.topology B X.left hXB) Ab.{u + 1} ⥤
        Sheaf (stageTopology (bcColimitDatum T X Z B hD hY) i) Ab.{u + 1}}
    (adj : ∀ i : (sys.{u, u} (baseChange T X Z) (systemLimitCone T X Z) B hD hY
        (isLimitSystemLimitCone T X Z)).I,
      L i ⊣ projRestrict (bcColimitDatum T X Z B hD hY) Ab.{u + 1}
        (bcProj T X Z B hD hY hXB) i)
    (𝓕 : Sheaf (AlgebraicGeometry.SmallEtale.topology B X.left hXB) Ab.{u + 1}) :
    AbelianSheafSystem.{u, u, u + 1, u + 1}
      (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY) :=
  AffineLimitCohomology.levelInverseImageSystem.{u, u} (baseChange T X Z)
    (systemLimitCone T X Z) B hD hY (isLimitSystemLimitCone T X Z)
    (baseChangeCoconeToX T X Z) hXB adj 𝓕

end Stacks.EtaleCohomology.BaseChangeAlgebraSystem

end
