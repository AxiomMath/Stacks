module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelBaseChangeComparison
public import StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus

/-! # The identity and composition laws of the base-change square of Stacks 0EYL's levels

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelBaseChangeComparison.lean` separates
a level of the site system of Stacks 0EYL from the small étale site of the scheme `X_i` it sits
over by *two* comparisons: the level equivalence of Stacks 0EYL and the affine inclusion of Stacks
04HR, each compatible with base change. Its closing section records that the two compatibilities
have no identity or composition law, and that without those the system of inverse images of a
single sheaf cannot be assembled.

This file supplies the law — for the **pasting** of the two, which is where it is cheap.
Restriction along a composite of functors of sites is the
composite of the restrictions on the nose (`CategoryTheory.Functor.sheafPushforwardContinuousComp`
is `CategoryTheory.Iso.refl`), and the level of the system sits in the small étale site of `X_i`
by the single functor `Stacks.EtaleCohomology.TransitionBaseChange.levelEtale`, which *is* the
level equivalence followed by the affine inclusion. So the pasting of the two squares of direct
images is restriction along the one site-level comparison
`Stacks.EtaleCohomology.TransitionBaseChange.transitionIso`, whose identity and composition laws
are `transitionIso_id_hom_app` and `transitionIso_comp_hom_app`, already available.

## Main definitions

In the namespace `Stacks.EtaleCohomology.TransitionBaseChange`:

* `levelEtaleRestrict` — restriction of sheaves from the small étale site of `X_i` to the level
  `i`. By `levelEtaleRestrict_eq` it is the affine restriction of Stacks 04HR followed by the
  level restriction of Stacks 0EYL, on the nose.
* `levelEtaleSquare` — **the pasted square of direct images**: restriction to the level `i`
  followed by direct image along the transition of `a : i ⟶ j` is direct image along base change
  in the small étale site followed by restriction to the level `j`.
* `levelPushIdIso`, `levelPushCompIso` — the identity and composition comparisons of the direct
  images along the transitions of the system, in the spelling
  `InverseSystemOfFiniteSites.abelianSheafPushforwardIdIso` and `...CompIso` have at an arbitrary
  coefficient category.
* `stagePushIdIso`, `stagePushCompIso` — the same for the direct images along the transition
  morphisms `X_i ⟶ X_j` of schemes.

## Main results

* `levelEtaleSquare_id_inv_app` — **the identity law.** At an identity arrow the square is, read
  across the two identity comparisons, the identity.
* `levelEtaleSquare_comp_inv_app` — **the composition law.** At a composite `a ≫ b` the square is
  the pasting of the squares at `a` and at `b`, read across the two composition comparisons.

These are the two laws whose absence the closing section of `LevelBaseChangeComparison.lean`
names, in the shape in which a transport of a system of sheaves across the square consumes them:
each says that one leg of the square, composed with the identity resp. composition comparison of
the direct images on the other side, is the identity resp. composition comparison on this side —
the same shape as the `hid` and `hcomp` of
`Stacks.WeakSites.ColimitSiteCohomology.systemOfDirectImageMaps`.

## Implementation notes

Every isomorphism in sight is restriction along an isomorphism of functors of sites, so the
calculus of `StacksFrontier/CategoryTheory/Sites/PushforwardContinuousCalculus.lean` applies: the
component of `CategoryTheory.Functor.sheafPushforwardContinuousIso e` at a sheaf `M` and an object
`Y` is `M.obj.map (e.inv.app Y).op`. Both laws are therefore proved componentwise on presheaves,
where they are the functorial image under `M.obj` of the site-level laws of `transitionIso`; no
sheaf-level coherence is reproved.

The continuity of `levelEtale` is taken as an instance hypothesis rather than derived, because
`Stacks.EtaleCohomology.AffineEtaleSiteColimit` carries its level equivalences as equivalences of
*categories* — that they are equivalences of *sites* is
`Stacks.EtaleCohomology.AffineLimitCohomology.isDenseSubsite_levelFunctor`, available for the
canonical system only. `isContinuous_levelEtale` discharges the hypothesis there.

## What this file does not contain

The system of sheaves. Transporting a system of abelian sheaves from the small étale sites of the
`X_i` onto the levels needs nothing further — `levelEtaleSquare` with the two laws below is
exactly that datum — and the system *on the small étale sites of the `X_i`*, as the inverse images
of a single sheaf on the vertex of a cocone, is built in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/StageProjectionBaseChangeCoherence.lean`.
Its input is the pseudofunctor coherence of `AlgebraicGeometry.smallEtaleBaseChange` along the
legs of the cocone: for legs `p_i : X_i ⟶ S` and a transition `X_i ⟶ X_j`, the comparison of
direct images `(X_i ⟶ X_j)_* ⋙ (p_j)_* ≅ (p_i)_*` is
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` read on sheaves, and its own identity and
composition laws — the unit and associativity coherence of that comparison and of
`AlgebraicGeometry.smallEtaleBaseChange_factoredIdIso` — are
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_unit` and `..._hom_app_assoc` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/TransitionBaseChangeCoherence.lean`. With
them and the two laws below,
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.bcLevelInverseImageSystem` assembles, and does.

## References

* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
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

/-- The étale topology of the small étale site of `X_i`, the scheme the level `i` sits over. -/
abbrev stageTopology (i : E.system.I) :
    GrothendieckTopology
      (AlgebraicGeometry.SmallEtale B (D.obj (stage E i)) (hD (stage E i))) :=
  AlgebraicGeometry.SmallEtale.topology B (D.obj (stage E i)) (hD (stage E i))

variable (A : Type u') [Category.{v'} A]
  [hcont : ∀ i : E.system.I, (levelEtale E i).IsContinuous (E.system.J i) (stageTopology E i)]

/-! ### The continuity restatements

`InverseSystemOfFiniteSites.continuous` is a theorem rather than an instance, and
`AlgebraicGeometry.smallEtaleBaseChange_isContinuous` is stated for a morphism of `B.Scheme`, so
its conclusion names the topologies of `(B.obj (D.obj _) _).obj` while the statements here carry
`D.obj (stage E _)`; the two are definitionally equal but instance search does not pass between
them. These are the restatements it does find, in the style of
`AlgebraicGeometry.SmallEtale.isContinuous_inclusionSmallEtaleBaseChange`.
-/

/-- **The transition functor of the site system of Stacks 0EYL is continuous.** -/
theorem isContinuous_transition {i j : E.system.I} (a : i ⟶ j) :
    (E.system.u a).IsContinuous (E.system.J j) (E.system.J i) :=
  E.system.continuous a

/-- **Base change between the small étale sites of two stages is continuous**, in the spelling the
statements below need. -/
theorem isContinuous_stageBaseChange {i j : E.system.I} (a : i ⟶ j) :
    (AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).IsContinuous
      (stageTopology E j) (stageTopology E i) :=
  AlgebraicGeometry.smallEtaleBaseChange_isContinuous B (stageMap E a)

attribute [local instance] isContinuous_transition isContinuous_stageBaseChange

/-- The transition functor followed by the level is continuous: the source of the comparison
`Stacks.EtaleCohomology.TransitionBaseChange.transitionIso`. -/
theorem isContinuous_transition_comp_levelEtale {i j : E.system.I} (a : i ⟶ j) :
    (E.system.u a ⋙ levelEtale E i).IsContinuous (E.system.J j) (stageTopology E i) :=
  Functor.isContinuous_comp _ _ _ (E.system.J i) _

/-- The level followed by base change is continuous: the target of the comparison
`Stacks.EtaleCohomology.TransitionBaseChange.transitionIso`. -/
theorem isContinuous_levelEtale_comp_stageBaseChange {i j : E.system.I} (a : i ⟶ j) :
    (levelEtale E j ⋙ AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).IsContinuous
      (E.system.J j) (stageTopology E i) :=
  Functor.isContinuous_comp _ _ _ (stageTopology E j) _

/-- The composite of two transition functors is continuous: the source of the composition
comparison of the direct images along the transitions. -/
theorem isContinuous_transition_comp {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    (E.system.u b ⋙ E.system.u a).IsContinuous (E.system.J k) (E.system.J i) :=
  Functor.isContinuous_comp _ _ _ (E.system.J j) _

/-- The composite of two stage base changes is continuous: the source of the composition
comparison of the direct images along the transition morphisms of schemes. -/
theorem isContinuous_stageBaseChange_comp {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    (AlgebraicGeometry.smallEtaleBaseChange B (stageMap E b) ⋙
        AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).IsContinuous
      (stageTopology E k) (stageTopology E i) :=
  Functor.isContinuous_comp _ _ _ (stageTopology E j) _

attribute [local instance] isContinuous_transition_comp_levelEtale
  isContinuous_levelEtale_comp_stageBaseChange isContinuous_transition_comp
  isContinuous_stageBaseChange_comp

section Functors

/-- **Restriction of sheaves from the small étale site of `X_i` to the level `i`.** -/
abbrev levelEtaleRestrict (i : E.system.I) :
    Sheaf (stageTopology E i) A ⥤ Sheaf (E.system.J i) A :=
  (levelEtale E i).sheafPushforwardContinuous A (E.system.J i) (stageTopology E i)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **The restriction to a level is the affine restriction of Stacks 04HR followed by the level
restriction of Stacks 0EYL**, on the nose: restriction along a composite of functors of sites is
the composite of the restrictions, `CategoryTheory.Functor.sheafPushforwardContinuousComp` being
`CategoryTheory.Iso.refl`. At the coefficients of the colimit development the two factors are
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale` and
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictToLevel`. -/
theorem levelEtaleRestrict_eq (i : E.system.I)
    [(AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj (stage E i))
      (hD (stage E i))).IsContinuous
      (AlgebraicGeometry.SmallAffineEtale.topology B (D.obj (stage E i)) (hD (stage E i)))
      (stageTopology E i)]
    [((E.levelEquiv i).functor).IsContinuous (E.system.J i)
      (AlgebraicGeometry.SmallAffineEtale.topology B (D.obj (stage E i)) (hD (stage E i)))] :
    levelEtaleRestrict E A i =
      (AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj (stage E i))
          (hD (stage E i))).sheafPushforwardContinuous A
          (AlgebraicGeometry.SmallAffineEtale.topology B (D.obj (stage E i)) (hD (stage E i)))
          (stageTopology E i) ⋙
        ((E.levelEquiv i).functor).sheafPushforwardContinuous A (E.system.J i)
          (AlgebraicGeometry.SmallAffineEtale.topology B (D.obj (stage E i))
            (hD (stage E i))) :=
  rfl

/-- Direct image of sheaves along the transition functor of the system, at an arbitrary
coefficient category. At `Ab` this is
`InverseSystemOfFiniteSites.abelianSheafPushforward`. -/
abbrev levelPush {i j : E.system.I} (a : i ⟶ j) :
    Sheaf (E.system.J i) A ⥤ Sheaf (E.system.J j) A :=
  (E.system.u a).sheafPushforwardContinuous A (E.system.J j) (E.system.J i)

/-- Direct image of sheaves along the transition morphism `X_i ⟶ X_j` of schemes. -/
abbrev stagePush {i j : E.system.I} (a : i ⟶ j) :
    Sheaf (stageTopology E i) A ⥤ Sheaf (stageTopology E j) A :=
  (AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).sheafPushforwardContinuous A
    (stageTopology E j) (stageTopology E i)

end Functors

section Comparisons

/-- The identity comparison of the direct images along the transitions of the system, in the
spelling of `InverseSystemOfFiniteSites.abelianSheafPushforwardIdIso`. -/
def levelPushIdIso (i : E.system.I) : 𝟭 (Sheaf (E.system.J i) A) ≅ levelPush E A (𝟙 i) :=
  (Functor.sheafPushforwardContinuousId A (E.system.J i)).symm ≪≫
    (Functor.sheafPushforwardContinuousIso (eqToIso (E.system.id_map i)) A
      (E.system.J i) (E.system.J i)).symm

/-- The composition comparison of the direct images along the transitions of the system, in the
spelling of `InverseSystemOfFiniteSites.abelianSheafPushforwardCompIso`. -/
def levelPushCompIso {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    levelPush E A a ⋙ levelPush E A b ≅ levelPush E A (a ≫ b) :=
  Functor.sheafPushforwardContinuousComp' (eqToIso (E.system.comp a b).symm) A
    (E.system.J k) (E.system.J j) (E.system.J i)

/-- The identity comparison of the direct images along the transition morphisms of schemes. -/
def stagePushIdIso (i : E.system.I) :
    𝟭 (Sheaf (stageTopology E i) A) ≅ stagePush E A (𝟙 i) :=
  (Functor.sheafPushforwardContinuousId' (stageIdIso E i) A (stageTopology E i)).symm

/-- The composition comparison of the direct images along the transition morphisms of schemes. -/
def stagePushCompIso {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    stagePush E A a ⋙ stagePush E A b ≅ stagePush E A (a ≫ b) :=
  Functor.sheafPushforwardContinuousComp' (stageCompIso E a b) A
    (stageTopology E k) (stageTopology E j) (stageTopology E i)

/-- **The pasted square of direct images of Stacks 0EYL's levels.** Restriction to the level `i`
followed by direct image along the transition functor of `a : i ⟶ j` is direct image along base
change in the small étale site followed by restriction to the level `j`.

This is the pasting of the two squares of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelBaseChangeComparison.lean` — the
level square of Stacks 0EYL and the affine square of Stacks 04HR — and it is a *single*
restriction, along `Stacks.EtaleCohomology.TransitionBaseChange.transitionIso`, because
`levelEtale` is the level equivalence followed by the affine inclusion. -/
def levelEtaleSquare {i j : E.system.I} (a : i ⟶ j) :
    levelEtaleRestrict E A i ⋙ levelPush E A a ≅
      stagePush E A a ⋙ levelEtaleRestrict E A j :=
  Functor.sheafPushforwardContinuousIso (transitionIso E a) A (E.system.J j) (stageTopology E i)

end Comparisons

section Coherence

/-- The presheaf component of the pasted square. -/
theorem levelEtaleSquare_inv_app_hom_app {i j : E.system.I} (a : i ⟶ j)
    (M : Sheaf (stageTopology E i) A) (Y : (E.system.C j)ᵒᵖ) :
    ((levelEtaleSquare E A a).inv.app M).hom.app Y =
      M.obj.map ((transitionIso E a).hom.app (Opposite.unop Y)).op :=
  rfl

/-- The presheaf component of the identity comparison of the direct images along the transitions
of the system. -/
theorem levelPushIdIso_hom_app_hom_app (i : E.system.I) (N : Sheaf (E.system.J i) A)
    (Y : (E.system.C i)ᵒᵖ) :
    ((levelPushIdIso E A i).hom.app N).hom.app Y =
      N.obj.map (eqToHom (Functor.congr_obj (E.system.id_map i) (Opposite.unop Y))).op := by
  have h : (levelPushIdIso E A i).hom = (Functor.sheafPushforwardContinuousIso
      (eqToIso (E.system.id_map i)) A (E.system.J i) (E.system.J i)).inv :=
    Category.id_comp _
  rw [h, Functor.sheafPushforwardContinuousIso_inv_app_hom_app]
  exact congrArg (fun z => N.obj.map (Quiver.Hom.op z))
    (eqToHom_app (E.system.id_map i) (Opposite.unop Y))

/-- The presheaf component of the identity comparison of the direct images along the transition
morphisms of schemes. -/
theorem stagePushIdIso_hom_app_hom_app (i : E.system.I) (M : Sheaf (stageTopology E i) A)
    (Y : (AlgebraicGeometry.SmallEtale B (D.obj (stage E i)) (hD (stage E i)))ᵒᵖ) :
    ((stagePushIdIso E A i).hom.app M).hom.app Y =
      M.obj.map ((stageIdIso E i).hom.app (Opposite.unop Y)).op := by
  have h : (stagePushIdIso E A i).hom = (Functor.sheafPushforwardContinuousIso
      (stageIdIso E i) A (stageTopology E i) (stageTopology E i)).inv :=
    Category.id_comp _
  rw [h, Functor.sheafPushforwardContinuousIso_inv_app_hom_app]

/-- The presheaf component of the composition comparison of the direct images along the
transitions of the system. -/
theorem levelPushCompIso_hom_app_hom_app {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    (N : Sheaf (E.system.J i) A) (Y : (E.system.C k)ᵒᵖ) :
    ((levelPushCompIso E A a b).hom.app N).hom.app Y =
      N.obj.map (eqToHom (Functor.congr_obj (E.system.comp a b) (Opposite.unop Y))).op := by
  have h : (levelPushCompIso E A a b).hom =
      (Functor.sheafPushforwardContinuousIso (eqToIso (E.system.comp a b).symm) A
        (E.system.J k) (E.system.J i)).hom :=
    Functor.sheafPushforwardContinuousComp'_hom_eq _ _ _ _ _
  rw [h, Functor.sheafPushforwardContinuousIso_hom_app_hom_app]
  refine congrArg (fun z => N.obj.map (Quiver.Hom.op z)) ?_
  rw [eqToIso.inv]
  exact eqToHom_app _ (Opposite.unop Y)

/-- The presheaf component of the composition comparison of the direct images along the transition
morphisms of schemes. -/
theorem stagePushCompIso_hom_app_hom_app {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    (M : Sheaf (stageTopology E i) A)
    (Y : (AlgebraicGeometry.SmallEtale B (D.obj (stage E k)) (hD (stage E k)))ᵒᵖ) :
    ((stagePushCompIso E A a b).hom.app M).hom.app Y =
      M.obj.map ((stageCompIso E a b).inv.app (Opposite.unop Y)).op := by
  have h : (stagePushCompIso E A a b).hom =
      (Functor.sheafPushforwardContinuousIso (stageCompIso E a b) A
        (stageTopology E k) (stageTopology E i)).hom :=
    Functor.sheafPushforwardContinuousComp'_hom_eq _ _ _ _ _
  rw [h, Functor.sheafPushforwardContinuousIso_hom_app_hom_app]

/-- **The identity law of the pasted square of Stacks 0EYL's levels.** At an identity arrow of the
index category the square is, read across the identity comparisons of the two direct images, the
identity.

This is `Stacks.EtaleCohomology.TransitionBaseChange.transitionIso_id_hom_app` read on sheaves:
every isomorphism here is restriction along an isomorphism of functors of sites, so every presheaf
component is the image under the sheaf of a site-level morphism, and the site-level identity is
that law. -/
theorem levelEtaleSquare_id_inv_app (i : E.system.I) (M : Sheaf (stageTopology E i) A) :
    (levelEtaleRestrict E A i).map ((stagePushIdIso E A i).hom.app M) ≫
        (levelEtaleSquare E A (𝟙 i)).inv.app M =
      (levelPushIdIso E A i).hom.app ((levelEtaleRestrict E A i).obj M) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun Y => ?_))
  have hL := stagePushIdIso_hom_app_hom_app E A i M ((levelEtale E i).op.obj Y)
  have hS := levelEtaleSquare_inv_app_hom_app E A (𝟙 i) M Y
  have hR := levelPushIdIso_hom_app_hom_app E A i ((levelEtaleRestrict E A i).obj M) Y
  exact (congrArg₂ (fun f g => f ≫ g) hL hS).trans ((M.obj.map_comp _ _).symm.trans
    ((congrArg (fun z => M.obj.map (Quiver.Hom.op z))
      (transitionIso_id_hom_app E i (Opposite.unop Y))).trans hR.symm))

/-- **The composition law of the pasted square of Stacks 0EYL's levels.** At a composite `a ≫ b`
the square is the pasting of the squares at `a` and at `b`, read across the composition
comparisons of the two direct images.

This is `Stacks.EtaleCohomology.TransitionBaseChange.transitionIso_comp_hom_app` read on
sheaves. -/
theorem levelEtaleSquare_comp_inv_app {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    (M : Sheaf (stageTopology E i) A) :
    (levelEtaleRestrict E A k).map ((stagePushCompIso E A a b).hom.app M) ≫
        (levelEtaleSquare E A (a ≫ b)).inv.app M =
      (levelEtaleSquare E A b).inv.app ((stagePush E A a).obj M) ≫
        (levelPush E A b).map ((levelEtaleSquare E A a).inv.app M) ≫
          (levelPushCompIso E A a b).hom.app ((levelEtaleRestrict E A i).obj M) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun Y => ?_))
  have hL := stagePushCompIso_hom_app_hom_app E A a b M ((levelEtale E k).op.obj Y)
  have hS := levelEtaleSquare_inv_app_hom_app E A (a ≫ b) M Y
  have hR₁ := levelEtaleSquare_inv_app_hom_app E A b ((stagePush E A a).obj M) Y
  have hR₂ := levelEtaleSquare_inv_app_hom_app E A a M ((E.system.u b).op.obj Y)
  have hR₃ := levelPushCompIso_hom_app_hom_app E A a b ((levelEtaleRestrict E A i).obj M) Y
  have key : (transitionIso E (a ≫ b)).hom.app (Opposite.unop Y) ≫
      (stageCompIso E a b).inv.app ((levelEtale E k).obj (Opposite.unop Y)) =
      (levelEtale E i).map
          (eqToHom (Functor.congr_obj (E.system.comp a b) (Opposite.unop Y))) ≫
        (transitionIso E a).hom.app ((E.system.u b).obj (Opposite.unop Y)) ≫
          (AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map
            ((transitionIso E b).hom.app (Opposite.unop Y)) := by
    rw [transitionIso_comp_hom_app E a b (Opposite.unop Y)]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact congrArg (fun z => (levelEtale E i).map
        (eqToHom (Functor.congr_obj (E.system.comp a b) (Opposite.unop Y))) ≫
      (transitionIso E a).hom.app ((E.system.u b).obj (Opposite.unop Y)) ≫ z)
      (Category.comp_id ((AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map
        ((transitionIso E b).hom.app (Opposite.unop Y))))
  refine (congrArg₂ (fun f g => f ≫ g) hL hS).trans ((M.obj.map_comp _ _).symm.trans
    ((congrArg (fun z => M.obj.map (Quiver.Hom.op z)) key).trans ?_))
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp, Category.assoc]
  exact (congrArg₂ (fun f g => f ≫ g) hR₁ (congrArg₂ (fun f g => f ≫ g) hR₂ hR₃)).symm

end Coherence

end Stacks.EtaleCohomology.TransitionBaseChange

namespace Stacks.EtaleCohomology.AffineLimitCohomology

universe v u

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open Stacks.EtaleCohomology.TransitionBaseChange

attribute [local instance] isDenseSubsite_levelFunctor
  isDenseSubsite_smallAffineEtaleInclusion

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Limits.Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : Limits.IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- **A level of the site system of Stacks 0EYL, read in the small étale site of `X_i`, is a
continuous functor of sites.** It is the level equivalence of Stacks 0EYL followed by the affine
inclusion of Stacks 04HR, each the inclusion of a dense subsite
(`Stacks.EtaleCohomology.AffineLimitCohomology.isDenseSubsite_levelFunctor` and
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.isDenseSubsite_smallAffineEtaleInclusion`).

This discharges the instance hypothesis of
`Stacks.EtaleCohomology.TransitionBaseChange.levelEtaleSquare` and of its two coherence laws at
the canonical system, so those laws are available for the site system of Stacks 0EYL — and hence
for `Stacks.EtaleCohomology.BaseChangeAlgebraSystem.bcSys`, which is that system at the diagram of
base changes. -/
theorem isContinuous_levelEtale :
    ∀ i : (sys D c B hD hX hc).I,
      (levelEtale (affineEtaleSiteColimit D c B hD hX hc) i).IsContinuous
        ((sys D c B hD hX hc).J i)
        (stageTopology (affineEtaleSiteColimit D c B hD hX hc) i) :=
  fun i => Functor.isContinuous_comp _ _ _
    (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
      (hD (levelIndex D c B hD hX hc i))) _

end Stacks.EtaleCohomology.AffineLimitCohomology

end
