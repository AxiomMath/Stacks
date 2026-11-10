module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.InvariantBaseChange

/-!
# Base change of the pre-relation of a group action

Let a group object `G` of the slice over a base `Z` act on an object `U`, and let `j` be the
pre-relation of the action groupoid, that is the pre-relation on `U` whose arrow object is
`G ⊗ U`, whose target is the action and whose source is the second projection. If a morphism
`φ` out of `U` is invariant under `j`, then the base change of `j` along any `f : X' ⟶ X` is
again the pre-relation of a group action: `G` acts on the base-changed object by acting on the
second coordinate and fixing the first, and the base-changed arrow object is `G ⊗ U'`.

## Main results

* `AlgebraicGeometry.Space.exists_inducedAction_of_baseChangedPreRelation`: **Stacks 048G**,
  the induced action, its two characterizing equations, and the comparison isomorphism of
  arrow objects intertwining the source and the target maps.

## Implementation notes

The action is characterized by its two composites with the projections of the pullback: it
preserves the coordinate in `X'` and acts on the coordinate in `U`. The comparison
isomorphism `G ⊗ U' ≅ R'` is fixed by its composite with the projection to the original arrow
object, and it carries the source and the target of the base-changed pre-relation to the
second projection and to the induced action.

Everything happens in the slice `CategoryTheory.Over Z` of presheaves on the big fppf site,
whose cartesian monoidal structure is
`AlgebraicGeometry.Space.overCartesianMonoidalCategory`; this is the slice at which
`AlgebraicGeometry.Space.IsGroupInvariant` of **Stacks 048E** and the group-object API of
`CategoryTheory.GrpObj` and `CategoryTheory.ModObj` are available. The monoidal product of
the slice is the fibre product over `Z`, so the underlying object of `G ⊗ U` is the pullback
of the two structure morphisms, which is what lets the two constructions be compared by the
universal property of a pullback.

The invariance hypothesis is `AlgebraicGeometry.Space.IsInvariant` of **Stacks 048E**, which
is stated over an arbitrary base object of an arbitrary category whose slice has binary
products and so applies to the slice of presheaves used here.

The self-action of the slice on itself, `CategoryTheory.MonoidalCategory.selfLeftAction`, is
used in the proof to transport the unit and associativity laws of the action along the
projection `U' ⟶ U`.

## References

* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 048E](https://stacks.math.columbia.edu/tag/048E)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (G U : Over Z) [GrpObj G] [ModObj G U]
  {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (j : PreRelation (G ⊗ U) U) (φ : U.left ⟶ X) (f : X' ⟶ X)

/-- An invariant base change of an action pre-relation is again an action
pre-relation. The comparison of arrow spaces respects the original arrows and
both endpoints, while the induced action fixes the new-base coordinate. -/
@[stacks 048G "induced_group_action"]
theorem exists_inducedAction_of_baseChangedPreRelation
    (hsource : j.source = snd G U) (htarget : j.target = γ[G,U])
    (hφ : IsInvariant j φ) :
    ∃ action : ModObj G (baseChangedObject φ f),
      letI : ModObj G (baseChangedObject φ f) := action
      let U' := baseChangedObject φ f
      let R' := baseChangedArrows j φ f
      let j' := (baseChangedPreRelation j φ f hφ).val
      let q : U' ⟶ U := Over.homMk (pullback.snd f φ) (by rfl)
      let toOriginal : G ⊗ U' ⟶ G ⊗ U :=
        lift (fst G U') (snd G U' ≫ q)
      ((γ[G, U']).left ≫ pullback.fst f φ =
        (snd G U').left ≫ pullback.fst f φ) ∧
      (γ[G, U'] ≫ q = toOriginal ≫ γ[G,U]) ∧
    ∃ e : G ⊗ U' ≅ R',
        (e.hom.left ≫ pullback.snd f (j.target.left ≫ φ) = toOriginal.left) ∧
        (e.hom ≫ j'.source = snd G U') ∧
        (e.hom ≫ j'.target = γ[G, U']) := by
  classical
  let actionOnSelf : MonoidalLeftAction (Over Z) (Over Z) :=
    CategoryTheory.MonoidalCategory.selfLeftAction (Over Z)
  let U' := baseChangedObject φ f
  let R' := baseChangedArrows j φ f
  let j' := (baseChangedPreRelation j φ f hφ).val
  let q : U' ⟶ U := Over.homMk (pullback.snd f φ) (by rfl)
  let toOriginal : G ⊗ U' ⟶ G ⊗ U := lift (fst G U') (snd G U' ≫ q)
  have hInvariant : (γ[G, U]).left ≫ φ = (snd G U).left ≫ φ := by
    rw [← htarget, ← hsource]
    exact hφ
  have htoOriginal : toOriginal.left ≫ (snd G U).left =
      (snd G U').left ≫ q.left := by
    change (lift (fst G U') (snd G U' ≫ q)).left ≫ (snd G U).left = _
    exact congrArg Over.Hom.left (lift_snd (fst G U') (snd G U' ≫ q))
  have htoOriginal' : toOriginal.left ≫ (snd G U).left =
      (snd G U').left ≫ pullback.snd f φ := by
    have hq : q.left = pullback.snd f φ := Over.homMk_left _ _
    rw [hq] at htoOriginal
    exact htoOriginal
  have hcompat :
      ((snd G U').left ≫ pullback.fst f φ) ≫ f =
        (toOriginal.left ≫ (γ[G, U]).left) ≫ φ := by
    change
      (pullback.snd G.hom U'.hom ≫ pullback.fst f φ) ≫ f =
        (toOriginal.left ≫ (γ[G, U]).left) ≫ φ
    have htoOriginal'' : toOriginal.left ≫ (snd G U).left =
        pullback.snd G.hom U'.hom ≫ pullback.snd f φ := by
      simpa [U', baseChangedObject] using htoOriginal'
    have hpull : pullback.fst f φ ≫ f = pullback.snd f φ ≫ φ := pullback.condition
    calc
      _ = pullback.snd G.hom U'.hom ≫ (pullback.fst f φ ≫ f) := Category.assoc _ _ _
      _ = pullback.snd G.hom U'.hom ≫ (pullback.snd f φ ≫ φ) :=
        congrArg (fun k => pullback.snd G.hom U'.hom ≫ k) hpull
      _ = (pullback.snd G.hom U'.hom ≫ pullback.snd f φ) ≫ φ :=
        (Category.assoc _ _ _).symm
      _ = (toOriginal.left ≫ (snd G U).left) ≫ φ :=
        congrArg (fun k => k ≫ φ) htoOriginal''.symm
      _ = (toOriginal.left ≫ (γ[G, U]).left) ≫ φ := by
        simpa only [Category.assoc] using
          congrArg (fun k => toOriginal.left ≫ k) hInvariant.symm
  let inducedSmul : G ⊗ U' ⟶ U' := Over.homMk
    (pullback.lift ((snd G U').left ≫ pullback.fst f φ)
      (toOriginal.left ≫ (γ[G, U]).left) hcompat) (by
        change (pullback.lift _ _ _ ≫ pullback.snd f φ) ≫ U.hom = (G ⊗ U').hom
        rw [pullback.lift_snd, Category.assoc, (γ[G, U]).w]
        change toOriginal.left ≫ (G ⊗ U).hom = (G ⊗ U').hom
        exact toOriginal.w)
  have hinducedSmulLeft : inducedSmul.left =
      pullback.lift ((snd G U').left ≫ pullback.fst f φ)
        (toOriginal.left ≫ (γ[G, U]).left) hcompat := Over.homMk_left _ _
  have hqLeft : q.left = pullback.snd f φ := Over.homMk_left _ _
  have hsmulFst : inducedSmul.left ≫ pullback.fst f φ =
      (snd G U').left ≫ pullback.fst f φ := by
    rw [hinducedSmulLeft]
    exact pullback.lift_fst _ _ _
  have hsmulSnd : inducedSmul.left ≫ q.left =
      toOriginal.left ≫ (γ[G, U]).left := by
    rw [hinducedSmulLeft, hqLeft]
    exact pullback.lift_snd _ _ _
  have htoOriginalAction : toOriginal = G ◁ q := by
    apply CartesianMonoidalCategory.hom_ext
    · change lift (fst G U') (snd G U' ≫ q) ≫ fst G U = (G ◁ q) ≫ fst G U
      rw [lift_fst, whiskerLeft_fst]
    · change lift (fst G U') (snd G U' ≫ q) ≫ snd G U = (G ◁ q) ≫ snd G U
      rw [lift_snd, whiskerLeft_snd]
  have hInducedQ : inducedSmul ≫ q = G ◁ q ≫ γ[G,U] := by
    apply Over.OverMorphism.ext
    change inducedSmul.left ≫ q.left = (G ◁ q).left ≫ (γ[G,U]).left
    rw [hsmulSnd, htoOriginalAction]
  let action : ModObj G U' := {
    smul := inducedSmul
    one_smul := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · change ((η ▷ U').left ≫ inducedSmul.left) ≫ pullback.fst f φ =
          (λ_ U').hom.left ≫ pullback.fst f φ
        have hEtaSnd : (η ▷ U').left ≫ (snd G U').left =
            (snd (𝟙_ (Over Z)) U').left :=
          congrArg Over.Hom.left (whiskerRight_snd η U')
        have hUnitSnd : (λ_ U').hom.left = (snd (𝟙_ (Over Z)) U').left := by
          cat_disch
        calc
          _ = (η ▷ U').left ≫ (inducedSmul.left ≫ pullback.fst f φ) :=
            Category.assoc _ _ _
          _ = (η ▷ U').left ≫ ((snd G U').left ≫ pullback.fst f φ) :=
            congrArg (fun k => (η ▷ U').left ≫ k) hsmulFst
          _ = (snd (𝟙_ (Over Z)) U').left ≫ pullback.fst f φ :=
            congrArg (fun k => k ≫ pullback.fst f φ) hEtaSnd
          _ = (λ_ U').hom.left ≫ pullback.fst f φ :=
            congrArg (fun k => k ≫ pullback.fst f φ) hUnitSnd.symm
      · change ((η ▷ U').left ≫ inducedSmul.left) ≫ pullback.snd f φ =
          (λ_ U').hom.left ≫ pullback.snd f φ
        rw [← hqLeft]
        have htoOriginalAction' : toOriginal.left = (G ◁ q).left :=
          congrArg Over.Hom.left htoOriginalAction
        have hExchange :
            MonoidalLeftActionStruct.actionHomRight (𝟙_ (Over Z)) q ≫ η ▷ U =
              η ▷ U' ≫ MonoidalLeftActionStruct.actionHomRight G q :=
          MonoidalLeftAction.action_exchange (C := Over Z) (D := Over Z)
            (w := 𝟙_ (Over Z)) (x := G) (y := U') (z := U) η q
        have hexchange' :
            ((MonoidalLeftActionStruct.actionHomRight (𝟙_ (Over Z)) q).left ≫
              (η ▷ U).left) =
              ((η ▷ U').left ≫
                (MonoidalLeftActionStruct.actionHomRight G q).left) :=
          congrArg Over.Hom.left hExchange
        calc
          _ = (η ▷ U').left ≫ (inducedSmul.left ≫ q.left) :=
            Category.assoc _ _ _
          _ = (η ▷ U').left ≫ (toOriginal.left ≫ γ[G,U].left) :=
            congrArg (fun k => (η ▷ U').left ≫ k) hsmulSnd
          _ = (MonoidalLeftActionStruct.actionHomRight (𝟙_ (Over Z)) q).left ≫
              (η ▷ U).left ≫ γ[G,U].left := by
            rw [htoOriginalAction']
            exact congrArg (fun k => k ≫ γ[G,U].left) hexchange'.symm
          _ = (MonoidalLeftActionStruct.actionHomRight (𝟙_ (Over Z)) q).left ≫
              (λ_ U).hom.left :=
            congrArg
              (fun k => (MonoidalLeftActionStruct.actionHomRight (𝟙_ (Over Z)) q).left ≫ k)
              (congrArg Over.Hom.left (ModObj.one_smul_self G U))
          _ = (λ_ U').hom.left ≫ q.left :=
            congrArg Over.Hom.left
              (MonoidalLeftAction.actionUnitIso_hom_naturality q).symm
    mul_smul := by
      have hμsnd : (μ[G] ▷ U') ≫ snd G U' = snd (G ⊗ G) U' :=
        whiskerRight_snd (f := μ[G]) U'
      have hwhiskerSnd := whiskerLeft_snd G inducedSmul
      have hαsnd := associator_hom_snd_snd G G U'
      have hExchangeMul : (G ⊗ G) ◁ q ≫ μ[G] ▷ U =
          μ[G] ▷ U' ≫ G ◁ q :=
        MonoidalLeftAction.action_exchange (C := Over Z) (D := Over Z)
          (w := G ⊗ G) (x := G) (y := U') (z := U) μ[G] q
      have hAssocNat := associator_naturality_right G G q
      have hMulQ : (μ[G] ▷ U') ≫ inducedSmul ≫ q =
          (α_ G G U').hom ≫ G ◁ inducedSmul ≫ inducedSmul ≫ q := by
        calc
          _ = (μ[G] ▷ U') ≫ (G ◁ q ≫ γ[G,U]) :=
            congrArg (fun k => (μ[G] ▷ U') ≫ k) hInducedQ
          _ = ((G ⊗ G) ◁ q ≫ μ[G] ▷ U) ≫ γ[G,U] :=
            congrArg (fun k => k ≫ γ[G,U]) hExchangeMul.symm
          _ = (G ⊗ G) ◁ q ≫ (μ[G] ▷ U ≫ γ[G,U]) := Category.assoc _ _ _
          _ = (G ⊗ G) ◁ q ≫
              ((α_ G G U).hom ≫ G ◁ γ[G,U] ≫ γ[G,U]) :=
            congrArg (fun k => (G ⊗ G) ◁ q ≫ k) (ModObj.mul_smul_self G U)
          _ = ((α_ G G U').hom ≫ G ◁ (G ◁ q)) ≫
              G ◁ γ[G,U] ≫ γ[G,U] :=
            congrArg (fun k => k ≫ G ◁ γ[G,U] ≫ γ[G,U]) hAssocNat
          _ = (α_ G G U').hom ≫
              (G ◁ (G ◁ q) ≫ G ◁ γ[G,U]) ≫ γ[G,U] := by
            simp only [Category.assoc]
          _ = (α_ G G U').hom ≫ G ◁ (G ◁ q ≫ γ[G,U]) ≫ γ[G,U] := by
            rw [← whiskerLeft_comp]
          _ = (α_ G G U').hom ≫ G ◁ (inducedSmul ≫ q) ≫ γ[G,U] :=
            congrArg (fun k => (α_ G G U').hom ≫ G ◁ k ≫ γ[G,U]) hInducedQ.symm
          _ = (α_ G G U').hom ≫ G ◁ inducedSmul ≫ G ◁ q ≫ γ[G,U] := by
            rw [whiskerLeft_comp]
            simp only [Category.assoc]
          _ = (α_ G G U').hom ≫ G ◁ inducedSmul ≫ inducedSmul ≫ q := by
            simpa only [Category.assoc] using
              congrArg (fun k => ((α_ G G U').hom ≫ G ◁ inducedSmul) ≫ k)
                hInducedQ.symm
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · change (μ ▷ U').left ≫ inducedSmul.left ≫ pullback.fst f φ =
          ((α_ G G U').hom.left ≫ (G ◁ inducedSmul).left ≫ inducedSmul.left) ≫
            pullback.fst f φ
        have hm : (μ ▷ U').left ≫ (snd G U').left =
            (snd (G ⊗ G) U').left := congrArg Over.Hom.left hμsnd
        have hw : (G ◁ inducedSmul).left ≫ (snd G U').left =
            (snd G (G ⊗ U')).left ≫ inducedSmul.left :=
          congrArg Over.Hom.left hwhiskerSnd
        have ha : (α_ G G U').hom.left ≫ (snd G (G ⊗ U')).left ≫
            (snd G U').left = (snd (G ⊗ G) U').left :=
          congrArg Over.Hom.left hαsnd
        calc
          _ = (μ ▷ U').left ≫ ((inducedSmul.left ≫ pullback.fst f φ)) :=
            Category.assoc _ _ _
          _ = (μ ▷ U').left ≫ ((snd G U').left ≫ pullback.fst f φ) :=
            congrArg (fun k => (μ ▷ U').left ≫ k) hsmulFst
          _ = ((μ ▷ U').left ≫ (snd G U').left) ≫ pullback.fst f φ :=
            (Category.assoc _ _ _).symm
          _ = (snd (G ⊗ G) U').left ≫ pullback.fst f φ :=
            congrArg (fun k => k ≫ pullback.fst f φ) hm
          _ = ((α_ G G U').hom.left ≫ (snd G (G ⊗ U')).left ≫
              (snd G U').left) ≫ pullback.fst f φ := by
                rw [ha]
          _ = ((α_ G G U').hom.left ≫ (snd G (G ⊗ U')).left) ≫
              ((snd G U').left ≫ pullback.fst f φ) := Category.assoc _ _ _
          _ = ((α_ G G U').hom.left ≫ (snd G (G ⊗ U')).left) ≫
              (inducedSmul.left ≫ pullback.fst f φ) :=
                congrArg (fun k => ((α_ G G U').hom.left ≫ (snd G (G ⊗ U')).left) ≫ k)
                  hsmulFst.symm
          _ = ((α_ G G U').hom.left ≫
              ((snd G (G ⊗ U')).left ≫ inducedSmul.left)) ≫ pullback.fst f φ :=
                (Category.assoc _ _ _).symm
          _ = ((α_ G G U').hom.left ≫
              ((G ◁ inducedSmul).left ≫ (snd G U').left)) ≫ pullback.fst f φ :=
                congrArg (fun k => ((α_ G G U').hom.left ≫ k) ≫ pullback.fst f φ)
                  hw.symm
          _ = (((α_ G G U').hom.left ≫ (G ◁ inducedSmul).left) ≫
              (snd G U').left) ≫ pullback.fst f φ := Category.assoc _ _ _
          _ = ((α_ G G U').hom.left ≫ (G ◁ inducedSmul).left) ≫
              ((snd G U').left ≫ pullback.fst f φ) := Category.assoc _ _ _
          _ = ((α_ G G U').hom.left ≫ (G ◁ inducedSmul).left) ≫
              (inducedSmul.left ≫ pullback.fst f φ) :=
                congrArg (fun k => ((α_ G G U').hom.left ≫ (G ◁ inducedSmul).left) ≫ k)
                  hsmulFst.symm
          _ = _ := by cat_disch
      · rw [← hqLeft]
        change ((μ[G] ▷ U') ≫ inducedSmul ≫ q).left =
          ((α_ G G U').hom ≫ G ◁ inducedSmul ≫ inducedSmul ≫ q).left
        exact congrArg Over.Hom.left hMulQ
  }
  let inducedModObj : ModObj G U' := action
  have hTargetLeft : j.target.left = (γ[G,U]).left :=
    congrArg Over.Hom.left htarget
  have hSourceLeft : j.source.left = (snd G U).left :=
    congrArg Over.Hom.left hsource
  have hRelationInvariant : j.target.left ≫ φ = j.source.left ≫ φ := hφ
  have hArrowCompat :
      ((snd G U').left ≫ pullback.fst f φ) ≫ f =
        toOriginal.left ≫ (j.target.left ≫ φ) := by
    calc
      _ = (toOriginal.left ≫ (γ[G,U]).left) ≫ φ := hcompat
      _ = toOriginal.left ≫ ((γ[G,U]).left ≫ φ) := Category.assoc _ _ _
      _ = toOriginal.left ≫ (j.target.left ≫ φ) :=
        congrArg (fun k => toOriginal.left ≫ (k ≫ φ)) hTargetLeft.symm
  let eMap : (G ⊗ U').left ⟶ R'.left :=
    pullback.lift ((snd G U').left ≫ pullback.fst f φ) toOriginal.left hArrowCompat
  have eMapFst : eMap ≫ pullback.fst f (j.target.left ≫ φ) =
      (snd G U').left ≫ pullback.fst f φ := pullback.lift_fst _ _ _
  have eMapSnd : eMap ≫ pullback.snd f (j.target.left ≫ φ) =
      toOriginal.left := pullback.lift_snd _ _ _
  let eHom : G ⊗ U' ⟶ R' := Over.homMk eMap (by
    dsimp only [R', baseChangedArrows]
    change eMap ≫ (pullback.snd f (j.target.left ≫ φ) ≫ (G ⊗ U).hom) =
      (G ⊗ U').hom
    calc
      _ = (eMap ≫ pullback.snd f (j.target.left ≫ φ)) ≫ (G ⊗ U).hom :=
        (Category.assoc _ _ _).symm
      _ = toOriginal.left ≫ (G ⊗ U).hom :=
        congrArg (fun k => k ≫ (G ⊗ U).hom) eMapSnd
      _ = (G ⊗ U').hom := toOriginal.w)
  have hSourceCompat :
      pullback.fst f (j.target.left ≫ φ) ≫ f =
        (pullback.snd f (j.target.left ≫ φ) ≫ j.source.left) ≫ φ := by
    simpa only [Category.assoc, hRelationInvariant] using
      (pullback.condition (f := f) (g := j.target.left ≫ φ))
  let eInvObjMap : pullback f (j.target.left ≫ φ) ⟶ pullback f φ :=
    pullback.lift (pullback.fst f (j.target.left ≫ φ))
      (pullback.snd f (j.target.left ≫ φ) ≫ j.source.left) hSourceCompat
  have hInvObjSnd : eInvObjMap ≫ pullback.snd f φ =
      pullback.snd f (j.target.left ≫ φ) ≫ j.source.left :=
    pullback.lift_snd _ _ _
  have hInvObjFst : eInvObjMap ≫ pullback.fst f φ =
      pullback.fst f (j.target.left ≫ φ) := pullback.lift_fst _ _ _
  let eInvObj : R' ⟶ U' := Over.homMk eInvObjMap (by
    change eInvObjMap ≫ (pullback.snd f φ ≫ U.hom) =
      pullback.snd f (j.target.left ≫ φ) ≫ (G ⊗ U).hom
    calc
      eInvObjMap ≫ (pullback.snd f φ ≫ U.hom) =
          (eInvObjMap ≫ pullback.snd f φ) ≫ U.hom := (Category.assoc _ _ _).symm
      _ = (pullback.snd f (j.target.left ≫ φ) ≫ j.source.left) ≫ U.hom :=
        congrArg (fun k => k ≫ U.hom) hInvObjSnd
      _ = pullback.snd f (j.target.left ≫ φ) ≫ (G ⊗ U).hom := by
        calc
          _ = pullback.snd f (j.target.left ≫ φ) ≫ (j.source.left ≫ U.hom) :=
            Category.assoc _ _ _
          _ = _ := congrArg (fun k => pullback.snd f (j.target.left ≫ φ) ≫ k)
            (Over.w j.source))
  let eInvGroupMap : R'.left ⟶ G.left :=
    pullback.snd f (j.target.left ≫ φ) ≫ (fst G U).left
  let eInvGroup : R' ⟶ G := Over.homMk eInvGroupMap (by
    change pullback.snd f (j.target.left ≫ φ) ≫ (fst G U).left ≫ G.hom =
      pullback.snd f (j.target.left ≫ φ) ≫ (G ⊗ U).hom
    exact congrArg (fun k => pullback.snd f (j.target.left ≫ φ) ≫ k)
      (Over.w (fst G U)))
  let eInv : R' ⟶ G ⊗ U' := lift eInvGroup eInvObj
  have htoOriginalFst : toOriginal.left ≫ (fst G U).left = (fst G U').left := by
    calc
      _ = (G ◁ q).left ≫ (fst G U).left :=
        congrArg (fun k => k.left ≫ (fst G U).left) htoOriginalAction
      _ = (fst G U').left := congrArg Over.Hom.left (whiskerLeft_fst G q)
  have hEInvFst : eInv ≫ fst G U' = eInvGroup := by
    change lift eInvGroup eInvObj ≫ fst G U' = eInvGroup
    exact CartesianMonoidalCategory.lift_fst eInvGroup eInvObj
  have hEInvSnd : eInv ≫ snd G U' = eInvObj := by
    change lift eInvGroup eInvObj ≫ snd G U' = eInvObj
    exact CartesianMonoidalCategory.lift_snd eInvGroup eInvObj
  have hEInvObjLeft : eInvObj.left = eInvObjMap := by
    change (Over.homMk (X := Z) (U := R') (V := U') eInvObjMap _).left = eInvObjMap
    exact Over.homMk_left _ _
  have hEInvSndLeft : eInv.left ≫ (snd G U').left = eInvObjMap := by
    have hh := congrArg Over.Hom.left hEInvSnd
    have hh' : eInv.left ≫ (snd G U').left = eInvObj.left := by
      simpa only [Over.comp_left] using hh
    exact hh'.trans hEInvObjLeft
  have hEHomInvGroup : eHom ≫ eInvGroup = fst G U' := by
    apply Over.OverMorphism.ext
    change eMap ≫ eInvGroupMap = (fst G U').left
    change eMap ≫ (pullback.snd f (j.target.left ≫ φ) ≫ (fst G U).left) =
      (fst G U').left
    calc
      _ = (eMap ≫ pullback.snd f (j.target.left ≫ φ)) ≫ (fst G U).left :=
        (Category.assoc _ _ _).symm
      _ = toOriginal.left ≫ (fst G U).left :=
        congrArg (fun k => k ≫ (fst G U).left) eMapSnd
      _ = (fst G U').left := htoOriginalFst
  have hEMapSrc : eMap ≫ (pullback.snd f (j.target.left ≫ φ) ≫ j.source.left) =
      (snd G U').left ≫ pullback.snd f φ := by
    rw [← Category.assoc, eMapSnd, hSourceLeft, htoOriginal, hqLeft]
  have hEHomInvObj : eHom ≫ eInvObj = snd G U' := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change eMap ≫ eInvObjMap ≫ pullback.fst f φ =
        (snd G U').left ≫ pullback.fst f φ
      calc
        eMap ≫ (eInvObjMap ≫ pullback.fst f φ) =
            eMap ≫ pullback.fst f (j.target.left ≫ φ) :=
          congrArg (fun k => eMap ≫ k) hInvObjFst
        _ = (snd G U').left ≫ pullback.fst f φ := eMapFst
    · change eMap ≫ eInvObjMap ≫ pullback.snd f φ =
        (snd G U').left ≫ pullback.snd f φ
      rw [hInvObjSnd]
      exact hEMapSrc
  let toArrow : R' ⟶ G ⊗ U := Over.homMk
    (pullback.snd f (j.target.left ≫ φ)) (by rfl)
  have hToOriginalFstOver : toOriginal ≫ fst G U = fst G U' := by
    rw [htoOriginalAction]
    exact whiskerLeft_fst G q
  have hToOriginalSndOver : toOriginal ≫ snd G U = snd G U' ≫ q := by
    apply Over.OverMorphism.ext
    exact htoOriginal
  have hInvGroupToArrow : eInvGroup = toArrow ≫ fst G U := by
    apply Over.OverMorphism.ext
    rfl
  have hInvObjToArrow : eInvObj ≫ q = toArrow ≫ snd G U := by
    apply Over.OverMorphism.ext
    change eInvObjMap ≫ q.left =
      pullback.snd f (j.target.left ≫ φ) ≫ (snd G U).left
    calc
      _ = eInvObjMap ≫ pullback.snd f φ :=
        congrArg (fun k => eInvObjMap ≫ k) hqLeft
      _ = pullback.snd f (j.target.left ≫ φ) ≫ j.source.left := hInvObjSnd
      _ = pullback.snd f (j.target.left ≫ φ) ≫ (snd G U).left :=
        congrArg (fun k => pullback.snd f (j.target.left ≫ φ) ≫ k) hSourceLeft
  have hInvToOriginal : eInv ≫ toOriginal = toArrow := by
    apply CartesianMonoidalCategory.hom_ext
    · calc
        eInv ≫ (toOriginal ≫ fst G U) = eInv ≫ fst G U' :=
          congrArg (fun k => eInv ≫ k) hToOriginalFstOver
        _ = eInvGroup := hEInvFst
        _ = toArrow ≫ fst G U := hInvGroupToArrow
    · calc
        eInv ≫ (toOriginal ≫ snd G U) = eInv ≫ (snd G U' ≫ q) :=
          congrArg (fun k => eInv ≫ k) hToOriginalSndOver
        _ = eInvObj ≫ q := congrArg (fun k => k ≫ q) hEInvSnd
        _ = toArrow ≫ snd G U := hInvObjToArrow
  have hInvToOriginalLeft : eInv.left ≫ toOriginal.left =
      pullback.snd f (j.target.left ≫ φ) := by
    have hh := congrArg Over.Hom.left hInvToOriginal
    have hh' : eInv.left ≫ toOriginal.left = toArrow.left := by
      simpa only [Over.comp_left] using hh
    have hToArrowLeft : toArrow.left = pullback.snd f (j.target.left ≫ φ) := by
      change (Over.homMk (X := Z) (U := R') (V := G ⊗ U)
        (pullback.snd f (j.target.left ≫ φ)) _).left = _
      exact Over.homMk_left _ _
    exact hh'.trans hToArrowLeft
  let e : G ⊗ U' ≅ R' := {
    hom := eHom
    inv := eInv
    hom_inv_id := by
      apply CartesianMonoidalCategory.hom_ext
      · simpa [eInv] using hEHomInvGroup
      · simpa [eInv] using hEHomInvObj
    inv_hom_id := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · change eInv.left ≫ eMap ≫ pullback.fst f (j.target.left ≫ φ) =
        pullback.fst f (j.target.left ≫ φ)
        rw [eMapFst]
        have hAssoc : eInv.left ≫ ((snd G U').left ≫ pullback.fst f φ) =
            (eInv.left ≫ (snd G U').left) ≫ pullback.fst f φ :=
          (Category.assoc _ _ _).symm
        rw [hAssoc, hEInvSndLeft]
        exact hInvObjFst
      · change eInv.left ≫ eMap ≫ pullback.snd f (j.target.left ≫ φ) =
        pullback.snd f (j.target.left ≫ φ)
        rw [eMapSnd]
        exact hInvToOriginalLeft
  }
  refine ⟨action, ?_⟩
  refine ⟨?_, ?_⟩
  · exact hsmulFst
  · refine ⟨?_, ?_⟩
    · change γ[G, U'] ≫ q = toOriginal ≫ γ[G, U]
      rw [htoOriginalAction]
      exact hInducedQ
    · refine ⟨e, ?_, ?_⟩
      · change eMap ≫ pullback.snd f (j.target.left ≫ φ) = toOriginal.left
        exact eMapSnd
      · refine ⟨?_, ?_⟩
        · change eHom ≫ j'.source = snd G U'
          apply Over.OverMorphism.ext
          apply pullback.hom_ext
          · change eMap ≫ j'.source.left ≫ pullback.fst f φ =
              (snd G U').left ≫ pullback.fst f φ
            calc
              (eMap ≫ j'.source.left) ≫ pullback.fst f φ =
                  eMap ≫ (j'.source.left ≫ pullback.fst f φ) :=
                Category.assoc _ _ _
              _ = eMap ≫ pullback.fst f (j.target.left ≫ φ) :=
                congrArg (fun k => eMap ≫ k)
                  (baseChangedPreRelation
                    j φ f hφ).property.2.1
              _ = (snd G U').left ≫ pullback.fst f φ := eMapFst
          · change eMap ≫ j'.source.left ≫ pullback.snd f φ =
              (snd G U').left ≫ pullback.snd f φ
            rw [(baseChangedPreRelation j φ f hφ).property.2.2]
            exact hEMapSrc
        · change eHom ≫ j'.target = γ[G, U']
          apply Over.OverMorphism.ext
          apply pullback.hom_ext
          · change eMap ≫ j'.target.left ≫ pullback.fst f φ =
              inducedSmul.left ≫ pullback.fst f φ
            calc
              (eMap ≫ j'.target.left) ≫ pullback.fst f φ =
                  eMap ≫ (j'.target.left ≫ pullback.fst f φ) :=
                Category.assoc _ _ _
              _ = eMap ≫ pullback.fst f (j.target.left ≫ φ) :=
                congrArg (fun k => eMap ≫ k)
                  (baseChangedPreRelation
                    j φ f hφ).property.1.1
              _ = (snd G U').left ≫ pullback.fst f φ := eMapFst
              _ = inducedSmul.left ≫ pullback.fst f φ := hsmulFst.symm
          · change eMap ≫ j'.target.left ≫ pullback.snd f φ =
              inducedSmul.left ≫ q.left
            calc
              (eMap ≫ j'.target.left) ≫ pullback.snd f φ =
                  eMap ≫ (j'.target.left ≫ pullback.snd f φ) :=
                Category.assoc _ _ _
              _ = eMap ≫ (pullback.snd f (j.target.left ≫ φ) ≫ j.target.left) :=
                congrArg (fun k => eMap ≫ k)
                  (baseChangedPreRelation
                    j φ f hφ).property.1.2
              _ = (eMap ≫ pullback.snd f (j.target.left ≫ φ)) ≫ j.target.left :=
                (Category.assoc _ _ _).symm
              _ = toOriginal.left ≫ j.target.left :=
                congrArg (fun k => k ≫ j.target.left) eMapSnd
              _ = toOriginal.left ≫ (γ[G, U]).left :=
                congrArg (fun k => toOriginal.left ≫ k) hTargetLeft
              _ = inducedSmul.left ≫ q.left := hsmulSnd.symm


end AlgebraicGeometry.Space

end
