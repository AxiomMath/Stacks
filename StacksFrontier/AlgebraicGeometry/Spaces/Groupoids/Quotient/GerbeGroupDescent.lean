module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.OverPullbackLeft
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack

/-!
# Algebraicity of the quotient stack of a group action (Stacks 06PK)

Let a group algebraic space `G` over an algebraic space `B` act on an algebraic space `X` over
`B`. The quotient stack `[X/G]` is an algebraic stack exactly when there is a morphism
`φ : X' ⟶ X` of algebraic spaces over `B` for which `(g, x') ↦ g • φ x'` is a surjection of
fppf sheaves `G ×_B X' ⟶ X` and both projections of the space of triples
`{(x₁, g, x₂) : φ x₁ = g • φ x₂}` to `X'` are flat and locally of finite presentation.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_action_iff`: the reduction of the
  criterion above to the groupoid criterion of Stacks 06PJ, applied to an action groupoid.

## Implementation notes

The action groupoid of Stacks 0444 has object space `X`, arrow space `G ×_B X`, source the
second projection and target the action, so Stacks 06PJ applied to it reads: `[X/G]` is
algebraic exactly when some `φ : X' ⟶ X` makes
`X' ×_{φ, X, γ} (G ×_B X) ⟶ G ×_B X ⟶ X` a surjection of sheaves and the source and target of
the restriction of the action groupoid along `φ` flat and locally of finite presentation. The
two translations of that into the data of the action are the content of this file.

The first translation is `actionSaturationIso`: inverting the group element identifies
`X' ×_{φ, X, γ} (G ×_B X)` with `G ×_B X'` compatibly with the two maps to `X`, which is where
the inverse of `G` enters the proof of Stacks 06PK. The second is `actionRestrictionIso`: the
same inversion identifies the arrow space of the restriction, the fibre product of
`X' ×_{φ, X, γ} (G ×_B X)` and `(G ×_B X) ×_{pr, X, φ} X'` over `G ×_B X`, with the space of
triples, carrying the restriction's source and target to the two projections. Both are built in
the slice over `B`, so `overPullbackLeftIso`, the comparison of a fibre product taken in the slice
with the one taken in presheaves, transports them to the underlying presheaves, where flatness
and local finite presentation of Stacks 03ML and Stacks 03XP are stated.

The statements here take the groupoid criterion of Stacks 06PJ as an argument `hgroupoid`, so
that this file does not import its proof. That criterion is
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_iff_restrictionAlong`, and supplying it
gives Stacks 06PK itself:
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_action_iff_exists_cover` and
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_groupoidOfAction_iff_exists_cover` of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ActionQuotientStackAlgebraicIff`.

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
* [Stacks Project, Tag 06PK](https://stacks.math.columbia.edu/tag/06PK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u w

namespace AlgebraicGeometry.Stack

private theorem holdsOnEveryEtaleChart_precompIso
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (P : MorphismProperty Scheme.{u})
    {F F' H : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ F') (f : F' ⟶ H) :
    Space.HoldsOnEveryEtaleChart C S hS P (e.hom ≫ f) ↔
      Space.HoldsOnEveryEtaleChart C S hS P f := by
  let Q : MorphismProperty (AlgebraicGeometry.BigFppfOver C S hS) :=
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme C S hS)
  let _ : Q.presheaf.RespectsIso := MorphismProperty.relative_respectsIso Q
  constructor
  · intro hf U V a b h ha hb hab
    apply hf U V (a ≫ e.inv) b h
      ((Q.presheaf.cancel_right_of_respectsIso a e.inv).2 ha) hb
    simpa [Category.assoc] using hab
  · intro hf U V a b h ha hb hab
    apply hf U V (a ≫ e.hom) b h
      ((Q.presheaf.cancel_right_of_respectsIso a e.hom).2 ha) hb
    simpa [Category.assoc] using hab

private theorem isLocallySurjective_precompIso
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {F F' H : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ F') (f : F' ⟶ H) :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology C S hS)
      (e.hom ≫ f) ↔
        Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology C S hS) f := by
  constructor
  · intro hf
    let _ := hf
    exact Presheaf.isLocallySurjective_of_isLocallySurjective
      (AlgebraicGeometry.BigFppfOver.topology C S hS) e.hom f
  · intro hf
    let _ := Presheaf.isLocallySurjective_of_iso
      (AlgebraicGeometry.BigFppfOver.topology C S hS) e.hom
    let _ := hf
    infer_instance

private noncomputable def actionRestrictionOuterComparisonIso
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    (pullback (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ)).left ≅
      pullback (pullback.snd φ.left γ[G, X].left)
        (pullback.fst (snd G X).left φ.left) := by
  let fO := pullback.snd φ (γ[G, X])
  let gO := pullback.fst (snd G X) φ
  let f := pullback.snd φ.left γ[G, X].left
  let g := pullback.fst (snd G X).left φ.left
  let ea := overPullbackLeftIso φ (γ[G, X])
  let ed := overPullbackLeftIso (snd G X) φ
  let eo := overPullbackLeftIso fO gO
  let m := pullback.map fO.left gO.left f g ea.hom ed.hom (𝟙 (G ⊗ X).left)
    (by simpa [fO, f, ea] using (overPullbackLeftIso_hom_snd φ (γ[G, X])).symm)
    (by simpa [gO, g, ed] using (overPullbackLeftIso_hom_fst (snd G X) φ).symm)
  let e₁ : (pullback fO.left gO.left) ≅ pullback f g := asIso m
  exact eo ≪≫ e₁

private theorem actionRestrictionOuterComparisonIso_inv_source
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    (actionRestrictionOuterComparisonIso C S hS B G X X' φ).inv ≫
        ((pullback.snd (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ)).left ≫
          (pullback.snd (snd G X) φ).left) =
      pullback.snd (pullback.snd φ.left γ[G, X].left)
        (pullback.fst (snd G X).left φ.left) ≫ pullback.snd (snd G X).left φ.left := by
  rw [Iso.inv_comp_eq]
  dsimp only [actionRestrictionOuterComparisonIso, Iso.trans_hom, asIso_hom]
  simp only [Category.assoc]
  erw [pullback.lift_snd_assoc]
  simp only [Category.assoc, overPullbackLeftIso_hom_snd]
  rw [← Category.assoc, overPullbackLeftIso_hom_snd]

private theorem actionRestrictionOuterComparisonIso_inv_target
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    (actionRestrictionOuterComparisonIso C S hS B G X X' φ).inv ≫
        ((pullback.fst (pullback.snd φ (γ[G, X]))
            (pullback.fst (snd G X) φ)).left ≫
          (pullback.fst φ (γ[G, X])).left) =
      pullback.fst (pullback.snd φ.left γ[G, X].left)
        (pullback.fst (snd G X).left φ.left) ≫ pullback.fst φ.left γ[G, X].left := by
  rw [Iso.inv_comp_eq]
  dsimp only [actionRestrictionOuterComparisonIso, Iso.trans_hom, asIso_hom]
  simp only [Category.assoc]
  erw [pullback.lift_fst_assoc]
  simp only [Category.assoc, overPullbackLeftIso_hom_fst]
  rw [← Category.assoc, overPullbackLeftIso_hom_fst]

private theorem actionInverse_involutive
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X : Over B.obj) [GrpObj G] [ModObj G X] :
    Space.actionInverse B G X ≫
        Space.actionInverse B G X = 𝟙 (G ⊗ X) :=
  Stacks.Groupoids.ActionGroupoid.inverse_comp_inverse G X

private theorem actionInverse_comp_snd
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X : Over B.obj) [GrpObj G] [ModObj G X] :
    Space.actionInverse B G X ≫ snd G X = γ[G, X] :=
  Stacks.Groupoids.ActionGroupoid.inverse_source G X

private theorem actionInverse_comp_smul
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X : Over B.obj) [GrpObj G] [ModObj G X] :
    Space.actionInverse B G X ≫ γ[G, X] = snd G X :=
  Stacks.Groupoids.ActionGroupoid.inverse_target G X

private noncomputable def actionSaturationLift
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    G ⊗ X' ⟶ pullback φ (γ[G, X]) :=
  pullback.lift (snd G X') ((𝟙 G ⊗ₘ φ) ≫ Space.actionInverse B G X)
    (by rw [Category.assoc, actionInverse_comp_smul, tensorHom_snd])

private noncomputable def actionSaturationDrop
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    pullback φ (γ[G, X]) ⟶ G ⊗ X' :=
  lift
    (pullback.snd φ (γ[G, X]) ≫ Space.actionInverse B G X ≫ fst G X)
    (pullback.fst φ (γ[G, X]))

private theorem actionSaturationLift_fst
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionSaturationLift C S hS B G X X' φ ≫ pullback.fst φ (γ[G, X]) =
      snd G X' := by
  rw [actionSaturationLift, pullback.lift_fst]

private theorem actionSaturationLift_snd
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionSaturationLift C S hS B G X X' φ ≫ pullback.snd φ (γ[G, X]) =
      (𝟙 G ⊗ₘ φ) ≫ Space.actionInverse B G X := by
  rw [actionSaturationLift, pullback.lift_snd]

private theorem actionSaturationDrop_fst
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionSaturationDrop C S hS B G X X' φ ≫ fst G X' =
      pullback.snd φ (γ[G, X]) ≫ Space.actionInverse B G X ≫ fst G X := by
  simp [actionSaturationDrop]

private theorem actionSaturationDrop_snd
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionSaturationDrop C S hS B G X X' φ ≫ snd G X' =
      pullback.fst φ (γ[G, X]) := by
  simp [actionSaturationDrop]

private theorem actionSaturationDrop_tensorHom
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionSaturationDrop C S hS B G X X' φ ≫ (𝟙 G ⊗ₘ φ) =
      pullback.snd φ (γ[G, X]) ≫ Space.actionInverse B G X := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [Category.assoc, actionSaturationDrop_fst]
  · simp [Category.assoc, actionSaturationDrop, actionInverse_comp_snd,
      pullback.condition]

private noncomputable def actionSaturationIso
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    pullback φ (γ[G, X]) ≅ G ⊗ X' where
  hom := actionSaturationDrop C S hS B G X X' φ
  inv := actionSaturationLift C S hS B G X X' φ
  hom_inv_id := by
    apply pullback.hom_ext
    · calc
        (actionSaturationDrop C S hS B G X X' φ ≫
            actionSaturationLift C S hS B G X X' φ) ≫ pullback.fst φ (γ[G, X]) =
          actionSaturationDrop C S hS B G X X' φ ≫ snd G X' := by rw [Category.assoc,
            actionSaturationLift_fst]
        _ = pullback.fst φ (γ[G, X]) := by rw [actionSaturationDrop_snd]
    · calc
        (actionSaturationDrop C S hS B G X X' φ ≫
            actionSaturationLift C S hS B G X X' φ) ≫ pullback.snd φ (γ[G, X]) =
          actionSaturationDrop C S hS B G X X' φ ≫
            ((𝟙 G ⊗ₘ φ) ≫ Space.actionInverse B G X) := by
              rw [Category.assoc, actionSaturationLift_snd]
        _ = (pullback.snd φ (γ[G, X]) ≫ Space.actionInverse B G X) ≫
              Space.actionInverse B G X := by
                rw [← Category.assoc, actionSaturationDrop_tensorHom]
        _ = pullback.snd φ (γ[G, X]) := by
              simp [Category.assoc, actionInverse_involutive]

  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · calc
        (actionSaturationLift C S hS B G X X' φ ≫
            actionSaturationDrop C S hS B G X X' φ) ≫ fst G X' =
          actionSaturationLift C S hS B G X X' φ ≫
            (pullback.snd φ (γ[G, X]) ≫ Space.actionInverse B G X ≫ fst G X) := by
              rw [Category.assoc, actionSaturationDrop_fst]
        _ = (actionSaturationLift C S hS B G X X' φ ≫
              pullback.snd φ (γ[G, X])) ≫ Space.actionInverse B G X ≫ fst G X := by
                cat_disch
        _ = ((𝟙 G ⊗ₘ φ) ≫ Space.actionInverse B G X) ≫
              Space.actionInverse B G X ≫ fst G X := by
                rw [actionSaturationLift_snd]
        _ = ((𝟙 G ⊗ₘ φ) ≫
              (Space.actionInverse B G X ≫ Space.actionInverse B G X)) ≫
                fst G X := by
              cat_disch
        _ = ((𝟙 G ⊗ₘ φ) ≫ 𝟙 (G ⊗ X)) ≫ fst G X := by
              rw [actionInverse_involutive]
        _ = fst G X' := by simp
    · calc
        (actionSaturationLift C S hS B G X X' φ ≫
            actionSaturationDrop C S hS B G X X' φ) ≫ snd G X' =
          actionSaturationLift C S hS B G X X' φ ≫ pullback.fst φ (γ[G, X]) := by
            rw [Category.assoc, actionSaturationDrop_snd]
        _ = snd G X' := by rw [actionSaturationLift_fst]

private theorem actionSaturationDrop_comp_action
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionSaturationDrop C S hS B G X X' φ ≫
        ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) =
      pullback.snd φ (γ[G, X]) ≫ snd G X := by
  calc
    actionSaturationDrop C S hS B G X X' φ ≫
        ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) =
      (actionSaturationDrop C S hS B G X X' φ ≫ (𝟙 G ⊗ₘ φ)) ≫ γ[G, X] := by
        cat_disch
    _ = (pullback.snd φ (γ[G, X]) ≫ Space.actionInverse B G X) ≫ γ[G, X] := by
        rw [actionSaturationDrop_tensorHom]
    _ = pullback.snd φ (γ[G, X]) ≫ snd G X := by
        calc
          (pullback.snd φ (γ[G, X]) ≫ Space.actionInverse B G X) ≫ γ[G, X] =
              pullback.snd φ (γ[G, X]) ≫
                (Space.actionInverse B G X ≫ γ[G, X]) := by cat_disch
          _ = pullback.snd φ (γ[G, X]) ≫ snd G X := by rw [actionInverse_comp_smul]

private theorem isLocallySurjective_action_saturation_iff
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology C S hS)
        (pullback.snd φ.left γ[G, X].left ≫ pullback.snd G.hom X.hom) ↔
      Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology C S hS)
        (((𝟙 G ⊗ₘ φ) ≫ γ[G, X]).left) := by
  let e := overPullbackLeftIso φ (γ[G, X])
  let f : (pullback φ.left γ[G, X].left) ⟶ X.left :=
    pullback.snd φ.left γ[G, X].left ≫ pullback.snd G.hom X.hom
  have h₁ : e.hom ≫ f = (pullback.snd φ (γ[G, X]) ≫ snd G X).left := by
    rw [← Category.assoc, overPullbackLeftIso_hom_snd]
    simp [Over.comp_left]
  have h₂ : (actionSaturationDrop C S hS B G X X' φ).left ≫ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]).left =
      (pullback.snd φ (γ[G, X]) ≫ snd G X).left :=
    congrArg Over.Hom.left (actionSaturationDrop_comp_action C S hS B G X X' φ)
  rw [← isLocallySurjective_precompIso C S hS e f, h₁, ← h₂]
  exact isLocallySurjective_precompIso C S hS
    ((Over.forget B.obj).mapIso (actionSaturationIso C S hS B G X X' φ)) _

private noncomputable def actionRestrictionForward
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    pullback (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ) ⟶
      pullback φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) := by
  refine pullback.lift
    (pullback.snd (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ) ≫
      pullback.snd (snd G X) φ)
    (pullback.fst (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ) ≫
      actionSaturationDrop C S hS B G X X' φ) ?_
  calc
    pullback.snd (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ) ≫
        pullback.snd (snd G X) φ ≫ φ =
      pullback.snd (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ) ≫
        pullback.fst (snd G X) φ ≫ snd G X := by
          calc
            _ = pullback.snd (pullback.snd φ (γ[G, X]))
                  (pullback.fst (snd G X) φ) ≫
                (pullback.snd (snd G X) φ ≫ φ) := by cat_disch
            _ = pullback.snd (pullback.snd φ (γ[G, X]))
                  (pullback.fst (snd G X) φ) ≫
                (pullback.fst (snd G X) φ ≫ snd G X) := by
                  rw [← pullback.condition]
            _ = _ := by cat_disch
    _ = pullback.fst (pullback.snd φ (γ[G, X]))
          (pullback.fst (snd G X) φ) ≫
        pullback.snd φ (γ[G, X]) ≫ snd G X := by
          calc
            _ = (pullback.snd (pullback.snd φ (γ[G, X]))
                  (pullback.fst (snd G X) φ) ≫
                pullback.fst (snd G X) φ) ≫ snd G X := by cat_disch
            _ = (pullback.fst (pullback.snd φ (γ[G, X]))
                  (pullback.fst (snd G X) φ) ≫
                pullback.snd φ (γ[G, X])) ≫ snd G X := by rw [pullback.condition]
            _ = _ := by cat_disch
    _ = pullback.fst (pullback.snd φ (γ[G, X]))
          (pullback.fst (snd G X) φ) ≫
        actionSaturationDrop C S hS B G X X' φ ≫
          ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) := by
          rw [actionSaturationDrop_comp_action]
    _ = _ := by cat_disch

private noncomputable def actionRestrictionArrowInverse
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    pullback φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ⟶ G ⊗ X :=
  pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
    (𝟙 G ⊗ₘ φ) ≫ Space.actionInverse B G X

private noncomputable def actionRestrictionToA
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    pullback φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ⟶ pullback φ (γ[G, X]) :=
  pullback.lift
    (pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫ snd G X')
    (actionRestrictionArrowInverse C S hS B G X X' φ)
    (by
      rw [actionRestrictionArrowInverse]
      calc
        pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫ snd G X' ≫ φ =
            pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
              ((𝟙 G ⊗ₘ φ) ≫ snd G X) := by
                rw [tensorHom_snd]
        _ = pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
              ((𝟙 G ⊗ₘ φ) ≫ Space.actionInverse B G X ≫ γ[G, X]) := by
                rw [actionInverse_comp_smul]
      )

private noncomputable def actionRestrictionToB
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    pullback φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ⟶ pullback (snd G X) φ :=
  pullback.lift
    (actionRestrictionArrowInverse C S hS B G X X' φ)
    (pullback.fst φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]))
    (by
      rw [actionRestrictionArrowInverse]
      calc
        pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
            (𝟙 G ⊗ₘ φ) ≫ Space.actionInverse B G X ≫ snd G X =
            pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
              ((𝟙 G ⊗ₘ φ) ≫ (Space.actionInverse B G X ≫ snd G X)) := by
                cat_disch
        _ = pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
              ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) := by
                rw [actionInverse_comp_snd]
        _ = pullback.fst φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫ φ := by
                rw [← pullback.condition]
      )

private noncomputable def actionRestrictionBackward
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    pullback φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ⟶
      pullback (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ) :=
  pullback.lift
    (actionRestrictionToA C S hS B G X X' φ)
    (actionRestrictionToB C S hS B G X X' φ)
    (by
      calc
        actionRestrictionToA C S hS B G X X' φ ≫ pullback.snd φ (γ[G, X]) =
            actionRestrictionArrowInverse C S hS B G X X' φ := by
              rw [actionRestrictionToA, pullback.lift_snd]
        _ = actionRestrictionToB C S hS B G X X' φ ≫
              pullback.fst (snd G X) φ := by
              rw [actionRestrictionToB, pullback.lift_fst]
      )

private theorem actionRestrictionForward_fst
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
  actionRestrictionForward C S hS B G X X' φ ≫
        pullback.fst φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) =
      pullback.snd (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ) ≫
        pullback.snd (snd G X) φ := by
  rw [actionRestrictionForward, pullback.lift_fst]

private theorem actionRestrictionForward_snd
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionRestrictionForward C S hS B G X X' φ ≫
        pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) =
      pullback.fst (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ) ≫
        actionSaturationDrop C S hS B G X X' φ := by
  rw [actionRestrictionForward, pullback.lift_snd]

private theorem actionRestrictionBackward_fst
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionRestrictionBackward C S hS B G X X' φ ≫
        pullback.fst (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ) =
      actionRestrictionToA C S hS B G X X' φ := by
  rw [actionRestrictionBackward, pullback.lift_fst]

private theorem actionRestrictionBackward_snd
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionRestrictionBackward C S hS B G X X' φ ≫
        pullback.snd (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ) =
      actionRestrictionToB C S hS B G X X' φ := by
  rw [actionRestrictionBackward, pullback.lift_snd]

private theorem actionRestrictionToA_fst
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionRestrictionToA C S hS B G X X' φ ≫ pullback.fst φ (γ[G, X]) =
      pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫ snd G X' := by
  rw [actionRestrictionToA, pullback.lift_fst]

private theorem actionRestrictionToA_snd
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionRestrictionToA C S hS B G X X' φ ≫ pullback.snd φ (γ[G, X]) =
      actionRestrictionArrowInverse C S hS B G X X' φ := by
  rw [actionRestrictionToA, pullback.lift_snd]

private theorem actionRestrictionToB_fst
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionRestrictionToB C S hS B G X X' φ ≫ pullback.fst (snd G X) φ =
      actionRestrictionArrowInverse C S hS B G X X' φ := by
  rw [actionRestrictionToB, pullback.lift_fst]

private theorem actionRestrictionToB_snd
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionRestrictionToB C S hS B G X X' φ ≫ pullback.snd (snd G X) φ =
      pullback.fst φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) := by
  rw [actionRestrictionToB, pullback.lift_snd]

private theorem actionRestrictionToA_eq_saturationLift
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionRestrictionToA C S hS B G X X' φ =
      pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
        actionSaturationLift C S hS B G X X' φ := by
  apply pullback.hom_ext
  · calc
      actionRestrictionToA C S hS B G X X' φ ≫ pullback.fst φ (γ[G, X]) =
          pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫ snd G X' :=
            actionRestrictionToA_fst C S hS B G X X' φ
      _ = pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
            (actionSaturationLift C S hS B G X X' φ ≫ pullback.fst φ (γ[G, X])) := by
              rw [actionSaturationLift_fst]
  · calc
      actionRestrictionToA C S hS B G X X' φ ≫ pullback.snd φ (γ[G, X]) =
          actionRestrictionArrowInverse C S hS B G X X' φ :=
            actionRestrictionToA_snd C S hS B G X X' φ
      _ = pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
            (actionSaturationLift C S hS B G X X' φ ≫ pullback.snd φ (γ[G, X])) := by
              rw [actionRestrictionArrowInverse, actionSaturationLift_snd]
      _ = _ := by cat_disch

private theorem actionRestrictionForward_arrowInverse
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    actionRestrictionForward C S hS B G X X' φ ≫
      actionRestrictionArrowInverse C S hS B G X X' φ =
        pullback.fst (pullback.snd φ (γ[G, X]))
          (pullback.fst (snd G X) φ) ≫ pullback.snd φ (γ[G, X]) := by
  calc
    actionRestrictionForward C S hS B G X X' φ ≫
        actionRestrictionArrowInverse C S hS B G X X' φ =
      actionRestrictionForward C S hS B G X X' φ ≫
        pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
          (𝟙 G ⊗ₘ φ) ≫ Space.actionInverse B G X := by
            rw [actionRestrictionArrowInverse]
    _ = pullback.fst (pullback.snd φ (γ[G, X]))
          (pullback.fst (snd G X) φ) ≫ actionSaturationDrop C S hS B G X X' φ ≫
          (𝟙 G ⊗ₘ φ) ≫ Space.actionInverse B G X := by
            rw [← Category.assoc, actionRestrictionForward_snd]
            cat_disch
    _ = pullback.fst (pullback.snd φ (γ[G, X]))
          (pullback.fst (snd G X) φ) ≫ pullback.snd φ (γ[G, X]) ≫
          Space.actionInverse B G X ≫ Space.actionInverse B G X := by
            calc
              _ = pullback.fst (pullback.snd φ (γ[G, X]))
                    (pullback.fst (snd G X) φ) ≫
                    (actionSaturationDrop C S hS B G X X' φ ≫
                      (𝟙 G ⊗ₘ φ)) ≫ Space.actionInverse B G X := by cat_disch
              _ = pullback.fst (pullback.snd φ (γ[G, X]))
                    (pullback.fst (snd G X) φ) ≫
                    (pullback.snd φ (γ[G, X]) ≫ Space.actionInverse B G X) ≫
                      Space.actionInverse B G X := by
                        rw [actionSaturationDrop_tensorHom]
              _ = _ := by cat_disch
    _ = pullback.fst (pullback.snd φ (γ[G, X]))
          (pullback.fst (snd G X) φ) ≫ pullback.snd φ (γ[G, X]) := by
            simp [actionInverse_involutive]

private noncomputable def actionRestrictionIso
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    pullback (pullback.snd φ (γ[G, X])) (pullback.fst (snd G X) φ) ≅
      pullback φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) where
  hom := actionRestrictionForward C S hS B G X X' φ
  inv := actionRestrictionBackward C S hS B G X X' φ
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · calc
          (actionRestrictionForward C S hS B G X X' φ ≫
              actionRestrictionBackward C S hS B G X X' φ) ≫
              pullback.fst (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫ pullback.fst φ (γ[G, X]) =
            actionRestrictionForward C S hS B G X X' φ ≫
              (actionRestrictionBackward C S hS B G X X' φ ≫
                pullback.fst (pullback.snd φ (γ[G, X]))
                  (pullback.fst (snd G X) φ)) ≫ pullback.fst φ (γ[G, X]) := by
                    cat_disch
          _ = actionRestrictionForward C S hS B G X X' φ ≫
                actionRestrictionToA C S hS B G X X' φ ≫ pullback.fst φ (γ[G, X]) := by
                  rw [actionRestrictionBackward_fst]
          _ = actionRestrictionForward C S hS B G X X' φ ≫
                pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫ snd G X' := by
                  rw [actionRestrictionToA_fst]
          _ = (pullback.fst (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫
                actionSaturationDrop C S hS B G X X' φ) ≫ snd G X' := by
                  rw [← Category.assoc, actionRestrictionForward_snd]
          _ = pullback.fst (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫ pullback.fst φ (γ[G, X]) := by
                  calc
                    _ = pullback.fst (pullback.snd φ (γ[G, X]))
                          (pullback.fst (snd G X) φ) ≫
                          (actionSaturationDrop C S hS B G X X' φ ≫ snd G X') := by
                            cat_disch
                    _ = _ := by rw [actionSaturationDrop_snd]
          _ = (𝟙 _ ≫ pullback.fst (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ)) ≫ pullback.fst φ (γ[G, X]) := by simp
      · calc
          (actionRestrictionForward C S hS B G X X' φ ≫
              actionRestrictionBackward C S hS B G X X' φ) ≫
              pullback.fst (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫ pullback.snd φ (γ[G, X]) =
            actionRestrictionForward C S hS B G X X' φ ≫
              (actionRestrictionBackward C S hS B G X X' φ ≫
                pullback.fst (pullback.snd φ (γ[G, X]))
                  (pullback.fst (snd G X) φ)) ≫ pullback.snd φ (γ[G, X]) := by
                    cat_disch
          _ = actionRestrictionForward C S hS B G X X' φ ≫
                actionRestrictionToA C S hS B G X X' φ ≫ pullback.snd φ (γ[G, X]) := by
                  rw [actionRestrictionBackward_fst]
          _ = actionRestrictionForward C S hS B G X X' φ ≫
                actionRestrictionArrowInverse C S hS B G X X' φ := by
                  rw [actionRestrictionToA_snd]
          _ = pullback.fst (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫ pullback.snd φ (γ[G, X]) := by
                  rw [actionRestrictionForward_arrowInverse]
          _ = (𝟙 _ ≫ pullback.fst (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ)) ≫ pullback.snd φ (γ[G, X]) := by simp
    · apply pullback.hom_ext
      · calc
          (actionRestrictionForward C S hS B G X X' φ ≫
              actionRestrictionBackward C S hS B G X X' φ) ≫
              pullback.snd (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫ pullback.fst (snd G X) φ =
            actionRestrictionForward C S hS B G X X' φ ≫
              (actionRestrictionBackward C S hS B G X X' φ ≫
                pullback.snd (pullback.snd φ (γ[G, X]))
                  (pullback.fst (snd G X) φ)) ≫ pullback.fst (snd G X) φ := by
                    cat_disch
          _ = actionRestrictionForward C S hS B G X X' φ ≫
                actionRestrictionToB C S hS B G X X' φ ≫ pullback.fst (snd G X) φ := by
                  rw [actionRestrictionBackward_snd]
          _ = actionRestrictionForward C S hS B G X X' φ ≫
                actionRestrictionArrowInverse C S hS B G X X' φ := by
                  rw [actionRestrictionToB_fst]
          _ = pullback.fst (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫ pullback.snd φ (γ[G, X]) := by
                  rw [actionRestrictionForward_arrowInverse]
          _ = pullback.snd (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫ pullback.fst (snd G X) φ := by
                  rw [pullback.condition]
          _ = (𝟙 _ ≫ pullback.snd (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ)) ≫ pullback.fst (snd G X) φ := by simp
      · calc
          (actionRestrictionForward C S hS B G X X' φ ≫
              actionRestrictionBackward C S hS B G X X' φ) ≫
              pullback.snd (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫ pullback.snd (snd G X) φ =
            actionRestrictionForward C S hS B G X X' φ ≫
              (actionRestrictionBackward C S hS B G X X' φ ≫
                pullback.snd (pullback.snd φ (γ[G, X]))
                  (pullback.fst (snd G X) φ)) ≫ pullback.snd (snd G X) φ := by
                    cat_disch
          _ = actionRestrictionForward C S hS B G X X' φ ≫
                actionRestrictionToB C S hS B G X X' φ ≫ pullback.snd (snd G X) φ := by
                  rw [actionRestrictionBackward_snd]
          _ = actionRestrictionForward C S hS B G X X' φ ≫
                pullback.fst φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) := by
                  rw [actionRestrictionToB_snd]
          _ = pullback.snd (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫ pullback.snd (snd G X) φ := by
                  rw [actionRestrictionForward_fst]
          _ = (𝟙 _ ≫ pullback.snd (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ)) ≫ pullback.snd (snd G X) φ := by simp
  inv_hom_id := by
    apply pullback.hom_ext
    · calc
        (actionRestrictionBackward C S hS B G X X' φ ≫
            actionRestrictionForward C S hS B G X X' φ) ≫
            pullback.fst φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) =
          actionRestrictionBackward C S hS B G X X' φ ≫
            (actionRestrictionForward C S hS B G X X' φ ≫
              pullback.fst φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X])) := by cat_disch
        _ = actionRestrictionBackward C S hS B G X X' φ ≫
              pullback.snd (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫ pullback.snd (snd G X) φ := by
                rw [actionRestrictionForward_fst]
        _ = actionRestrictionToB C S hS B G X X' φ ≫ pullback.snd (snd G X) φ := by
                rw [← Category.assoc, actionRestrictionBackward_snd]
        _ = pullback.fst φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) := by
                rw [actionRestrictionToB_snd]
        _ = 𝟙 _ ≫ pullback.fst φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) := by simp
    · calc
        (actionRestrictionBackward C S hS B G X X' φ ≫
            actionRestrictionForward C S hS B G X X' φ) ≫
            pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) =
          actionRestrictionBackward C S hS B G X X' φ ≫
            (actionRestrictionForward C S hS B G X X' φ ≫
              pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X])) := by cat_disch
        _ = actionRestrictionBackward C S hS B G X X' φ ≫
              pullback.fst (pullback.snd φ (γ[G, X]))
                (pullback.fst (snd G X) φ) ≫ actionSaturationDrop C S hS B G X X' φ := by
                rw [actionRestrictionForward_snd]
        _ = actionRestrictionToA C S hS B G X X' φ ≫
              actionSaturationDrop C S hS B G X X' φ := by
                rw [← Category.assoc, actionRestrictionBackward_fst]
        _ = pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) := by
                rw [actionRestrictionToA_eq_saturationLift]
                calc
                  _ = pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
                        (actionSaturationLift C S hS B G X X' φ ≫
                          actionSaturationDrop C S hS B G X X' φ) := by cat_disch
                  _ = pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
                        𝟙 (G ⊗ X') := by
                    calc
                      _ = pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X]) ≫
                            (actionSaturationLift C S hS B G X X' φ ≫
                              actionSaturationDrop C S hS B G X X' φ) := by cat_disch
                      _ = _ := by
                            have hIso :=
                              (actionSaturationIso C S hS B G X X' φ).inv_hom_id
                            change actionSaturationLift C S hS B G X X' φ ≫
                              actionSaturationDrop C S hS B G X X' φ = 𝟙 (G ⊗ X') at hIso
                            rw [hIso]
                  _ = _ := by simp

private noncomputable def actionRestrictionComparisonIso
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    pullback (pullback.snd φ.left γ[G, X].left)
        (pullback.fst (snd G X).left φ.left) ≅
      pullback φ.left ((𝟙 G ⊗ₘ φ).left ≫ γ[G, X].left) := by
  let fO := pullback.snd φ (γ[G, X])
  let gO := pullback.fst (snd G X) φ
  let eR := actionRestrictionOuterComparisonIso C S hS B G X X' φ
  let eAction := actionRestrictionIso C S hS B G X X' φ
  let eActionLeft : (pullback fO gO).left ≅ (pullback φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X])).left :=
    (Over.forget B.obj).mapIso eAction
  let e₂ := overPullbackLeftIso φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X])
  exact eR.symm ≪≫ eActionLeft ≪≫ e₂

private theorem actionRestrictionComparisonIso_hom_fst
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    (actionRestrictionComparisonIso C S hS B G X X' φ).hom ≫
        pullback.fst φ.left ((𝟙 G ⊗ₘ φ).left ≫ γ[G, X].left) =
      pullback.snd (pullback.snd φ.left γ[G, X].left)
        (pullback.fst (snd G X).left φ.left) ≫ pullback.snd (snd G X).left φ.left := by
  let fO := pullback.snd φ (γ[G, X])
  let gO := pullback.fst (snd G X) φ
  let eR := actionRestrictionOuterComparisonIso C S hS B G X X' φ
  let e₂ := overPullbackLeftIso φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X])
  let a : G ⊗ X' ⟶ X := (𝟙 G ⊗ₘ φ) ≫ γ[G, X]
  have hForward :
      (actionRestrictionForward C S hS B G X X' φ).left ≫
          (pullback.fst φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X])).left =
        (pullback.snd (pullback.snd φ (γ[G, X]))
            (pullback.fst (snd G X) φ) ≫ pullback.snd (snd G X) φ).left :=
    congrArg Over.Hom.left (actionRestrictionForward_fst C S hS B G X X' φ)
  change eR.inv ≫ (actionRestrictionForward C S hS B G X X' φ).left ≫
      e₂.hom ≫ pullback.fst φ.left a.left = _
  rw [show e₂.hom ≫ pullback.fst φ.left a.left = (pullback.fst φ a).left by
    simpa [e₂, a, Over.comp_left] using (overPullbackLeftIso_hom_fst φ a)]
  rw [hForward]
  exact actionRestrictionOuterComparisonIso_inv_source C S hS B G X X' φ

private theorem actionRestrictionComparisonIso_hom_snd
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X) :
    (actionRestrictionComparisonIso C S hS B G X X' φ).hom ≫
        (pullback.snd φ.left ((𝟙 G ⊗ₘ φ).left ≫ γ[G, X].left) ≫
          (snd G X').left) =
      pullback.fst (pullback.snd φ.left γ[G, X].left)
        (pullback.fst (snd G X).left φ.left) ≫
        pullback.fst φ.left γ[G, X].left := by
  let fO := pullback.snd φ (γ[G, X])
  let gO := pullback.fst (snd G X) φ
  let eR := actionRestrictionOuterComparisonIso C S hS B G X X' φ
  let e₂ := overPullbackLeftIso φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X])
  let a : G ⊗ X' ⟶ X := (𝟙 G ⊗ₘ φ) ≫ γ[G, X]
  have hForward :
      (actionRestrictionForward C S hS B G X X' φ).left ≫
          ((pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X])).left ≫ (snd G X').left) =
        (pullback.fst (pullback.snd φ (γ[G, X]))
            (pullback.fst (snd G X) φ) ≫ pullback.fst φ (γ[G, X])).left := by
    calc
      _ = ((actionRestrictionForward C S hS B G X X' φ ≫
            pullback.snd φ ((𝟙 G ⊗ₘ φ) ≫ γ[G, X])) ≫ snd G X').left := by
              simp [Over.comp_left, Category.assoc]
      _ = ((pullback.fst (pullback.snd φ (γ[G, X]))
            (pullback.fst (snd G X) φ) ≫ actionSaturationDrop C S hS B G X X' φ) ≫
              snd G X').left := by rw [actionRestrictionForward_snd]
      _ = (pullback.fst (pullback.snd φ (γ[G, X]))
            (pullback.fst (snd G X) φ) ≫ pullback.fst φ (γ[G, X])).left := by
              rw [Category.assoc, actionSaturationDrop_snd]
  change eR.inv ≫ (actionRestrictionForward C S hS B G X X' φ).left ≫
      e₂.hom ≫ (pullback.snd φ.left a.left ≫ (snd G X').left) = _
  have hE₂ : e₂.hom ≫ (pullback.snd φ.left a.left ≫ (snd G X').left) =
      (pullback.snd φ a).left ≫ (snd G X').left := by
    calc
      _ = (e₂.hom ≫ pullback.snd φ.left a.left) ≫ (snd G X').left := by cat_disch
      _ = _ := by
        rw [show e₂.hom ≫ pullback.snd φ.left a.left = (pullback.snd φ a).left by
          simpa [e₂, a, Over.comp_left] using (overPullbackLeftIso_hom_snd φ a)]
  rw [hE₂]
  change eR.inv ≫ (actionRestrictionForward C S hS B G X X' φ).left ≫
      ((pullback.snd φ a).left ≫ (snd G X').left) = _
  rw [hForward]
  exact actionRestrictionOuterComparisonIso_inv_target C S hS B G X X' φ

/-- Étale-chart-local properties of the first projection from the arrow space of the restriction
are those of the restricted source. -/
private theorem holdsOnEveryEtaleChart_restriction_fst_iff
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X)
    (P : MorphismProperty Scheme.{u}) :
    Space.HoldsOnEveryEtaleChart C S hS P
        (pullback.fst φ.left ((𝟙 G ⊗ₘ φ).left ≫ γ[G, X].left)) ↔
      Space.HoldsOnEveryEtaleChart C S hS P
        (pullback.snd (pullback.snd φ.left γ[G, X].left)
          (pullback.fst (snd G X).left φ.left) ≫ pullback.snd (snd G X).left φ.left) := by
  rw [← holdsOnEveryEtaleChart_precompIso C S hS P
    (actionRestrictionComparisonIso C S hS B G X X' φ), actionRestrictionComparisonIso_hom_fst]

/-- Étale-chart-local properties of the second projection from the arrow space of the restriction
are those of the restricted target. -/
private theorem holdsOnEveryEtaleChart_restriction_snd_iff
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X X' : Over B.obj) [GrpObj G] [ModObj G X] (φ : X' ⟶ X)
    (P : MorphismProperty Scheme.{u}) :
    Space.HoldsOnEveryEtaleChart C S hS P
        (pullback.snd φ.left ((𝟙 G ⊗ₘ φ).left ≫ γ[G, X].left) ≫ (snd G X').left) ↔
      Space.HoldsOnEveryEtaleChart C S hS P
        (pullback.fst (pullback.snd φ.left γ[G, X].left)
          (pullback.fst (snd G X).left φ.left) ≫ pullback.fst φ.left γ[G, X].left) := by
  rw [← holdsOnEveryEtaleChart_precompIso C S hS P
    (actionRestrictionComparisonIso C S hS B G X X' φ), actionRestrictionComparisonIso_hom_snd]

/-- **The reduction of Stacks 06PK to Stacks 06PJ.** Let a group algebraic space `G` over an
algebraic space `B` act on an algebraic space `X` over `B`. Given the groupoid criterion of
Stacks 06PJ as `hgroupoid`, the quotient stack `[X/G]` of the action groupoid is an algebraic
stack exactly when there is a morphism `φ : X' ⟶ X` of algebraic spaces over `B` for which
`G ×_B X' ⟶ X`, `(g, x') ↦ g • φ x'`, is a surjection of fppf sheaves and both projections to
`X'` of the space of triples `{(x₁, g, x₂) : φ x₁ = g • φ x₂}` are flat and locally of finite
presentation.

The criterion of Stacks 06PJ is
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_iff_restrictionAlong`; with it supplied
this is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_action_iff_exists_cover`. -/
theorem isAlgebraicStack_quotientStack_action_iff
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left)
    (A : Space.ActionGroupoidConstruction B G X hG hX)
    (hgroupoid : ∀ H : GroupoidInAlgebraicSpaces C S hS B,
      IsAlgebraicStack.{u, w} C S hS (quotientStack H) ↔
        ∃ (U' : AlgebraicSpaces C S hS) (g : U' ⟶ H.objects),
          Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
            ((GroupoidInAlgebraicSpaces.fiberProductSnd g H.target ≫ H.source).hom) ∧
          Space.IsFlat C S hS
            (GroupoidInAlgebraicSpaces.restrictionSource H g).hom ∧
          Space.IsFlat C S hS
            (GroupoidInAlgebraicSpaces.restrictionTarget H g).hom ∧
          Space.IsLocallyOfFinitePresentation C S hS
            (GroupoidInAlgebraicSpaces.restrictionSource H g).hom ∧
          Space.IsLocallyOfFinitePresentation C S hS
            (GroupoidInAlgebraicSpaces.restrictionTarget H g).hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack A.groupoid) ↔
      ∃ (X' : Over B.obj) (_ : IsAlgebraicSpace C S hS X'.left) (φ : X' ⟶ X),
        let a : G ⊗ X' ⟶ X := (𝟙 G ⊗ₘ φ) ≫ γ[G, X]
        Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) a.left ∧
        Space.IsFlat C S hS (pullback.fst φ.left a.left) ∧
        Space.IsLocallyOfFinitePresentation C S hS (pullback.fst φ.left a.left) ∧
        Space.IsFlat C S hS (pullback.snd φ.left a.left ≫ (snd G X').left) ∧
        Space.IsLocallyOfFinitePresentation C S hS
          (pullback.snd φ.left a.left ≫ (snd G X').left) := by
  rw [hgroupoid A.groupoid]
  rcases A with ⟨grp, hObjects, hArrows, hObjectsBase, hArrowsBase,
    hSource, hTarget, hCompIso, hCompFst, hCompSnd, hComp, hIdentity, hInverse⟩
  rcases grp with ⟨objects, arrows, objectsToBase, arrowsToBase, source, target,
    sourceOver, targetOver, comp, compOver, pointwise⟩
  cases hObjects
  cases hArrows
  have hSourceEq : source.hom = (snd G X).left := eq_of_heq hSource
  have hTargetEq : target.hom = γ[G, X].left := eq_of_heq hTarget
  have hBaseEq : objectsToBase.hom = X.hom := eq_of_heq hObjectsBase
  have hres : ∀ (X' : Over B.obj) (φ : X' ⟶ X) (P : MorphismProperty Scheme.{u}),
      (Space.HoldsOnEveryEtaleChart C S hS P
          (pullback.fst φ.left ((𝟙 G ⊗ₘ φ).left ≫ γ[G, X].left)) ↔
        Space.HoldsOnEveryEtaleChart C S hS P
          (pullback.snd (pullback.snd φ.left target.hom) (pullback.fst source.hom φ.left) ≫
            pullback.snd source.hom φ.left)) ∧
      (Space.HoldsOnEveryEtaleChart C S hS P
          (pullback.snd φ.left ((𝟙 G ⊗ₘ φ).left ≫ γ[G, X].left) ≫ (snd G X').left) ↔
        Space.HoldsOnEveryEtaleChart C S hS P
          (pullback.fst (pullback.snd φ.left target.hom) (pullback.fst source.hom φ.left) ≫
            pullback.fst φ.left target.hom)) := fun X' φ P => by
    rw [hTargetEq, hSourceEq]
    exact ⟨holdsOnEveryEtaleChart_restriction_fst_iff C S hS B G X X' φ P,
      holdsOnEveryEtaleChart_restriction_snd_iff C S hS B G X X' φ P⟩
  constructor
  · rintro ⟨U', g, hcover, hflat₁, hflat₂, hfp₁, hfp₂⟩
    let X' : Over B.obj := Over.mk (g.hom ≫ objectsToBase.hom)
    let hX' : IsAlgebraicSpace C S hS X'.left := U'.property
    let φ : X' ⟶ X := Over.homMk g.hom (by
      simpa [X', Category.assoc] using (congrArg (fun f => g.hom ≫ f) hBaseEq).symm)
    refine ⟨X', hX', φ, ?_, ?_, ?_, ?_, ?_⟩
    · change Presheaf.IsLocallySurjective
        (BigFppfOver.topology C S hS)
        (pullback.snd g.hom target.hom ≫ source.hom) at hcover
      rw [hTargetEq, hSourceEq] at hcover
      exact (isLocallySurjective_action_saturation_iff C S hS B G X X' φ).mp hcover
    · exact (hres X' φ (@Flat : MorphismProperty Scheme.{u})).1.mpr hflat₁
    · exact (hres X' φ (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})).1.mpr hfp₁
    · exact (hres X' φ (@Flat : MorphismProperty Scheme.{u})).2.mpr hflat₂
    · exact (hres X' φ (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})).2.mpr hfp₂
  · rintro ⟨X', hX', φ, hcover, hflat₁, hfp₁, hflat₂, hfp₂⟩
    let a : G ⊗ X' ⟶ X := (𝟙 G ⊗ₘ φ) ≫ γ[G, X]
    let U' : AlgebraicSpaces C S hS := ⟨X'.left, hX'⟩
    let g : U' ⟶ (⟨X.left, hX⟩ : AlgebraicSpaces C S hS) :=
      ObjectProperty.homMk φ.left
    refine ⟨U', g, ?_, ?_, ?_, ?_, ?_⟩
    · change Presheaf.IsLocallySurjective
        (BigFppfOver.topology C S hS)
        (pullback.snd φ.left target.hom ≫ source.hom)
      rw [hTargetEq, hSourceEq]
      exact (isLocallySurjective_action_saturation_iff C S hS B G X X' φ).mpr hcover
    · exact (hres X' φ (@Flat : MorphismProperty Scheme.{u})).1.mp hflat₁
    · exact (hres X' φ (@Flat : MorphismProperty Scheme.{u})).2.mp hflat₂
    · exact (hres X' φ (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})).1.mp hfp₁
    · exact (hres X' φ (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})).2.mp hfp₂

/-- **The reduction of Stacks 06PK to Stacks 06PJ** for the action groupoid of Stacks 0444
itself: given the groupoid criterion of Stacks 06PJ as `hgroupoid`, the quotient stack `[X/G]`
is an algebraic stack exactly when there is a morphism `φ : X' ⟶ X` of algebraic spaces over
`B` for which `G ×_B X' ⟶ X`, `(g, x') ↦ g • φ x'`, is a surjection of fppf sheaves and both
projections to `X'` of the space of triples `{(x₁, g, x₂) : φ x₁ = g • φ x₂}` are flat and
locally of finite presentation.

With `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_iff_restrictionAlong` supplied this
is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_groupoidOfAction_iff_exists_cover`. -/
theorem isAlgebraicStack_quotientStack_groupoidOfAction_iff
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left)
    (hgroupoid : ∀ H : GroupoidInAlgebraicSpaces C S hS B,
      IsAlgebraicStack.{u, w} C S hS (quotientStack H) ↔
        ∃ (U' : AlgebraicSpaces C S hS) (g : U' ⟶ H.objects),
          Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
            ((GroupoidInAlgebraicSpaces.fiberProductSnd g H.target ≫ H.source).hom) ∧
          Space.IsFlat C S hS
            (GroupoidInAlgebraicSpaces.restrictionSource H g).hom ∧
          Space.IsFlat C S hS
            (GroupoidInAlgebraicSpaces.restrictionTarget H g).hom ∧
          Space.IsLocallyOfFinitePresentation C S hS
            (GroupoidInAlgebraicSpaces.restrictionSource H g).hom ∧
          Space.IsLocallyOfFinitePresentation C S hS
            (GroupoidInAlgebraicSpaces.restrictionTarget H g).hom) :
    IsAlgebraicStack.{u, w} C S hS
        (quotientStack (Space.groupoidOfAction B G X hG hX).groupoid) ↔
      ∃ (X' : Over B.obj) (_ : IsAlgebraicSpace C S hS X'.left) (φ : X' ⟶ X),
        let a : G ⊗ X' ⟶ X := (𝟙 G ⊗ₘ φ) ≫ γ[G, X]
        Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) a.left ∧
        Space.IsFlat C S hS (pullback.fst φ.left a.left) ∧
        Space.IsLocallyOfFinitePresentation C S hS (pullback.fst φ.left a.left) ∧
        Space.IsFlat C S hS (pullback.snd φ.left a.left ≫ (snd G X').left) ∧
        Space.IsLocallyOfFinitePresentation C S hS
          (pullback.snd φ.left a.left ≫ (snd G X').left) :=
  isAlgebraicStack_quotientStack_action_iff C S hS B G X hG hX
    (Space.groupoidOfAction B G X hG hX) hgroupoid

end AlgebraicGeometry.Stack

end
