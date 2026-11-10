module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Étale lifts along a tower of thickenings

Let `V ⟶ X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯` be a sequence of thickenings of schemes, that is, of closed
immersions which are surjective on points. By the topological invariance of the étale site,
Stacks 04DZ, base change along each `V ⟶ Xₙ` is an equivalence from the schemes étale over `Xₙ`
to the schemes étale over `V`. So every scheme `W` étale over `V` has an étale lift `Wₙ` to
every stage, unique up to unique isomorphism, and the lifts form a sequence
`W₀ ⟶ W₁ ⟶ W₂ ⟶ ⋯` of closed immersions, `Wₙ` being the base change of `Wₙ₊₁` along
`Xₙ ⟶ Xₙ₊₁`.

## Main definitions

* `AlgebraicGeometry.ThickeningTower`: the data of the tower.
* `AlgebraicGeometry.ThickeningTower.toStage`: the composite `V ⟶ Xₙ`.
* `AlgebraicGeometry.ThickeningTower.lift`: the étale lift `V.Etale ⥤ Xₙ.Etale`, the inverse
  of base change along `V ⟶ Xₙ`.
* `AlgebraicGeometry.ThickeningTower.liftSuccIso`: the lift to `Xₙ` is the lift to `Xₙ₊₁`
  followed by base change along `Xₙ ⟶ Xₙ₊₁`.
* `AlgebraicGeometry.ThickeningTower.transition`: the closed immersion `Wₙ ⟶ Wₙ₊₁`.

## Main results

* `AlgebraicGeometry.ThickeningTower.isThickening_toStage`: each `V ⟶ Xₙ` is a thickening.
* `AlgebraicGeometry.ThickeningTower.isClosedImmersion_transition`: each `Wₙ ⟶ Wₙ₊₁` is a closed
  immersion.
* `AlgebraicGeometry.ThickeningTower.transition_naturality`: the transitions are natural in `W`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

/-- A tower of thickenings `V ⟶ X₀ ⟶ X₁ ⟶ ⋯` below a scheme `V`: a sequence of schemes whose
transition morphisms are thickenings, together with a thickening of `V` into its first term. -/
structure ThickeningTower (V : Scheme.{u}) where
  /-- The schemes of the tower and their transition morphisms. -/
  stage : ℕ ⥤ Scheme.{u}
  /-- The inclusion of `V` into the first stage. -/
  ι : V ⟶ stage.obj 0
  /-- The inclusion of `V` into the first stage is a thickening. -/
  isThickening_ι : Stacks.Thickenings.IsThickening ι
  /-- The transition morphisms are thickenings. -/
  isThickening_succ : ∀ n : ℕ,
    Stacks.Thickenings.IsThickening (stage.map (homOfLE (Nat.le_succ n)))

namespace ThickeningTower

variable {V : Scheme.{u}} (T : ThickeningTower V)

/-- A composite of thickenings is a thickening. -/
theorem _root_.Stacks.Thickenings.IsThickening.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Stacks.Thickenings.IsThickening f) (hg : Stacks.Thickenings.IsThickening g) :
    Stacks.Thickenings.IsThickening (f ≫ g) := by
  have := hf.1
  have := hg.1
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp]
  exact hg.2.comp hf.2

/-- An isomorphism is a thickening. -/
theorem _root_.Stacks.Thickenings.IsThickening.of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] : Stacks.Thickenings.IsThickening f :=
  ⟨inferInstance, (Scheme.homeoOfIso (asIso f)).surjective⟩

/-- Every transition morphism of the tower is a thickening. -/
theorem isThickening_stage_map {i j : ℕ} (h : i ≤ j) :
    Stacks.Thickenings.IsThickening (T.stage.map (homOfLE h)) := by
  induction j, h using Nat.le_induction with
  | base =>
    rw [show homOfLE (le_refl i) = 𝟙 i from rfl, CategoryTheory.Functor.map_id]
    exact .of_isIso _
  | succ j hij ih =>
    rw [show homOfLE (hij.trans (Nat.le_succ j)) = homOfLE hij ≫ homOfLE (Nat.le_succ j) from rfl,
      CategoryTheory.Functor.map_comp]
    exact ih.comp (T.isThickening_succ j)

/-- The composite `V ⟶ Xₙ`. -/
noncomputable def toStage (n : ℕ) : V ⟶ T.stage.obj n :=
  T.ι ≫ T.stage.map (homOfLE (Nat.zero_le n))

/-- The composite `V ⟶ Xₙ₊₁` factors through `V ⟶ Xₙ`. -/
theorem toStage_succ (n : ℕ) :
    T.toStage (n + 1) = T.toStage n ≫ T.stage.map (homOfLE (Nat.le_succ n)) := by
  rw [toStage, toStage, Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

/-- **Each `V ⟶ Xₙ` is a thickening.** -/
theorem isThickening_toStage (n : ℕ) : Stacks.Thickenings.IsThickening (T.toStage n) :=
  T.isThickening_ι.comp (T.isThickening_stage_map (Nat.zero_le n))

/-- Each `V ⟶ Xₙ` is a closed immersion. -/
instance isClosedImmersion_toStage (n : ℕ) : IsClosedImmersion (T.toStage n) :=
  (T.isThickening_toStage n).1

/-- Each `V ⟶ Xₙ` is surjective. -/
instance surjective_toStage (n : ℕ) : Surjective (T.toStage n) :=
  ⟨(T.isThickening_toStage n).2⟩

/-- Each transition `Xₙ ⟶ Xₙ₊₁` of the tower is a closed immersion. -/
instance isClosedImmersion_stage_map (n : ℕ) :
    IsClosedImmersion (T.stage.map (homOfLE (Nat.le_succ n))) :=
  (T.isThickening_succ n).1

/-- **Stacks 04DZ along `V ⟶ Xₙ`.** Base change along the thickening `V ⟶ Xₙ` is an equivalence
of small étale sites. -/
instance isEquivalence_smallEtaleBaseChange_toStage (n : ℕ) :
    (smallEtaleBaseChange (T.toStage n)).IsEquivalence :=
  Stacks.Etale.etalePullback_isEquivalence (T.toStage n)

/-- The étale lift to the stage `Xₙ`: the inverse of base change along `V ⟶ Xₙ`. -/
noncomputable def lift (n : ℕ) : V.Etale ⥤ (T.stage.obj n).Etale :=
  (smallEtaleBaseChange (T.toStage n)).inv

/-- Base change along `V ⟶ Xₙ` of the lift of `W` is `W` again. -/
noncomputable def baseChangeLiftIso (n : ℕ) (W : V.Etale) :
    (smallEtaleBaseChange (T.toStage n)).obj ((T.lift n).obj W) ≅ W :=
  (smallEtaleBaseChange (T.toStage n)).asEquivalence.counitIso.app W

/-- **The lift of an affine scheme étale over `V` is affine.** The base change of the lift along
`V ⟶ Xₙ` is the given affine scheme, and it maps to the lift by a base change of the thickening
`V ⟶ Xₙ`, which is a thickening; a thickening of an affine scheme is affine (Stacks 06AD). -/
theorem isAffine_lift_obj_left (n : ℕ) (W : V.Etale) [IsAffine W.left] :
    IsAffine ((T.lift n).obj W).left := by
  let Z := (T.lift n).obj W
  have e : ((smallEtaleBaseChange (T.toStage n)).obj Z).left ≅ W.left :=
    (Scheme.Etale.forget _ ⋙ Over.forget _).mapIso (T.baseChangeLiftIso n W)
  have : IsAffine ((smallEtaleBaseChange (T.toStage n)).obj Z).left := IsAffine.of_isIso e.hom
  have hthick : Stacks.Thickenings.IsThickening (pullback.fst Z.hom (T.toStage n)) := by
    refine ⟨MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (IsPullback.of_hasPullback _ _).flip (T.isThickening_toStage n).1, ?_⟩
    exact (MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback _ _).flip
      inferInstance : Surjective (pullback.fst Z.hom (T.toStage n))).surj
  exact @Stacks.Thickenings.isAffine_of_isThickening _ _ _ hthick this

/-- The étale lift to `Xₙ` is an equivalence of small étale sites. -/
instance isEquivalence_lift (n : ℕ) : (T.lift n).IsEquivalence := by
  unfold lift
  infer_instance

/-- The étale lift to `Xₙ` preserves pullbacks. -/
instance lift_preservesPullbacks (n : ℕ) : PreservesLimitsOfShape WalkingCospan (T.lift n) :=
  inferInstance

/-- Base change along the transition `Xₙ ⟶ Xₙ₊₁`. -/
noncomputable abbrev stageRestrict (n : ℕ) : (T.stage.obj (n + 1)).Etale ⥤ (T.stage.obj n).Etale :=
  smallEtaleBaseChange (T.stage.map (homOfLE (Nat.le_succ n)))

/-- Base change along `V ⟶ Xₙ₊₁` is base change along `Xₙ ⟶ Xₙ₊₁` followed by base change along
`V ⟶ Xₙ`. -/
noncomputable def smallEtaleBaseChangeSuccIso (n : ℕ) :
    smallEtaleBaseChange (T.toStage (n + 1)) ≅
      T.stageRestrict n ⋙ smallEtaleBaseChange (T.toStage n) :=
  eqToIso (by rw [T.toStage_succ n]; rfl) ≪≫
    (letI : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u})
        (T.toStage n) := ⟨fun _ _ ↦ inferInstance⟩
     letI : MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u})
        (T.toStage n) :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
     letI : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u})
        (T.stage.map (homOfLE (Nat.le_succ n))) := ⟨fun _ _ ↦ inferInstance⟩
     letI : MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u})
        (T.stage.map (homOfLE (Nat.le_succ n))) :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
     letI : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u})
        (T.toStage n ≫ T.stage.map (homOfLE (Nat.le_succ n))) := ⟨fun _ _ ↦ inferInstance⟩
     letI : MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u})
        (T.toStage n ≫ T.stage.map (homOfLE (Nat.le_succ n))) :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
     MorphismProperty.Over.pullbackComp (T.toStage n) (T.stage.map (homOfLE (Nat.le_succ n))))

/-- **The lift to `Xₙ` is the base change of the lift to `Xₙ₊₁`.** -/
noncomputable def liftSuccIso (n : ℕ) : T.lift n ≅ T.lift (n + 1) ⋙ T.stageRestrict n :=
  let F := smallEtaleBaseChange (T.toStage n)
  let F' := smallEtaleBaseChange (T.toStage (n + 1))
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (F'.asEquivalence.counitIso).symm (T.lift n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (T.lift (n + 1))
      (Functor.isoWhiskerRight (T.smallEtaleBaseChangeSuccIso n) (T.lift n) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (T.stageRestrict n) F.asEquivalence.unitIso.symm ≪≫
        Functor.rightUnitor _)

/-- The closed immersion `Wₙ ⟶ Wₙ₊₁` from the lift of `W` to `Xₙ` into its lift to `Xₙ₊₁`. -/
noncomputable def transition (n : ℕ) (W : V.Etale) :
    ((T.lift n).obj W).left ⟶ ((T.lift (n + 1)).obj W).left :=
  ((T.liftSuccIso n).hom.app W).left ≫
    pullback.fst ((T.lift (n + 1)).obj W).hom (T.stage.map (homOfLE (Nat.le_succ n)))

/-- The transition `Wₙ ⟶ Wₙ₊₁` lies over the transition `Xₙ ⟶ Xₙ₊₁` of the tower. -/
@[reassoc]
theorem transition_hom (n : ℕ) (W : V.Etale) :
    T.transition n W ≫ ((T.lift (n + 1)).obj W).hom =
      ((T.lift n).obj W).hom ≫ T.stage.map (homOfLE (Nat.le_succ n)) := by
  have hw : ((T.liftSuccIso n).hom.app W).left ≫
      pullback.snd ((T.lift (n + 1)).obj W).hom (T.stage.map (homOfLE (Nat.le_succ n))) =
      ((T.lift n).obj W).hom :=
    MorphismProperty.Over.w ((T.liftSuccIso n).hom.app W)
  calc T.transition n W ≫ ((T.lift (n + 1)).obj W).hom
      = ((T.liftSuccIso n).hom.app W).left ≫
          (pullback.fst ((T.lift (n + 1)).obj W).hom (T.stage.map (homOfLE (Nat.le_succ n))) ≫
            ((T.lift (n + 1)).obj W).hom) := Category.assoc _ _ _
    _ = ((T.liftSuccIso n).hom.app W).left ≫
          (pullback.snd ((T.lift (n + 1)).obj W).hom (T.stage.map (homOfLE (Nat.le_succ n))) ≫
            T.stage.map (homOfLE (Nat.le_succ n))) := congrArg _ pullback.condition
    _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hw)

/-- **The transition `Wₙ ⟶ Wₙ₊₁` is a closed immersion.** -/
instance isClosedImmersion_transition (n : ℕ) (W : V.Etale) :
    IsClosedImmersion (T.transition n W) := by
  have h : IsIso ((T.liftSuccIso n).hom.app W).left :=
    inferInstanceAs (IsIso ((Scheme.Etale.forget _ ⋙ Over.forget _).map
      ((T.liftSuccIso n).hom.app W)))
  have hp : IsClosedImmersion (pullback.fst ((T.lift (n + 1)).obj W).hom
      (T.stage.map (homOfLE (Nat.le_succ n)))) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (IsPullback.of_hasPullback _ _).flip (T.isThickening_succ n).1
  exact @IsClosedImmersion.comp _ _ _ _ _ inferInstance hp

/-- The transitions are natural in the scheme étale over `V`. -/
@[reassoc]
theorem transition_naturality (n : ℕ) {W W' : V.Etale} (g : W ⟶ W') :
    ((T.lift n).map g).left ≫ T.transition n W' =
      T.transition n W ≫ ((T.lift (n + 1)).map g).left := by
  have h₁ : ((T.lift n).map g).left ≫ ((T.liftSuccIso n).hom.app W').left =
      ((T.liftSuccIso n).hom.app W).left ≫
        ((T.stageRestrict n).map ((T.lift (n + 1)).map g)).left :=
    congrArg (fun φ ↦ φ.left) ((T.liftSuccIso n).hom.naturality g)
  have h₂ : ((T.stageRestrict n).map ((T.lift (n + 1)).map g)).left ≫
      pullback.fst ((T.lift (n + 1)).obj W').hom (T.stage.map (homOfLE (Nat.le_succ n))) =
      pullback.fst ((T.lift (n + 1)).obj W).hom (T.stage.map (homOfLE (Nat.le_succ n))) ≫
        ((T.lift (n + 1)).map g).left :=
    (congrArg (· ≫ pullback.fst ((T.lift (n + 1)).obj W').hom
      (T.stage.map (homOfLE (Nat.le_succ n)))) (smallEtaleBaseChange_map_left _ _)).trans
      (pullback.lift_fst _ _ _)
  calc ((T.lift n).map g).left ≫ T.transition n W'
      = (((T.lift n).map g).left ≫ ((T.liftSuccIso n).hom.app W').left) ≫
          pullback.fst ((T.lift (n + 1)).obj W').hom (T.stage.map (homOfLE (Nat.le_succ n))) :=
        (Category.assoc _ _ _).symm
    _ = ((T.liftSuccIso n).hom.app W).left ≫
          (((T.stageRestrict n).map ((T.lift (n + 1)).map g)).left ≫
            pullback.fst ((T.lift (n + 1)).obj W').hom (T.stage.map (homOfLE (Nat.le_succ n)))) :=
        (congrArg (· ≫ pullback.fst ((T.lift (n + 1)).obj W').hom
          (T.stage.map (homOfLE (Nat.le_succ n)))) h₁).trans (Category.assoc _ _ _)
    _ = T.transition n W ≫ ((T.lift (n + 1)).map g).left :=
        (congrArg (((T.liftSuccIso n).hom.app W).left ≫ ·) h₂).trans
          (Category.assoc _ _ _).symm

/-- **Lifts of a jointly surjective family are jointly surjective.** If a family of morphisms of
schemes étale over `V` is jointly surjective, so is the family of their lifts to `Xₙ`. -/
theorem lift_jointlySurjective (n : ℕ) {ι : Type*} {Z : ι → V.Etale} {W : V.Etale}
    (g : ∀ i, Z i ⟶ W) (h : ∀ x : W.left, ∃ i, ∃ y : (Z i).left, (g i).left y = x) :
    ∀ x : ((T.lift n).obj W).left, ∃ i, ∃ y : ((T.lift n).obj (Z i)).left,
      ((T.lift n).map (g i)).left y = x := by
  intro x
  let F := smallEtaleBaseChange (T.toStage n)
  let G := T.lift n
  obtain ⟨p, hp⟩ := (MorphismProperty.of_isPullback (P := @Surjective)
    (IsPullback.of_hasPullback _ _).flip inferInstance :
      Surjective (pullback.fst (G.obj W).hom (T.toStage n))).surj x
  let cW := (T.baseChangeLiftIso n W).hom.left
  obtain ⟨i, y, hy⟩ := h (cW p)
  let cZ := (T.baseChangeLiftIso n (Z i)).inv.left
  have hnat : (F.map (G.map (g i))).left ≫ cW = (T.baseChangeLiftIso n (Z i)).hom.left ≫
      (g i).left :=
    congrArg (fun φ ↦ φ.left) (F.asEquivalence.counitIso.hom.naturality (g i))
  have hq : (F.map (G.map (g i))).left (cZ y) = p := by
    have hinj : Function.Injective cW := by
      have : IsIso cW := inferInstanceAs (IsIso ((Scheme.Etale.forget _ ⋙ Over.forget _).map
        (T.baseChangeLiftIso n W).hom))
      exact (ConcreteCategory.bijective_of_isIso cW.base).1
    apply hinj
    rw [← Scheme.Hom.comp_apply, hnat, Scheme.Hom.comp_apply]
    change (g i).left (((T.baseChangeLiftIso n (Z i)).inv ≫
      (T.baseChangeLiftIso n (Z i)).hom).left y) = cW p
    rw [Iso.inv_hom_id]
    exact hy
  exact ⟨i, pullback.fst (G.obj (Z i)).hom (T.toStage n) (cZ y),
    (smallEtaleBaseChange_map_left_apply (T.toStage n) (G.map (g i)) (cZ y)).trans
      ((congrArg _ hq).trans hp)⟩

end ThickeningTower

end AlgebraicGeometry

end
