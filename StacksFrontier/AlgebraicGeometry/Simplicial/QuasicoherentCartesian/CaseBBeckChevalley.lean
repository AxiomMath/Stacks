module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseBSlice
public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.RanBaseChangeMate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunctionUnderlying

/-!
# The Beck–Chevalley comparison of case (B) is invertible

The square formed by the transition `u_φ`, the localized transition `h` and the two forgetful
functors from slices commutes. The base change of Stacks 0FN1 is a comparison
`(f_* M)|_Q ⟶ h_*(M|_W)` of modules; its mate along the transition pullbacks is the Beck–Chevalley
comparison `h^*(G|_Q) ⟶ (f^*G)|_W`, and its mate along the restrictions to slices is, on underlying
presheaves, the mate of a base change of right Kan extensions, which is invertible by
`Stacks.Sites.CocontinuousExchange.isIso_mateEquiv_ranBaseChange`. Since iterated mates are
conjugates, the Beck–Chevalley comparison is invertible.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.CartesianSlice.isIso_beckChevalleyB`.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 03EG](https://stacks.math.columbia.edu/tag/03EG)
* [Stacks Project, Tag 0FN1](https://stacks.math.columbia.edu/tag/0FN1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

/-- A mate, at one object, is the transpose of the 2-cell followed by the counit. -/
theorem mateEquiv_natTrans_app_eq_homEquiv {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁}
    {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)
    (X : C₂) :
    (mateEquiv adj₁ adj₂ α).natTrans.app X =
      adj₂.homEquiv _ _ (α.natTrans.app (R₁.obj X) ≫ H.map (adj₁.counit.app X)) := by
  have h1 := mateEquiv_counit adj₁ adj₂ α X
  refine (adj₂.homEquiv _ _).symm.injective ?_
  exact ((Adjunction.homEquiv_counit _ _ _ _).trans h1).trans
    (Equiv.symm_apply_apply _ _).symm

end CategoryTheory

namespace CategoryTheory.CocontinuousSimplicialSite.CartesianSlice

variable (C : CocontinuousSimplicialSite.{u})
  (P : Sheaf (situation C).totalTopology CommRingCat.{u})
  {n m : SimplexCategory} (φ : n ⟶ m) {W : (situation C).component m}
  {Q : (situation C).component n} (b : (transitionFunctorB C φ).obj W ⟶ Q)

/-- Restriction of modules on a component to a slice, as the left adjoint of the direct image
along `Over.forget`. -/
abbrev overRestrictionAdjB (k : SimplexCategory) (X : (situation C).component k) :=
  Stacks.SheafOfModules.RestrictRan.sheafAdjunction (Over.forget X)
    (((situation C).componentTopology k).over X) ((situation C).componentTopology k)
    (ringSheafB C P k)

/-- The direct image of modules along the transition of case (B). -/
abbrev transitionPushforwardB :
    SheafOfModules.{u} (ringSheafB C P m) ⥤ SheafOfModules.{u} (ringSheafB C P n) :=
  Stacks.SheafOfModules.pushforwardCocontinuous.{u} (transitionFunctorB C φ) (fSharpB C P φ)

/-- **The square of direct images and restrictions to slices**: the base change of Stacks 0FN1. -/
def sliceSquare :
    TwoSquare (transitionPushforwardB C P φ)
      (Stacks.SheafOfModules.inverseImage.{u} (((situation C).componentTopology m).over W)
        ((situation C).componentTopology m) (Over.forget W) (ringSheafB C P m))
      (Stacks.SheafOfModules.inverseImage.{u} (((situation C).componentTopology n).over Q)
        ((situation C).componentTopology n) (Over.forget Q) (ringSheafB C P n))
      (slicePushforward C P φ b) :=
  TwoSquare.mk _ _ _ _ (Stacks.SheafOfModules.squareComparison
    (J' := ((situation C).componentTopology m).over W)
    (K' := ((situation C).componentTopology n).over Q) (fSharpB C P φ)
    (sliceTransition_comp_forget C φ b))

/-- **The Beck–Chevalley comparison of case (B)** `h^*(M|_Q) ⟶ (f^*M)|_W`. -/
def beckChevalleyB :
    TwoSquare
      (Stacks.SheafOfModules.inverseImage.{u} (((situation C).componentTopology n).over Q)
        ((situation C).componentTopology n) (Over.forget Q) (ringSheafB C P n))
      (transitionModulePullbackB C P n m φ) (slicePullback C P φ b)
      (Stacks.SheafOfModules.inverseImage.{u} (((situation C).componentTopology m).over W)
        ((situation C).componentTopology m) (Over.forget W) (ringSheafB C P m)) :=
  (mateEquiv (transitionModulePullbackAdjunctionB C P φ) (slicePullbackAdj C P φ b)).symm
    (sliceSquare C P φ b)

/-- The mate of the square along the restrictions to slices. -/
def sliceSquareMate :=
  mateEquiv (overRestrictionAdjB C P m W) (overRestrictionAdjB C P n Q) (sliceSquare C P φ b)

/-- The module-level mate has the presheaf-level one underneath. -/
theorem toPresheaf_map_sliceSquareMate_app (N : SheafOfModules.{u} ((ringSheafB C P m).over W)) :
    (PresheafOfModules.toPresheaf _).map ((sliceSquareMate C P φ b).natTrans.app N).val =
      (mateEquiv ((Over.forget W).op.ranAdjunction AddCommGrpCat.{u})
        ((Over.forget Q).op.ranAdjunction AddCommGrpCat.{u})
        (TwoSquare.mk _ _ _ _ ((Stacks.Sites.CocontinuousExchange.twoSquare
          (sliceTransition_comp_forget C φ b)).op.ranBaseChange
            (D := AddCommGrpCat.{u})))).natTrans.app
        N.val.presheaf := by
  have hc : (PresheafOfModules.toPresheaf _).map
      ((overRestrictionAdjB C P m W).counit.app N).val =
      ((Over.forget W).op.ranAdjunction AddCommGrpCat.{u}).counit.app N.val.presheaf :=
    (congrArg (PresheafOfModules.toPresheaf _).map
      (Stacks.SheafOfModules.RestrictRan.sheafAdjunction_counit_app_val _ _ _ _ N)).trans
      (Stacks.SheafOfModules.RestrictRan.toPresheaf_map_adjunction_counit_app _ _ N.val)
  refine (congrArg (fun f => (PresheafOfModules.toPresheaf _).map f.val)
    (mateEquiv_natTrans_app_eq_homEquiv _ _ (sliceSquare C P φ b) N)).trans ?_
  refine (congrArg (PresheafOfModules.toPresheaf _).map
    (Stacks.SheafOfModules.RestrictRan.sheafAdjunction_homEquiv_val _ _ _ _ _)).trans ?_
  refine (Stacks.SheafOfModules.RestrictRan.toPresheaf_map_adjunction_homEquiv _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (mateEquiv_natTrans_app_eq_homEquiv
    ((Over.forget W).op.ranAdjunction AddCommGrpCat.{u})
    ((Over.forget Q).op.ranAdjunction AddCommGrpCat.{u})
    (TwoSquare.mk _ _ _ _ ((Stacks.Sites.CocontinuousExchange.twoSquare
      (sliceTransition_comp_forget C φ b)).op.ranBaseChange (D := AddCommGrpCat.{u})))
    N.val.presheaf).symm
  refine congrArg (((Over.forget Q).op.ranAdjunction AddCommGrpCat.{u}).homEquiv _ _) ?_
  refine Eq.trans ?_ (congrArg (fun t => (Stacks.Sites.CocontinuousExchange.twoSquare
        (sliceTransition_comp_forget C φ b)).op.ranBaseChange.app
          ((Over.forget W).op.ran.obj N.val.presheaf) ≫ (sliceTransition C φ b).op.ran.map t) hc)
  rfl

/-- **The mate of the square along the restrictions to slices is invertible.** -/
theorem isIso_sliceSquareMate : IsIso (sliceSquareMate C P φ b).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
  have hiso := Stacks.Sites.CocontinuousExchange.isIso_mateEquiv_ranBaseChange
    (sliceTransition_comp_forget C φ b) AddCommGrpCat.{u}
  have happ := @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hiso N.val.presheaf
  have h := toPresheaf_map_sliceSquareMate_app C P φ b N
  have : IsIso ((PresheafOfModules.toPresheaf _).map
      ((sliceSquareMate C P φ b).natTrans.app N).val) := h ▸ happ
  exact this

/-- **The Beck–Chevalley comparison of case (B) is invertible.** -/
theorem isIso_beckChevalleyB : IsIso (beckChevalleyB C P φ b).natTrans := by
  have h := iterated_mateEquiv_conjugateEquiv
    (transitionModulePullbackAdjunctionB C P φ) (slicePullbackAdj C P φ b)
    (overRestrictionAdjB C P n Q) (overRestrictionAdjB C P m W) (beckChevalleyB C P φ b)
  have e : sliceSquareMate C P φ b =
      mateEquiv (overRestrictionAdjB C P m W) (overRestrictionAdjB C P n Q)
        (mateEquiv (transitionModulePullbackAdjunctionB C P φ) (slicePullbackAdj C P φ b)
          (beckChevalleyB C P φ b)) :=
    congrArg (mateEquiv (overRestrictionAdjB C P m W) (overRestrictionAdjB C P n Q))
      ((mateEquiv (transitionModulePullbackAdjunctionB C P φ)
        (slicePullbackAdj C P φ b)).apply_symm_apply (sliceSquare C P φ b)).symm
  have := isIso_sliceSquareMate C P φ b
  have : IsIso (conjugateEquiv
      ((transitionModulePullbackAdjunctionB C P φ).comp (overRestrictionAdjB C P m W))
      ((overRestrictionAdjB C P n Q).comp (slicePullbackAdj C P φ b))
      (beckChevalleyB C P φ b).natTrans) := by
    rw [← h, ← e]
    infer_instance
  exact conjugateEquiv_of_iso
    ((transitionModulePullbackAdjunctionB C P φ).comp (overRestrictionAdjB C P m W))
    ((overRestrictionAdjB C P n Q).comp (slicePullbackAdj C P φ b))
    (beckChevalleyB C P φ b).natTrans

end CategoryTheory.CocontinuousSimplicialSite.CartesianSlice
