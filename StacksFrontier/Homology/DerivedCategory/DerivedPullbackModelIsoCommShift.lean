module

public import StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedNatTransCommShift
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelShiftedHom
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonQuotient
public import StacksFrontier.Homology.PseudoCoherent.BaseChange

/-!
# The comparison of the derived pullback at the two models commutes with the shift

`StacksDraft.DerivedModel.leftDerivedModelIso` compares two total left derived functors, taken
along two localizations `L₁ : K ⥤ D₁` and `L₂ : K ⥤ D₂` at the same class `W`, through
equivalences `G : D₁ ⥤ D₂` and `J : E₁ ⥤ E₂`. When everything in sight commutes with a shift and
the counits and the two comparisons `L₁ ⋙ G ≅ L₂`, `F₁ ⋙ J ≅ F₂` are compatible with it, the
comparison of the derived functors is compatible with it too.

For the two models of the derived category of a Grothendieck abelian category,
`StacksDraft.DerivedModel.shrinkComparisonQhIso` — the identification of the two `Qh` through
`Stacks.Injectives.grothendieckModelEquiv` — commutes with the shift, and so does the comparison
`StacksDraft.DerivedModel.derivedPullbackModelIso f` of `Lf^*` at the two models, each `Lf^*`
carrying the commutation with the shift of a total left derived functor,
`StacksDraft.PseudoCoherence.leftDerivedCommShift`.

## Main results

* `StacksDraft.DerivedModel.leftDerivedModelIso_hom_commShift`: the comparison of two total left
  derived functors commutes with the shift.
* `StacksDraft.DerivedModel.shrinkComparisonQhIso_hom_commShift`: the comparison of the two `Qh`
  commutes with the shift.
* `StacksDraft.DerivedModel.derivedPullbackModelIso_hom_commShift`: the comparison of the two
  `Lf^*` commutes with the shift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u v w

namespace StacksDraft.DerivedModel

/-! ### The abstract statement -/

section Derived

variable {K : Type u} [Category.{v} K] {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {E₁ : Type*} [Category* E₁] {E₂ : Type*} [Category* E₂]
  (W : MorphismProperty K)
  {L₁ : K ⥤ D₁} {L₂ : K ⥤ D₂} [L₁.IsLocalization W] [L₂.IsLocalization W]
  {G : D₁ ⥤ D₂} [G.IsEquivalence] {J : E₁ ⥤ E₂} [J.IsEquivalence]
  (M : Type*) [AddGroup M] [HasShift K M] [HasShift D₁ M] [HasShift D₂ M] [HasShift E₁ M]
  [HasShift E₂ M] [L₁.CommShift M] [L₂.CommShift M] [G.CommShift M] [J.CommShift M]

omit [G.IsEquivalence] in
/-- The counit `transportLeftDerivedCounit α₂ hG` exhibiting `G ⋙ LF₂` as a left derived functor
along `L₁` is compatible with the shift when `α₂` and `hG` are. -/
theorem transportLeftDerivedCounit_commShift {F₂ : K ⥤ E₂} {LF₂ : D₂ ⥤ E₂}
    (α₂ : L₂ ⋙ LF₂ ⟶ F₂) (hG : L₁ ⋙ G ≅ L₂) [F₂.CommShift M] [LF₂.CommShift M]
    [NatTrans.CommShift α₂ M] [NatTrans.CommShift hG.hom M] :
    NatTrans.CommShift (transportLeftDerivedCounit α₂ hG) M :=
  inferInstanceAs (NatTrans.CommShift
    ((Functor.associator L₁ G LF₂).inv ≫ whiskerRight hG.hom LF₂ ≫ α₂) M)

/-- **The comparison of two total left derived functors commutes with the shift.** If the
counits `α₁`, `α₂` and the comparisons `hG : L₁ ⋙ G ≅ L₂`, `hF : F₁ ⋙ J ≅ F₂` are compatible
with the shift, then so is `leftDerivedModelIso W α₁ α₂ hG hF : LF₁ ⋙ J ≅ G ⋙ LF₂`. -/
theorem leftDerivedModelIso_hom_commShift
    {F₁ : K ⥤ E₁} {LF₁ : D₁ ⥤ E₁} (α₁ : L₁ ⋙ LF₁ ⟶ F₁) [LF₁.IsLeftDerivedFunctor α₁ W]
    {F₂ : K ⥤ E₂} {LF₂ : D₂ ⥤ E₂} (α₂ : L₂ ⋙ LF₂ ⟶ F₂) [LF₂.IsLeftDerivedFunctor α₂ W]
    (hG : L₁ ⋙ G ≅ L₂) (hF : F₁ ⋙ J ≅ F₂)
    [F₁.CommShift M] [LF₁.CommShift M] [F₂.CommShift M] [LF₂.CommShift M]
    [hα₁ : NatTrans.CommShift α₁ M] [hα₂ : NatTrans.CommShift α₂ M]
    [hhG : NatTrans.CommShift hG.hom M] [hhF : NatTrans.CommShift hF.hom M] :
    NatTrans.CommShift (leftDerivedModelIso W α₁ α₂ hG hF).hom M := by
  let := isLeftDerivedFunctor_comp_isEquivalence W α₂ hG
  have := transportLeftDerivedCounit_commShift M α₂ hG
  exact Functor.leftDerivedNatTrans_commShift (LF₁ ⋙ J) (G ⋙ LF₂)
    ((Functor.associator L₁ LF₁ J).inv ≫ whiskerRight α₁ J) (transportLeftDerivedCounit α₂ hG)
    W M hF.hom

end Derived

/-! ### The comparison of the two `Qh` -/

section Shrink

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- **The comparison of the two localizations of the homotopy category commutes with the shift.**
Each `Qh` carries its commutation with the shift as a localization, and the comparison
equivalence carries `Stacks.Injectives.grothendieckModelEquivCommShift`. -/
theorem shrinkComparisonQhIso_hom_commShift :
    letI := Stacks.Injectives.grothendieckModelEquivCommShift.{w} C
    NatTrans.CommShift (shrinkComparisonQhIso.{u, v, w} C).hom ℤ := by
  let := Stacks.Injectives.grothendieckModelEquivCommShift.{w} C
  refine NatTrans.commShift_of_whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ)) _ ?_
  refine NatTrans.commShift_of_eq
    (θ := (@DerivedCategory.quotientCompQhIso C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).hom ≫
        (Localization.Lifting.iso (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))
          (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
          (@DerivedCategory.Q C _ _
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C))
          (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor).inv ≫
        whiskerRight (@DerivedCategory.quotientCompQhIso C _ _ (HasDerivedCategory.standard C)).inv
          (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor ≫
        (Functor.associator _ _ _).hom) ?_
  ext K
  refine (shrinkComparisonQhIso_hom_app_quotient C K).trans ?_
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id]
  exact congrArg (fun t => _ ≫ t) (Category.id_comp _).symm

end Shrink

/-! ### The derived pullback -/

section RingedSpaces

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The comparison of the derived pullback at the two models commutes with the shift.** Here
`Lf^*` carries at each model the commutation with the shift of a total left derived functor,
`StacksDraft.PseudoCoherence.leftDerivedCommShift` (at the standard model this is
`Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift`), and the comparison
equivalences carry `Stacks.Injectives.grothendieckModelEquivCommShift`. -/
theorem derivedPullbackModelIso_hom_commShift :
    letI := Stacks.Injectives.grothendieckModelEquivCommShift.{u}
      (SheafOfModules.{u} (structureSheafRing X))
    letI := Stacks.Injectives.grothendieckModelEquivCommShift.{u}
      (SheafOfModules.{u} (structureSheafRing Y))
    letI := StacksDraft.PseudoCoherence.leftDerivedCommShift
      (@derivedPullback X Y f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        inferInstance)
      (@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) inferInstance)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      ℤ
    letI := StacksDraft.PseudoCoherence.leftDerivedCommShift
      (@derivedPullback X Y f
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
      (@derivedPullbackComparison X Y f
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      ℤ
    NatTrans.CommShift (derivedPullbackModelIso f).hom ℤ := by
  let := Stacks.Injectives.grothendieckModelEquivCommShift.{u}
    (SheafOfModules.{u} (structureSheafRing X))
  let := Stacks.Injectives.grothendieckModelEquivCommShift.{u}
    (SheafOfModules.{u} (structureSheafRing Y))
  let := StacksDraft.PseudoCoherence.leftDerivedCommShift
    (@derivedPullback X Y f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      inferInstance)
    (@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) inferInstance)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) ℤ
  let := StacksDraft.PseudoCoherence.leftDerivedCommShift
    (@derivedPullback X Y f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
    (@derivedPullbackComparison X Y f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) ℤ
  have hX : NatTrans.CommShift
      (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).hom ℤ :=
    shrinkComparisonQhIso_hom_commShift _
  have hY : NatTrans.CommShift
      (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).hom ℤ :=
    shrinkComparisonQhIso_hom_commShift _
  have h₁ : NatTrans.CommShift (@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) inferInstance) ℤ :=
    StacksDraft.PseudoCoherence.leftDerivedCommShift_compatibility _ _ _ _
  have h₂ : NatTrans.CommShift (@derivedPullbackComparison X Y f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance) ℤ :=
    StacksDraft.PseudoCoherence.leftDerivedCommShift_compatibility _ _ _ _
  exact leftDerivedModelIso_hom_commShift _ ℤ _ _ _ _
    (hhF := inferInstanceAs (NatTrans.CommShift ((Functor.associator _ _ _).hom ≫
      whiskerLeft _ (shrinkComparisonQhIso
        (SheafOfModules.{u} (structureSheafRing X))).symm.hom) ℤ))

end RingedSpaces

end StacksDraft.DerivedModel

end
