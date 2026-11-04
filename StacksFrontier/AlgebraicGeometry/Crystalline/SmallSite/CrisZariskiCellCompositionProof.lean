module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImageCompCellSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiFlatteningSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareComposition

/-!
# The coherence of the three squares of topoi of [Stacks, Tag 07Q9] under composition

For composable morphisms `f₁` and `f₂` of global crystalline situations, the `2`-cell of the
square of topoi for `f₁ ≫ f₂`, followed by `u_{X₀/S₀, *}` of the comparison
`...SmallSite.crisDirectImageCompCell` of the crystalline direct images, is the pasting of the
cells of `f₁` and of `f₂` across `...SmallSite.zariskiPushforwardComp`. Consequently the
comparison map of [Stacks, Tag 07Q9] is functorial under composition, with no hypotheses.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crisDirectImage_obj_obj_hom_ext`: two maps into the sections of `f_{cris, *}ℋ` over an object
  of the small crystalline site agree as soon as they agree against every domination.
* `crisZariskiCellComp`: the coherence, for every composable pair of morphisms of the global
  crystalline situations of [Stacks, Tag 07I5].
* `zariskiComparison_comp'`: the composition functoriality of the comparison map of
  [Stacks, Tag 07Q9].

## References

* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S₂ S₁ S₀ : GlobalCrystallineSituation.{u}}
  {f₁S : S₂.S ⟶ S₁.S} {f₁X : S₂.X ⟶ S₁.X}
  {f₂S : S₁.S ⟶ S₀.S} {f₂X : S₁.X ⟶ S₀.X}
  (h₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁S = f₁X ≫ S₁.toClosedFiber)
  (h₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂S = f₂X ≫ S₀.toClosedFiber)

/-- **The sections of `f_{cris, *}ℋ` over an object of the small crystalline site are determined
by the counits.**  Two maps into these sections agree as soon as they agree after restriction
along every domination of the object by an object of `Cris(X₂/S₂)` after change of divided power
base, followed by the counits of `f_{CRIS, *}` and of `i_{X₂, *}`. -/
theorem crisDirectImage_obj_obj_hom_ext (ℋ : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1})
    (C : (CrystallineThickening S₁)ᵒᵖ) {Z : AddCommGrpCat.{u + 1}}
    {α β : Z ⟶ ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj ℋ).obj.obj C}
    (h : ∀ d' : StructuredArrow ((CrystallineThickening.ι S₁).op.obj C)
        ((CrystallineThickening.ι S₂).op ⋙ (changeBase S₂ S₁ f₁S f₁X h₁).op),
      α ≫ ((changeBase S₂ S₁ f₁S f₁X h₁).op.ran.obj
            ((CrystallineThickening.ι S₂).op.ran.obj ℋ.obj)).map d'.hom ≫
          ((changeBase S₂ S₁ f₁S f₁X h₁).op.ranCounit.app
              ((CrystallineThickening.ι S₂).op.ran.obj ℋ.obj)).app
            ((CrystallineThickening.ι S₂).op.obj d'.right) ≫
            ((CrystallineThickening.ι S₂).op.ranCounit.app ℋ.obj).app d'.right =
        β ≫ ((changeBase S₂ S₁ f₁S f₁X h₁).op.ran.obj
            ((CrystallineThickening.ι S₂).op.ran.obj ℋ.obj)).map d'.hom ≫
          ((changeBase S₂ S₁ f₁S f₁X h₁).op.ranCounit.app
              ((CrystallineThickening.ι S₂).op.ran.obj ℋ.obj)).app
            ((CrystallineThickening.ι S₂).op.obj d'.right) ≫
            ((CrystallineThickening.ι S₂).op.ranCounit.app ℋ.obj).app d'.right) :
    α = β :=
  Functor.ran_comp_obj_obj_hom_ext (CrystallineThickening.ι S₂).op
    (changeBase S₂ S₁ f₁S f₁X h₁).op ℋ.obj ((CrystallineThickening.ι S₁).op.obj C) h

/-- Pasting of the commuting squares and cells used in `crisZariskiCellComp`, in an abstract
category. -/
private theorem paste_cell_squares {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ X₁₀ X₁₁ X₁₂ X₁₃ Z₁ Z₂ W₁ W₂ : C}
    {a : X₀ ⟶ X₁} {n : X₁ ⟶ X₂} {M : X₂ ⟶ X₃} {M' : X₁ ⟶ X₄} {w : X₄ ⟶ X₃}
    {ρ : X₃ ⟶ X₅} {ρ' : X₄ ⟶ X₆} {c : X₆ ⟶ X₅} {R₁ : X₅ ⟶ X₇} {R₂ : X₇ ⟶ X₈}
    {R₃ : X₈ ⟶ X₉} {K₁ : X₉ ⟶ X₁₀} {K₂ : X₁₀ ⟶ X₁₁} {K₃ : X₁₁ ⟶ X₁₂}
    {U₁ : X₆ ⟶ X₁₃} {U₂ : X₁₃ ⟶ X₁₁} {z : X₀ ⟶ Z₁} {c₁ : Z₁ ⟶ Z₂} {c₂ : Z₂ ⟶ X₂}
    {Y : Z₂ ⟶ W₁} {ρ₁ : W₁ ⟶ X₉} {Y' : Z₁ ⟶ W₂} {ρ₂ : W₂ ⟶ X₁₂} {Y'' : X₀ ⟶ W₂}
    {G P : X₀ ⟶ X₂}
    (hnat₁ : n ≫ M = M' ≫ w) (hnat₂ : w ≫ ρ = ρ' ≫ c)
    (hK : c ≫ R₁ ≫ R₂ ≫ R₃ ≫ K₁ ≫ K₂ = U₁ ≫ U₂)
    (hF : a ≫ M' ≫ ρ' ≫ U₁ ≫ U₂ ≫ K₃ = Y'' ≫ ρ₂)
    (h₂ : c₂ ≫ M ≫ ρ ≫ R₁ ≫ R₂ ≫ R₃ = Y ≫ ρ₁)
    (h₁ : c₁ ≫ Y ≫ ρ₁ ≫ K₁ ≫ K₂ ≫ K₃ = Y' ≫ ρ₂) (h₀ : z ≫ Y' = Y'')
    (hG : G = a ≫ n) (hP : P = z ≫ c₁ ≫ c₂) :
    (G ≫ M ≫ ρ ≫ R₁ ≫ R₂ ≫ R₃) ≫ K₁ ≫ K₂ ≫ K₃ = (P ≫ M ≫ ρ ≫ R₁ ≫ R₂ ≫ R₃) ≫ K₁ ≫ K₂ ≫ K₃ := by
  have e₁ : (G ≫ M ≫ ρ ≫ R₁ ≫ R₂ ≫ R₃) ≫ K₁ ≫ K₂ ≫ K₃ = Y'' ≫ ρ₂ := by
    rw [← hF, hG]
    simp only [Category.assoc]
    rw [reassoc_of% hnat₁, reassoc_of% hnat₂, reassoc_of% hK]
  have e₂ : (P ≫ M ≫ ρ ≫ R₁ ≫ R₂ ≫ R₃) ≫ K₁ ≫ K₂ ≫ K₃ = Y'' ≫ ρ₂ := by
    rw [← h₀, Category.assoc z Y' ρ₂, ← h₁, hP]
    simp only [Category.assoc]
    rw [reassoc_of% h₂]
  exact e₁.trans e₂.symm

/-- **The coherence of the three squares of topoi of [Stacks, Tag 07Q9] under composition.**

The `2`-cell of the square for `f₁ ≫ f₂`, followed by `u_{X₀/S₀, *}` of the comparison
`crisDirectImageCompCell`, is the pasting `crisZariskiCellPastingApp` of the cells of `f₁` and of
`f₂` across `zariskiPushforwardComp`. -/
theorem crisZariskiCellComp : CrisZariskiCellComp h₁ h₂ := by
  intro ℋ
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ?_))
  obtain ⟨V⟩ := V
  rw [← cancel_mono (crisZariskiLeftObjIso S₁ S₀ f₂S f₂X h₂
    ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj ℋ) V).hom]
  refine limit.hom_ext fun d ↦ ?_
  rw [Category.assoc, Category.assoc, crisZariskiLeftObjIso_hom_comp_π]
  refine crisDirectImage_obj_obj_hom_ext h₁ ℋ d.right.right fun d' ↦ ?_
  have hV : (forgetToOpens S₀).obj d.right.left.unop ≤ V := leOfHom d.hom.unop
  have hVA : (forgetToOpens S₁).obj d.right.right.unop ≤ f₂X ⁻¹ᵁ V :=
    dominationPairs_le_preimage S₁ S₀ f₂S f₂X h₂ V d
  have hC : ∀ z : d.right.right.unop.obj.thickening.source,
      d.right.right.unop.obj.toX.base z ∈ f₂X ⁻¹ᵁ V := fun z ↦ hVA ⟨z, rfl⟩
  have hVA' : (forgetToOpens S₂).obj d'.right.unop ≤ f₁X ⁻¹ᵁ (f₂X ⁻¹ᵁ V) :=
    dominationPairs_le_preimage S₂ S₁ f₁S f₁X h₁ (f₂X ⁻¹ᵁ V)
      (dominationStructuredArrow S₂ S₁ f₁S f₁X h₁ (f₂X ⁻¹ᵁ V) d'.right.unop
        d.right.right.unop hC d'.hom.unop)
  have hVD : (forgetToOpens S₂).obj d'.right.unop ≤ (f₁X ≫ f₂X) ⁻¹ᵁ V := hVA'
  have hzpc :
      ((zariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X)).inv.app
        ((zariskiDirectImage S₂).obj ℋ)).hom.app (op V) =
      ((forgetToOpens S₂).op.ran.obj ℋ.obj).map
        ((TopologicalSpace.Opens.mapComp f₁X.base f₂X.base).symm.hom.app V).op :=
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app _ _ _ _ _ _ _
  have hm00 :
      ((zariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X)).inv.app
        ((zariskiDirectImage S₂).obj ℋ)).hom.app (op V) ≫
      ((forgetToOpens S₂).op.ran.obj ℋ.obj).map (homOfLE hVA').op =
      ((forgetToOpens S₂).op.ran.obj ℋ.obj).map (homOfLE hVD).op := by
    rw [hzpc]
    refine Eq.trans (((forgetToOpens S₂).op.ran.obj ℋ.obj).map_comp _ _).symm ?_
    exact congrArg (fun g ↦ ((forgetToOpens S₂).op.ran.obj ℋ.obj).map g)
      (Subsingleton.elim _ _)
  have hnat1 := (((forgetToOpens S₀).op.ran.map
    ((crisDirectImageCompCell h₁ h₂).app ℋ).hom).naturality (homOfLE hV).op).symm
  have hnat2 := NatTrans.congr_app ((forgetToOpens S₀).op.ranCounit.naturality
    ((crisDirectImageCompCell h₁ h₂).app ℋ).hom) d.right.left
  have hKEYb := crisDirectImageCompCell_app_hom_app_comp_ranCounit h₁ h₂ ℋ d.right.left.unop
      d.right.right.unop d'.right.unop d.right.hom.unop d'.hom.unop
  have hcellF := crisZariskiCell_app_hom_app_comp_ranCounit S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
      (comp_closedFiber_compat h₁ h₂) ℋ V d.right.left.unop d'.right.unop
      (compDomination h₁ h₂ d.right.left.unop d.right.right.unop
            d'.right.unop d.right.hom.unop d'.hom.unop) hV hVD
  have hcell2 := crisZariskiCell_app_hom_app_comp_ranCounit S₁ S₀ f₂S f₂X h₂
      ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj ℋ) V d.right.left.unop
      d.right.right.unop d.right.hom.unop hV hVA
  have hcell1 := crisZariskiCell_app_hom_app_comp_ranCounit S₂ S₁ f₁S f₁X h₁ ℋ (f₂X ⁻¹ᵁ V)
      d.right.right.unop d'.right.unop d'.hom.unop hVA hVA'
  exact paste_cell_squares hnat1 hnat2 hKEYb hcellF hcell2 hcell1 hm00 rfl rfl

/-- **The composition functoriality of the comparison map of [Stacks, Tag 07Q9]**, with no
hypotheses: the comparison map of the composite cover `f₁ ≫ f₂` is the comparison map of `f₂`,
followed by `f₂_{Zar, *}` of the comparison map of `f₁`, read through the composition isomorphism
`zariskiPushforwardComp` of the Zariski direct images and the composition comparison
`crisInverseImageCompCell` of the crystalline inverse images. -/
theorem zariskiComparison_comp' (F : Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1}) :
    zariskiComparison S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂)
        (crisZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
          (comp_closedFiber_compat h₁ h₂)) F =
      zariskiComparison S₁ S₀ f₂S f₂X h₂ (crisZariskiSquare S₁ S₀ f₂S f₂X h₂) F ≫
        (zariskiPushforward S₁ S₀ f₂X).map
            (zariskiComparison S₂ S₁ f₁S f₁X h₁ (crisZariskiSquare S₂ S₁ f₁S f₁X h₁)
              (crisPullback S₁ S₀ f₂S f₂X h₂ F)) ≫
          (zariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X)).hom.app
            ((zariskiDirectImage S₂).obj
              (crisPullback S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F))) ≫
          (zariskiPushforward S₂ S₀ (f₁X ≫ f₂X)).map
            ((zariskiDirectImage S₂).map ((crisInverseImageCompCell h₁ h₂).app F)) :=
  zariskiComparison_comp h₁ h₂ (crisZariskiCellComp h₁ h₂) F

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
