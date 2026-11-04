module

public import StacksFrontier.CategoryTheory.Functor.Derived.BaseChangePasting

/-!
# Pasting of composition comparisons of right derived functors

Let `Q₁, …, Q₄` be localization functors and let `F₁ : K₁ ⥤ K₂`, `G₁ : K₂ ⥤ K₃`,
`H₁ : K₃ ⥤ K₄`, `F₂ : K₁ ⥤ K₃`, `F₃ : K₁ ⥤ K₄`, `G₂ : K₂ ⥤ K₄` be functors with right derived
functors. For isomorphisms `a : F₁ ⋙ G₁ ≅ F₂`, `b : F₂ ⋙ H₁ ≅ F₃`, `c : F₁ ⋙ G₂ ≅ F₃` and
`d : G₁ ⋙ H₁ ≅ G₂` which paste, the two comparisons `RF₃ ⟶ RF₁ ⋙ RG₁ ⋙ RH₁` of
[Stacks, Tag 05T2] — through `RF₂` and through `RG₂` — agree. This is the coherence behind the
compatibility of the maps of [Stacks, Tag 0F7G] with composition.

## Main results

* `Stacks.DerivedBaseChange.compComparison_paste`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedBaseChange

variable {K₁ : Type*} [Category* K₁] {K₂ : Type*} [Category* K₂]
  {K₃ : Type*} [Category* K₃] {K₄ : Type*} [Category* K₄]
  {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {D₃ : Type*} [Category* D₃] {D₄ : Type*} [Category* D₄]
  {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} {Q₃ : K₃ ⥤ D₃} {Q₄ : K₄ ⥤ D₄}
  {F₁ : K₁ ⥤ K₂} {RF₁ : D₁ ⥤ D₂} {G₁ : K₂ ⥤ K₃} {RG₁ : D₂ ⥤ D₃}
  {H₁ : K₃ ⥤ K₄} {RH₁ : D₃ ⥤ D₄} {F₂ : K₁ ⥤ K₃} {RF₂ : D₁ ⥤ D₃}
  {F₃ : K₁ ⥤ K₄} {RF₃ : D₁ ⥤ D₄} {G₂ : K₂ ⥤ K₄} {RG₂ : D₂ ⥤ D₄}
  (W₁ : MorphismProperty K₁) [Q₁.IsLocalization W₁]
  (W₂ : MorphismProperty K₂) [Q₂.IsLocalization W₂]

/-- **Pasting of composition comparisons.** -/
theorem compComparison_paste
    (αF₁ : F₁ ⋙ Q₂ ⟶ Q₁ ⋙ RF₁) (αG₁ : G₁ ⋙ Q₃ ⟶ Q₂ ⋙ RG₁) (αH₁ : H₁ ⋙ Q₄ ⟶ Q₃ ⋙ RH₁)
    (αF₂ : F₂ ⋙ Q₃ ⟶ Q₁ ⋙ RF₂) (αF₃ : F₃ ⋙ Q₄ ⟶ Q₁ ⋙ RF₃) (αG₂ : G₂ ⋙ Q₄ ⟶ Q₂ ⋙ RG₂)
    [RF₂.IsRightDerivedFunctor αF₂ W₁] [RF₃.IsRightDerivedFunctor αF₃ W₁]
    [RG₂.IsRightDerivedFunctor αG₂ W₂]
    (a : F₁ ⋙ G₁ ≅ F₂) (b : F₂ ⋙ H₁ ≅ F₃) (c : F₁ ⋙ G₂ ≅ F₃) (d : G₁ ⋙ H₁ ≅ G₂)
    (h : ∀ X : K₁, H₁.map (a.hom.app X) ≫ b.hom.app X = d.hom.app (F₁.obj X) ≫ c.hom.app X) :
    compComparison W₁ αF₂ αH₁ αF₃ b ≫
        Functor.whiskerRight (compComparison W₁ αF₁ αG₁ αF₂ a) RH₁ =
      compComparison W₁ αF₁ αG₂ αF₃ c ≫
        Functor.whiskerLeft RF₁ (compComparison W₂ αG₁ αH₁ αG₂ d) := by
  apply RF₃.rightDerived_ext αF₃ W₁
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have hn := αH₁.naturality (a.inv.app X)
  have hd := (compComparison W₂ αG₁ αH₁ αG₂ d).naturality (αF₁.app X)
  simp only [Functor.comp_map, Functor.comp_obj] at hn hd
  have hp : b.inv.app X ≫ H₁.map (a.inv.app X) = c.inv.app X ≫ d.inv.app (F₁.obj X) := by
    rw [← cancel_epi (c.hom.app X), ← cancel_epi (d.hom.app (F₁.obj X)), ← reassoc_of% (h X)]
    simp [← Functor.map_comp]
  rw [compComparison_fac_app_assoc, ← RH₁.map_comp, compComparison_fac_app, RH₁.map_comp,
    RH₁.map_comp, ← reassoc_of% hn, ← Q₄.map_comp_assoc, hp, compComparison_fac_app_assoc,
    hd, compComparison_fac_app_assoc]
  simp

end Stacks.DerivedBaseChange
