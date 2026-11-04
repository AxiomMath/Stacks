module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmallTargetUnitIso

/-!
# `f_{cris, *}` is functorial in the morphism of situations

For a composable pair `f = f₁ ≫ f₂` of morphisms of the global crystalline situations of
[Stacks, Tag 07I5], the canonical comparison

`crisDirectImageCompCell : f_{cris, *} ⟶ f₁_{cris, *} ∘ f₂_{cris, *}`

of `SmallSite/CrisDirectImageComposition.lean` is an isomorphism, and so is the derived
comparison `Rf_{cris, *} ≅ Rf₁_{cris, *} ∘ Rf₂_{cris, *}`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.hasCrisDirectImageComp` — **the comparison is
  an isomorphism.**
* `Crystalline.GlobalCrystallineSituation.SmallSite.crisDirectImageComp` — the resulting
  isomorphism `f_{cris, *} ≅ f₁_{cris, *} ∘ f₂_{cris, *}`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.derivedCrisDirectImageCompIso` —
  `Rf_{cris, *} ≅ Rf₁_{cris, *} ∘ Rf₂_{cris, *}`, with no hypotheses.

## References

* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

namespace SmallSite

variable {S₂ S₁ S₀ : GlobalCrystallineSituation.{u}}
  {f₁S : S₂.S ⟶ S₁.S} {f₁X : S₂.X ⟶ S₁.X}
  {f₂S : S₁.S ⟶ S₀.S} {f₂X : S₁.X ⟶ S₀.X}
  (h₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁S = f₁X ≫ S₁.toClosedFiber)
  (h₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂S = f₂X ≫ S₀.toClosedFiber)

/-- **The comparison `f_{cris, *} ⟶ f₁_{cris, *} ∘ f₂_{cris, *}` is invertible at every sheaf.** -/
instance isIso_crisDirectImageCompCell_app
    (F : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) :
    IsIso ((crisDirectImageCompCell h₁ h₂).app F) := by
  have hcell : IsIso ((changeBaseDirectImageComp h₁ h₂).inv.app ((bigDirectImage S₂).obj F)) :=
    NatIso.isIso_app_of_isIso _ _
  have hfst : IsIso ((smallRestriction S₀).map
      ((changeBaseDirectImageComp h₁ h₂).inv.app ((bigDirectImage S₂).obj F))) :=
    Functor.map_isIso _ _
  have hsnd := isIso_smallRestriction_changeBase_unit S₁ S₀ f₂S f₂X h₂
    ((changeBaseDirectImage S₂ S₁ f₁S f₁X h₁).obj ((bigDirectImage S₂).obj F))
  rw [crisDirectImageCompCell_app, Functor.map_comp]
  exact IsIso.comp_isIso' hfst hsnd

/-- **`f_{cris, *}` is functorial in the morphism of situations**: the canonical comparison
`crisDirectImageCompCell` is an isomorphism. -/
theorem hasCrisDirectImageComp : HasCrisDirectImageComp h₁ h₂ :=
  NatIso.isIso_of_isIso_app _

/-- **`f_{cris, *}` is functorial in the morphism of situations**, as an isomorphism of functors:
`(f₁ ≫ f₂)_{cris, *} ≅ f₁_{cris, *} ∘ f₂_{cris, *}`. -/
def crisDirectImageComp :
    crisDirectImage S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) ≅
      crisDirectImage S₂ S₁ f₁S f₁X h₁ ⋙ crisDirectImage S₁ S₀ f₂S f₂X h₂ :=
  haveI : IsIso (crisDirectImageCompCell h₁ h₂) := hasCrisDirectImageComp h₁ h₂
  asIso (crisDirectImageCompCell h₁ h₂)

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S₁) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1})]

/-- **`Rf_{cris, *}` is functorial in the morphism of situations**, with no hypotheses:
`R(f₁ ≫ f₂)_{cris, *} ≅ Rf₁_{cris, *} ∘ Rf₂_{cris, *}`. -/
def derivedCrisDirectImageCompIso :
    derivedCrisDirectImageFunctor S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
        (comp_closedFiber_compat h₁ h₂) ≅
      derivedCrisDirectImageFunctor S₂ S₁ f₁S f₁X h₁ ⋙
        derivedCrisDirectImageFunctor S₁ S₀ f₂S f₂X h₂ :=
  derivedCrisDirectImageComp h₁ h₂ (hasCrisDirectImageComp h₁ h₂)

end Derived

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end
