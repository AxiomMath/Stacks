module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisInverseImageComposition
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareIso

/-!
# The square of topoi of [Stacks, Tag 07Q9] under composition

For a composable pair `S₂ ⟶ S₁ ⟶ S₀` of morphisms of the global crystalline situations of
[Stacks, Tag 07I5], the `2`-cell

`crisZariskiCell : f_{Zar, *}u_{X₂/S₂, *} ⟶ u_{X₀/S₀, *}f_{cris, *}`

of `SmallSite/CrisZariskiSquareIso.lean` is available for `f₁`, for `f₂` and for `f₁ ≫ f₂`, and
the two cells for the stages paste into one for the composite across the composition isomorphisms
`zariskiPushforwardComp` on the Zariski side and `crisDirectImageCompCell` on the crystalline
side.  This module states that the pasting is the cell of the composite,
`...SmallSite.CrisZariskiCellComp`, and proves from it `...SmallSite.zariskiComparison_comp`: the
comparison map of a composite cover is the comparison map of `f₂` followed by `f₂_{Zar, *}` of the
comparison map of `f₁`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crisZariskiSquarePastingApp` — the pasting of the commutation data of `f₁` and of `f₂` across
  `zariskiPushforwardComp`, read at a sheaf on `Cris(X₂/S₂)`, as an isomorphism.
* `crisZariskiCellPastingApp` — the pasting of the cells of `f₁` and of `f₂` across
  `zariskiPushforwardComp`, read at a sheaf on `Cris(X₂/S₂)`.
* `CrisZariskiCellComp` — **the coherence**: the cell of `f₁ ≫ f₂`, followed by `u_{X₀/S₀, *}` of
  the composition comparison of the direct images, is that pasting.

## Main results

* `crisZariskiSquare_inv` — the inverse of the commutation datum is the `2`-cell.
* `isIso_crisZariskiCellPastingApp` — the pasting of the cells is invertible.
* `zariskiComparison_comp` — **the composition functoriality of the comparison map of
  [Stacks, Tag 07Q9]**, under the coherence.

## References

* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

namespace SmallSite

variable {S₂ S₁ S₀ : GlobalCrystallineSituation.{u}}
  {f₁S : S₂.S ⟶ S₁.S} {f₁X : S₂.X ⟶ S₁.X}
  {f₂S : S₁.S ⟶ S₀.S} {f₂X : S₁.X ⟶ S₀.X}
  (h₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁S = f₁X ≫ S₁.toClosedFiber)
  (h₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂S = f₂X ≫ S₀.toClosedFiber)

/-- **The inverse of the commutation datum of the square of topoi is the canonical `2`-cell.** -/
theorem crisZariskiSquare_inv (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S)
    (fX : S.X ⟶ S'.X)
    (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber) :
    (crisZariskiSquare S S' fS fX hf).inv = crisZariskiCell S S' fS fX hf :=
  rfl

/-- **The pasting of the two squares of topoi, read at a sheaf on `Cris(X₂/S₂)`**, as an
isomorphism: the commutation datum of `f₂`, then `f₂_{Zar, *}` of the commutation datum of `f₁`,
then the composition isomorphism of the Zariski direct images.

Its inverse is `crisZariskiCellPastingApp`, the pasting of the two `2`-cells. -/
def crisZariskiSquarePastingApp (G : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) :
    (zariskiDirectImage S₀).obj
        ((crisDirectImage S₁ S₀ f₂S f₂X h₂).obj
          ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj G)) ≅
      (zariskiPushforward S₂ S₀ (f₁X ≫ f₂X)).obj ((zariskiDirectImage S₂).obj G) :=
  ((crisZariskiSquare S₁ S₀ f₂S f₂X h₂).app ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj G) ≪≫
      (zariskiPushforward S₁ S₀ f₂X).mapIso
        ((crisZariskiSquare S₂ S₁ f₁S f₁X h₁).app G)) ≪≫
    (zariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X)).app ((zariskiDirectImage S₂).obj G)

/-- **The pasting of the two `2`-cells of the squares of topoi, read at a sheaf on
`Cris(X₂/S₂)`.**

From `f_{Zar, *}u_{X₂/S₂, *}` it goes to `f₂_{Zar, *}f₁_{Zar, *}u_{X₂/S₂, *}` by
`zariskiPushforwardComp`, then to `f₂_{Zar, *}u_{X₁/S₁, *}f₁_{cris, *}` by `f₂_{Zar, *}` of the
cell of `f₁`, then to `u_{X₀/S₀, *}f₂_{cris, *}f₁_{cris, *}` by the cell of `f₂`. -/
def crisZariskiCellPastingApp (G : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) :
    (zariskiPushforward S₂ S₀ (f₁X ≫ f₂X)).obj ((zariskiDirectImage S₂).obj G) ⟶
      (zariskiDirectImage S₀).obj
        ((crisDirectImage S₁ S₀ f₂S f₂X h₂).obj
          ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj G)) :=
  (zariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X)).inv.app
      ((zariskiDirectImage S₂).obj G) ≫
    (zariskiPushforward S₁ S₀ f₂X).map ((crisZariskiCell S₂ S₁ f₁S f₁X h₁).app G) ≫
      (crisZariskiCell S₁ S₀ f₂S f₂X h₂).app ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj G)

/-- The pasting of the `2`-cells is the inverse of the pasting of the commutation data. -/
theorem crisZariskiSquarePastingApp_inv
    (G : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) :
    (crisZariskiSquarePastingApp h₁ h₂ G).inv = crisZariskiCellPastingApp h₁ h₂ G :=
  rfl

/-- **The pasting of the two squares of topoi is invertible.** -/
instance isIso_crisZariskiCellPastingApp
    (G : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) :
    IsIso (crisZariskiCellPastingApp h₁ h₂ G) :=
  inferInstanceAs (IsIso (crisZariskiSquarePastingApp h₁ h₂ G).inv)

/-- **The coherence of the three squares of topoi of [Stacks, Tag 07Q9] under composition.**

The `2`-cell of `f₁ ≫ f₂`, followed by `u_{X₀/S₀, *}` of the comparison
`crisDirectImageCompCell : (f₁ ≫ f₂)_{cris, *} ⟶ f₁_{cris, *} ∘ f₂_{cris, *}`, is the pasting
`crisZariskiCellPastingApp` of the cells of `f₁` and `f₂`. -/
def CrisZariskiCellComp : Prop :=
  ∀ G : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1},
    (crisZariskiCell S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
          (comp_closedFiber_compat h₁ h₂)).app G ≫
        (zariskiDirectImage S₀).map ((crisDirectImageCompCell h₁ h₂).app G) =
      crisZariskiCellPastingApp h₁ h₂ G

/-- Under the coherence `CrisZariskiCellComp`, the commutation datum of `f₂`, followed by
`f₂_{Zar, *}` of that of `f₁` and by the composition isomorphism of the Zariski direct images, is
`u_{X₀/S₀, *}` of the inverse of the composition comparison of the crystalline direct images
followed by the commutation datum of `f₁ ≫ f₂`. -/
theorem crisZariskiSquare_hom_app_comp_of_cellComp (hcoh : CrisZariskiCellComp h₁ h₂)
    (G : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) :
    (crisZariskiSquare S₁ S₀ f₂S f₂X h₂).hom.app
          ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj G) ≫
        (zariskiPushforward S₁ S₀ f₂X).map
          ((crisZariskiSquare S₂ S₁ f₁S f₁X h₁).hom.app G) ≫
        (zariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X)).hom.app
          ((zariskiDirectImage S₂).obj G) =
      (zariskiDirectImage S₀).map ((crisDirectImageComp h₁ h₂).inv.app G) ≫
        (crisZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
          (comp_closedFiber_compat h₁ h₂)).hom.app G := by
  have hc : (crisDirectImageCompCell h₁ h₂).app G ≫
      (crisDirectImageComp h₁ h₂).inv.app G =
      𝟙 ((crisDirectImage S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
        (comp_closedFiber_compat h₁ h₂)).obj G) :=
    NatTrans.congr_app (crisDirectImageComp h₁ h₂).hom_inv_id G
  have hcU : (zariskiDirectImage S₀).map ((crisDirectImageCompCell h₁ h₂).app G) ≫
      (zariskiDirectImage S₀).map ((crisDirectImageComp h₁ h₂).inv.app G) =
      𝟙 ((zariskiDirectImage S₀).obj
        ((crisDirectImage S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
          (comp_closedFiber_compat h₁ h₂)).obj G)) := by
    rw [← Functor.map_comp, hc, CategoryTheory.Functor.map_id]
  have ef : (crisZariskiCell S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
        (comp_closedFiber_compat h₁ h₂)).app G ≫
      (crisZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
        (comp_closedFiber_compat h₁ h₂)).hom.app G =
      𝟙 ((zariskiPushforward S₂ S₀ (f₁X ≫ f₂X)).obj ((zariskiDirectImage S₂).obj G)) :=
    (crisZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
      (comp_closedFiber_compat h₁ h₂)).inv_hom_id_app _
  have hleft : crisZariskiCellPastingApp h₁ h₂ G ≫
      (((crisZariskiSquare S₁ S₀ f₂S f₂X h₂).hom.app
            ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj G) ≫
          (zariskiPushforward S₁ S₀ f₂X).map
            ((crisZariskiSquare S₂ S₁ f₁S f₁X h₁).hom.app G)) ≫
        (zariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X)).hom.app
          ((zariskiDirectImage S₂).obj G)) =
      𝟙 ((zariskiPushforward S₂ S₀ (f₁X ≫ f₂X)).obj ((zariskiDirectImage S₂).obj G)) :=
    (crisZariskiSquarePastingApp h₁ h₂ G).inv_hom_id
  rw [Category.assoc] at hleft
  have hright : crisZariskiCellPastingApp h₁ h₂ G ≫
      ((zariskiDirectImage S₀).map ((crisDirectImageComp h₁ h₂).inv.app G) ≫
        (crisZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
          (comp_closedFiber_compat h₁ h₂)).hom.app G) =
      𝟙 ((zariskiPushforward S₂ S₀ (f₁X ≫ f₂X)).obj ((zariskiDirectImage S₂).obj G)) := by
    rw [← hcoh G, Category.assoc,
      ← Category.assoc ((zariskiDirectImage S₀).map ((crisDirectImageCompCell h₁ h₂).app G)),
      hcU, Category.id_comp]
    exact ef
  rw [← cancel_epi (crisZariskiCellPastingApp h₁ h₂ G), hleft, hright]

/-- **The composition functoriality of the comparison map of [Stacks, Tag 07Q9]**, from the
coherence of the three squares of topoi.

The comparison map of the composite cover `f₁ ≫ f₂` is the comparison map of `f₂`, followed by
`f₂_{Zar, *}` of the comparison map of `f₁`, read through the composition isomorphism
`zariskiPushforwardComp` of the Zariski direct images and the composition comparison
`crisInverseImageCompCell` of the crystalline inverse images. -/
theorem zariskiComparison_comp (hcoh : CrisZariskiCellComp h₁ h₂)
    (F : Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1}) :
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
            ((zariskiDirectImage S₂).map ((crisInverseImageCompCell h₁ h₂).app F)) := by
  rw [zariskiComparison, zariskiComparison, zariskiComparison, crisUnit_comp_eq h₁ h₂ F]
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
  slice_rhs 2 3 => erw [← (crisZariskiSquare S₁ S₀ f₂S f₂X h₂).hom.naturality]
  slice_rhs 3 5 => rw [crisZariskiSquare_hom_app_comp_of_cellComp h₁ h₂ hcoh]
  slice_rhs 4 5 => erw [← (crisZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
    (comp_closedFiber_compat h₁ h₂)).hom.naturality]
  slice_lhs 3 4 => erw [← Functor.map_comp,
    (crisDirectImageComp h₁ h₂).inv.naturality, Functor.map_comp]
  simp only [Functor.comp_map, Category.assoc]

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
