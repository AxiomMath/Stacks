module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImageComposition
public import StacksFrontier.CategoryTheory.Sites.CocontinuousPushforwardCompUnit

/-!
# The comparison `f_{cris, *} ⟶ f₁_{cris, *} ∘ f₂_{cris, *}` on sections

`SmallSite/CrisDirectImageComposition.lean` builds the canonical comparison
`...SmallSite.crisDirectImageCompCell` out of the composition isomorphism
`...SmallSite.changeBaseDirectImageComp` of the direct images on the big sites and the unit of
`...SmallSite.bigDirectImageAdjunction`.  Both factors are opaque: nothing yet says what the
comparison does to a section.

This file evaluates it.  The sections of `f₁_{cris, *}f₂_{cris, *}ℋ` over an object `A₀` of
`Cris(X₀/S₀)` are a limit indexed by the dominations of an object of `Cris(X₂/S₂)` that factor
through an object of `Cris(X₁/S₁)`, and the chain of counits reading off one such index is:
restrict along the domination `k₂` of `A₀` by `C`, take the counits of `f₂_{CRIS, *}` and of
`i_{X₁, *}`, restrict along the domination `k₁` of `C` by `D`, and take the counit of
`f₁_{CRIS, *}`.  The comparison followed by that chain is the chain of two counits for the
composite, read at the domination of `A₀` by `D` which the two dominations compose into.

Everything is carried out abstractly in
`StacksFrontier/CategoryTheory/Sites/CocontinuousPushforwardCompUnit.lean`: the two inputs are
`CategoryTheory.Functor`
`.rightAdjointUniq_sheafAdjunctionCocontinuous_inv_app_hom_app_comp_ranCounit` for the composition
isomorphism and
`CategoryTheory.Functor.sheafAdjunctionCocontinuous_unit_app_hom_app_comp_ranCounit` for the unit,
and `CategoryTheory.Functor.ran_comp_unit_ranCounit_chain` assembles them.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `compDomination` — the domination of an object of `Cris(X₀/S₀)` by an object of `Cris(X₂/S₂)`
  obtained from a factorization through an object of `Cris(X₁/S₁)`, read across the functoriality
  `...changeBaseComp` of change of divided power base.

## Main results

* `changeBaseComp_hom_app_comp_compDomination` — the factorization isomorphism cancels against
  `compDomination`, leaving the two dominations composed.
* `crisDirectImageCompCell_app_hom_app_comp_ranCounit` — **the comparison on sections.**

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
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

/-- **The domination obtained by composing two dominations across the functoriality of change of
divided power base.**  Given an object `D` of `Cris(X₂/S₂)` dominating an object `C` of
`Cris(X₁/S₁)` after rebasing along `f₁`, and `C` dominating an object `A₀` of `Cris(X₀/S₀)` after
rebasing along `f₂`, the object `D` dominates `A₀` after rebasing along `f₁ ≫ f₂`: rebase the first
domination along `f₂` and read the two rebasings of `D` through
`Crystalline.GlobalCrystallineSituation.changeBaseComp`. -/
def compDomination (A₀ : CrystallineThickening S₀) (C : CrystallineThickening S₁)
    (D : CrystallineThickening S₂)
    (k₂ : (changeBase S₁ S₀ f₂S f₂X h₂).obj ((CrystallineThickening.ι S₁).obj C) ⟶
      (CrystallineThickening.ι S₀).obj A₀)
    (k₁ : (changeBase S₂ S₁ f₁S f₁X h₁).obj ((CrystallineThickening.ι S₂).obj D) ⟶
      (CrystallineThickening.ι S₁).obj C) :
    (changeBase S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂)).obj
        ((CrystallineThickening.ι S₂).obj D) ⟶ (CrystallineThickening.ι S₀).obj A₀ :=
  (changeBaseComp h₁ h₂).inv.app ((CrystallineThickening.ι S₂).obj D) ≫
    (changeBase S₁ S₀ f₂S f₂X h₂).map k₁ ≫ k₂

/-- The functoriality isomorphism of change of divided power base cancels against
`compDomination`, which was built from its inverse, and what is left is the first domination
rebased along `f₂` followed by the second. -/
theorem changeBaseComp_hom_app_comp_compDomination (A₀ : CrystallineThickening S₀)
    (C : CrystallineThickening S₁) (D : CrystallineThickening S₂)
    (k₂ : (changeBase S₁ S₀ f₂S f₂X h₂).obj ((CrystallineThickening.ι S₁).obj C) ⟶
      (CrystallineThickening.ι S₀).obj A₀)
    (k₁ : (changeBase S₂ S₁ f₁S f₁X h₁).obj ((CrystallineThickening.ι S₂).obj D) ⟶
      (CrystallineThickening.ι S₁).obj C) :
    (changeBaseComp h₁ h₂).hom.app ((CrystallineThickening.ι S₂).obj D) ≫
        compDomination h₁ h₂ A₀ C D k₂ k₁ =
      (changeBase S₁ S₀ f₂S f₂X h₂).map k₁ ≫ k₂ := by
  rw [compDomination, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- **The comparison `f_{cris, *} ⟶ f₁_{cris, *} ∘ f₂_{cris, *}`, read on sections against the
counits.**

At an object `A₀` of `Cris(X₀/S₀)`, the comparison followed by the four-step chain of counits
attached to a domination `k₂` of `A₀` by an object `C` of `Cris(X₁/S₁)` and a domination `k₁` of
`C` by an object `D` of `Cris(X₂/S₂)` is the two-step chain of counits for the composite morphism,
read at the domination `compDomination` of `A₀` by `D`.

The comparison is the composition isomorphism of the direct images on the big sites followed by
`f₂_{CRIS, *}` of the unit of `π_{X₁, *} ⊣ i_{X₁, *}`; each factor is determined by what it does
to the counits, and `CategoryTheory.Functor.ran_comp_unit_ranCounit_chain` assembles the two
determinations, the triangle identity of the unit collapsing the middle of the chain. -/
theorem crisDirectImageCompCell_app_hom_app_comp_ranCounit
    (ℋ : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1})
    (A₀ : CrystallineThickening S₀) (C : CrystallineThickening S₁)
    (D : CrystallineThickening S₂)
    (k₂ : (changeBase S₁ S₀ f₂S f₂X h₂).obj ((CrystallineThickening.ι S₁).obj C) ⟶
      (CrystallineThickening.ι S₀).obj A₀)
    (k₁ : (changeBase S₂ S₁ f₁S f₁X h₁).obj ((CrystallineThickening.ι S₂).obj D) ⟶
      (CrystallineThickening.ι S₁).obj C) :
    ((crisDirectImageCompCell h₁ h₂).app ℋ).hom.app (op A₀) ≫
        ((changeBase S₁ S₀ f₂S f₂X h₂).op.ran.obj
            ((CrystallineThickening.ι S₁).op.ran.obj
              ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj ℋ).obj)).map k₂.op ≫
          ((changeBase S₁ S₀ f₂S f₂X h₂).op.ranCounit.app
              ((CrystallineThickening.ι S₁).op.ran.obj
                ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj ℋ).obj)).app
            ((CrystallineThickening.ι S₁).op.obj (op C)) ≫
            ((CrystallineThickening.ι S₁).op.ranCounit.app
                ((crisDirectImage S₂ S₁ f₁S f₁X h₁).obj ℋ).obj).app (op C) ≫
              ((changeBase S₂ S₁ f₁S f₁X h₁).op.ran.obj
                  ((CrystallineThickening.ι S₂).op.ran.obj ℋ.obj)).map k₁.op ≫
                ((changeBase S₂ S₁ f₁S f₁X h₁).op.ranCounit.app
                    ((CrystallineThickening.ι S₂).op.ran.obj ℋ.obj)).app
                  ((CrystallineThickening.ι S₂).op.obj (op D)) =
      ((changeBase S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂)).op.ran.obj
            ((CrystallineThickening.ι S₂).op.ran.obj ℋ.obj)).map
          (compDomination h₁ h₂ A₀ C D k₂ k₁).op ≫
        ((changeBase S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
              (comp_closedFiber_compat h₁ h₂)).op.ranCounit.app
            ((CrystallineThickening.ι S₂).op.ran.obj ℋ.obj)).app
          ((CrystallineThickening.ι S₂).op.obj (op D)) := by
  have hA := Functor.rightAdjointUniq_sheafAdjunctionCocontinuous_inv_app_hom_app_comp_ranCounit
    (A := AddCommGrpCat.{u + 1}) (changeBaseComp h₁ h₂) (topology S₂) (topology S₁) (topology S₀)
    ((bigDirectImage S₂).obj ℋ)
  have hB := Functor.sheafAdjunctionCocontinuous_unit_app_hom_app_comp_ranCounit
    (A := AddCommGrpCat.{u + 1}) (ι := CrystallineThickening.ι S₁) (J := smallTopology S₁)
    (K := topology S₁) ((changeBaseDirectImage S₂ S₁ f₁S f₁X h₁).obj ((bigDirectImage S₂).obj ℋ))
  have hgen := Functor.ran_comp_unit_ranCounit_chain
    (changeBase S₂ S₁ f₁S f₁X h₁).op (changeBase S₁ S₀ f₂S f₂X h₂).op
    (changeBase S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂)).op
    (NatIso.op (changeBaseComp h₁ h₂)).symm (CrystallineThickening.ι S₁).op
    ((bigDirectImage S₂).obj ℋ).obj hA hB
    ((CrystallineThickening.ι S₀).op.obj (op A₀)) (op C)
    ((CrystallineThickening.ι S₂).op.obj (op D)) k₂.op k₁.op
    (compDomination h₁ h₂ A₀ C D k₂ k₁).op
    (congrArg Quiver.Hom.op
      (changeBaseComp_hom_app_comp_compDomination h₁ h₂ A₀ C D k₂ k₁))
  refine Eq.trans ?_ hgen
  exact Category.assoc _ _ _

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
