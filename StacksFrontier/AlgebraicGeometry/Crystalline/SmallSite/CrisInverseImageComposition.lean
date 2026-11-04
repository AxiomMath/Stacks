module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImageCompositionIso

/-!
# `f_cris^{-1}` is functorial in the morphism of situations

`SmallSite/CrisDirectImageCompositionIso.lean` proves that the canonical comparison

`crisDirectImageCompCell : f_{cris, *} ⟶ f₁_{cris, *} ∘ f₂_{cris, *}`,  `f = f₁ ≫ f₂`,

is invertible.  **This module proves the mirror statement for the crystalline inverse image**,

`f₂_cris^{-1}` followed by `f₁_cris^{-1}` is `f_cris^{-1}`,

as `...SmallSite.crisInverseImageComp`, and reads it on a sheaf as
`...SmallSite.crisPullbackComp`, the composition isomorphism for the `ℱ' = f_cris^*ℱ` of
[Stacks, Tag 07Q9].  It also proves the compatibility of the units the comparison map of
[Stacks, Tag 07Q9] is built from, `...SmallSite.crisUnit_comp`.

## The obstruction, and why it is not met head on

`f_cris^{-1}` is the composite `i_{X, !} ∘ f_CRIS^{-1} ∘ π_{X', *}` of the inverse images of the
three factors of `f_cris` ([Stacks, Tag 07IK]), in the order opposite to the one in which
`f_{cris, *}` composes them.  Composing two of them therefore leaves one occurrence of
`i_{X₁, !} ∘ π_{X₁, *}` in the middle — the exact mirror of the `i_{X₁, *} ∘ π_{X₁, *}` that
composing two `f_{cris, *}` leaves — and the canonical comparison between the composite and
`f_cris^{-1}` is the **counit** `i_{X₁, !}π_{X₁, *}ℋ ⟶ ℋ` of `smallRestrictionAdjunction`,
whiskered into place.  Inverting that counit directly is not available, and the obvious approaches
are worse than unavailable: the module-level lower shriek is not even left exact
(`Stacks.SheafOfModules.lowerShriek_not_preservesFiniteLimits`), so no exactness argument of the
kind that settles `f_cris^{-1}` itself can be run on the middle factor.

The comparison is invertible all the same, and no limit or colimit is computed to see it.  Both
sides are **left adjoints**, of the two sides of the composition isomorphism for `f_{cris, *}`,
which `SmallSite/CrisDirectImageCompositionIso.lean` has already proved invertible; and the
passage from a natural transformation of right adjoints to one of their left adjoints —
`CategoryTheory.conjugateEquiv`, the mate construction with identity verticals — is a bijection
which carries isomorphisms to isomorphisms, `CategoryTheory.conjugateEquiv_symm_iso`.  So the
mirror comparison is the conjugate of `crisDirectImageCompCell`, and its invertibility is that of
`crisDirectImageCompCell`.

This is not a different morphism from the counit-whiskered one: being the conjugate of a 2-cell
assembled from the unit of `π_{X₁, *} ⊣ i_{X₁, *}` and the composition isomorphism of the big
direct images, it is by `CategoryTheory.conjugateEquiv_counit_symm` characterised by the same
triangle identity against the counits that the counit-whiskered cell satisfies.  What the
conjugation buys is that the characterisation is *proved* rather than assumed: the counit of
`i_{X₁, !} ⊣ π_{X₁, *}` is never inverted at any object.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crisInverseImageCompCell` — the canonical comparison
  `f₂_cris^{-1} ∘ f₁_cris^{-1}-wise composite ⟶ f_cris^{-1}`, the conjugate of
  `crisDirectImageCompCell`.
* `crisInverseImageComp` — **the composition isomorphism of `f_cris^{-1}`**, as an isomorphism of
  functors.
* `crisPullbackComp` — the same read on a sheaf: `ℱ'' ≅ (f₁ ≫ f₂)_cris^*ℱ` for
  `ℱ'' = f₁_cris^*(f₂_cris^*ℱ)`.

## Main results

* `isIso_crisInverseImageCompCell` — the comparison is invertible.
* `crisUnit_comp` — **the unit of [Stacks, Tag 07Q9] for a composite is the composite of the
  units**, read through the two composition comparisons.  This is the crystalline half of the
  composition functoriality of the comparison map of [Stacks, Tag 07Q9].
* `crisUnit_comp_eq` — the same identity solved for the unit of the composite.

## What is and is not proved

Everything here is unconditional, for every composable pair of morphisms of global crystalline
situations.

**No tag attribute is placed.**  Nothing here states a clause of [Stacks, Tag 07Q9]: this is the
second of the three inputs to the composition functoriality of the comparison map of
[Stacks, Tag 07Q9] listed in the module documentation of
`SmallSite/CrisDirectImageComposition.lean`.  The third — the coherence of the commutation data
of `SmallSite/CrisZariskiSquareIso.lean` under composition — is stated in
`SmallSite/CrisZariskiSquareComposition.lean`, and the *local* step of [Stacks, Tag 07Q9] is
untouched here.

## References

* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
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

/-- **The adjunction `f₂_cris^{-1} ∘ f₁_cris^{-1} ⊣ f₁_{cris, *} ∘ f₂_{cris, *}`** for a
composable pair, the composite of the two adjunctions `crisDirectImageAdjunction`.

Its right-hand side is the target of `crisDirectImageCompCell`, which is what lets that
comparison be conjugated. -/
def crisDirectImageAdjunctionComp :
    crisInverseImage S₁ S₀ f₂S f₂X h₂ ⋙ crisInverseImage S₂ S₁ f₁S f₁X h₁ ⊣
      crisDirectImage S₂ S₁ f₁S f₁X h₁ ⋙ crisDirectImage S₁ S₀ f₂S f₂X h₂ :=
  (crisDirectImageAdjunction S₁ S₀ f₂S f₂X h₂).comp
    (crisDirectImageAdjunction S₂ S₁ f₁S f₁X h₁)

/-- The unit of `crisDirectImageAdjunctionComp` is the unit of `f₂_cris` followed by
`f₂_{cris, *}` of the unit of `f₁_cris`, which is the composite of the two units of
[Stacks, Tag 07Q9]. -/
theorem crisDirectImageAdjunctionComp_unit_app
    (F : Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1}) :
    (crisDirectImageAdjunctionComp h₁ h₂).unit.app F =
      crisUnit S₁ S₀ f₂S f₂X h₂ F ≫
        (crisDirectImage S₁ S₀ f₂S f₂X h₂).map
          (crisUnit S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F)) :=
  Adjunction.comp_unit_app _ _ F

/-- **The canonical comparison `f₂_cris^{-1}` then `f₁_cris^{-1}` `⟶` `(f₁ ≫ f₂)_cris^{-1}`.**

It is the conjugate of `crisDirectImageCompCell` under `CategoryTheory.conjugateEquiv`: both
sides are left adjoints, of the two sides of that comparison, and a natural transformation of
right adjoints determines one of their left adjoints running the other way.  Equivalently —
`CategoryTheory.conjugateEquiv_counit_symm` — it is the unique natural transformation whose
composite with the counit of `f_cris^{-1} ⊣ f_{cris, *}` is the counit of the composite adjunction
transported along `crisDirectImageCompCell`, which is what the counit of
`i_{X₁, !} ⊣ π_{X₁, *}` whiskered into the middle of the composite satisfies.

See the module documentation for why the counit in the middle is not inverted directly. -/
def crisInverseImageCompCell :
    crisInverseImage S₁ S₀ f₂S f₂X h₂ ⋙ crisInverseImage S₂ S₁ f₁S f₁X h₁ ⟶
      crisInverseImage S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) :=
  (conjugateEquiv
    (crisDirectImageAdjunction S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂))
    (crisDirectImageAdjunctionComp h₁ h₂)).symm (crisDirectImageCompCell h₁ h₂)

/-- **The comparison of `crisInverseImageCompCell` is invertible.**  `conjugateEquiv` carries
isomorphisms to isomorphisms in both directions, and `crisDirectImageCompCell` is an isomorphism
by `hasCrisDirectImageComp`. -/
instance isIso_crisInverseImageCompCell : IsIso (crisInverseImageCompCell h₁ h₂) :=
  haveI : IsIso (crisDirectImageCompCell h₁ h₂) := hasCrisDirectImageComp h₁ h₂
  inferInstanceAs (IsIso ((conjugateEquiv _ _).symm (crisDirectImageCompCell h₁ h₂)))

/-- **`f_cris^{-1}` is functorial in the morphism of situations**, as an isomorphism of functors:
`f₂_cris^{-1}` followed by `f₁_cris^{-1}` is `(f₁ ≫ f₂)_cris^{-1}`.

This is the second of the three inputs to the composition functoriality of the comparison map of
[Stacks, Tag 07Q9]; see the module documentation of
`SmallSite/CrisDirectImageComposition.lean`. -/
def crisInverseImageComp :
    crisInverseImage S₁ S₀ f₂S f₂X h₂ ⋙ crisInverseImage S₂ S₁ f₁S f₁X h₁ ≅
      crisInverseImage S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) :=
  asIso (crisInverseImageCompCell h₁ h₂)

/-- **The composition isomorphism for `ℱ' = f_cris^*ℱ` of [Stacks, Tag 07Q9]**:
`f₁_cris^*(f₂_cris^*ℱ) ≅ (f₁ ≫ f₂)_cris^*ℱ`.  This is the statement the composition
functoriality of the comparison map consumes, and it is `crisInverseImageComp` read at `ℱ`. -/
def crisPullbackComp (F : Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1}) :
    crisPullback S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F) ≅
      crisPullback S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) F :=
  (crisInverseImageComp h₁ h₂).app F

/-- **The unit of [Stacks, Tag 07Q9] for a composite is the composite of the units.**

The unit `ℱ ⟶ f_{cris, *}ℱ'` of `crisUnit` for `f = f₁ ≫ f₂`, followed by the comparison
`crisDirectImageCompCell`, is the unit for `f₂` followed by `f₂_{cris, *}` of the unit for `f₁`,
followed by `f₁_{cris, *}f₂_{cris, *}` of the comparison `crisInverseImageCompCell`.

This is the triangle identity relating the two conjugate comparisons,
`CategoryTheory.unit_conjugateEquiv_symm`, together with the formula for the unit of a composite
adjunction; it is the crystalline half of the composition functoriality of the comparison map of
[Stacks, Tag 07Q9]. -/
theorem crisUnit_comp (F : Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1}) :
    crisUnit S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) F ≫
        (crisDirectImageCompCell h₁ h₂).app
          (crisPullback S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) F) =
      (crisUnit S₁ S₀ f₂S f₂X h₂ F ≫
          (crisDirectImage S₁ S₀ f₂S f₂X h₂).map
            (crisUnit S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F))) ≫
        (crisDirectImage S₂ S₁ f₁S f₁X h₁ ⋙ crisDirectImage S₁ S₀ f₂S f₂X h₂).map
          ((crisInverseImageCompCell h₁ h₂).app F) := by
  rw [← crisDirectImageAdjunctionComp_unit_app h₁ h₂ F]
  exact unit_conjugateEquiv_symm
    (crisDirectImageAdjunction S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂))
    (crisDirectImageAdjunctionComp h₁ h₂) (crisDirectImageCompCell h₁ h₂) F

/-- **The unit of [Stacks, Tag 07Q9] for a composite, solved for.**  `crisUnit_comp` with the
invertible `crisDirectImageCompCell` moved to the right-hand side, so that the unit of the
composite is exhibited as the composite of the two units read through the two composition
isomorphisms. -/
theorem crisUnit_comp_eq (F : Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1}) :
    crisUnit S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) F =
      (crisUnit S₁ S₀ f₂S f₂X h₂ F ≫
          (crisDirectImage S₁ S₀ f₂S f₂X h₂).map
            (crisUnit S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F))) ≫
        (crisDirectImage S₂ S₁ f₁S f₁X h₁ ⋙ crisDirectImage S₁ S₀ f₂S f₂X h₂).map
          ((crisInverseImageCompCell h₁ h₂).app F) ≫
        (crisDirectImageComp h₁ h₂).inv.app
          (crisPullback S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) F) := by
  have h : (crisDirectImageCompCell h₁ h₂).app
        (crisPullback S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) F) ≫
      (crisDirectImageComp h₁ h₂).inv.app
        (crisPullback S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) F) = 𝟙 _ :=
    NatTrans.congr_app (crisDirectImageComp h₁ h₂).hom_inv_id _
  rw [← Category.assoc, ← crisUnit_comp h₁ h₂ F, Category.assoc, h, Category.comp_id]

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
