module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import StacksCore.Tactic.StacksAttribute

/-!
# Left and right fractions give the same localization (Stacks 04VL)

Let `W` be a multiplicative system on `C`, i.e. one admitting both a left and a right
calculus of fractions. Stacks 04VL asserts that the *category of left fractions* and the
*category of right fractions* of `C` at `W` are canonically isomorphic: the two
constructions of `W⁻¹C` agree.

In Mathlib the category of left fractions is `LeftFraction.Localization W`, and it comes
with its localization functor `LeftFraction.Localization.Q W`. The **category of right
fractions** is modelled here by op-duality, as
`(LeftFraction.Localization W.op)ᵒᵖ` — recall that `W.op` has a left calculus of
fractions exactly because `W` has a right one, so that opposite category is the
category whose morphisms `X ⟶ Y` are classes of right fractions `X ⟵ X' ⟶ Y` of `W`.
This is the model of the right-fraction localization that Section 4.27 standardises on
for localization-theoretic statements, because it is the only one carrying a
localization functor and the universal property; the explicit quotient presentation
required by Stacks 04VH itself is
`CategoryTheory.MorphismProperty.RightLocalization` in
`StacksFrontier.CategoryTheory.Localization.RightFraction.Defs`.

Both categories carry a localization functor out of `C` inverting exactly `W`, so the
universal property (`Localization.uniq`) produces a comparison equivalence, and
`Localization.compUniqFunctor` says it is compatible with those two functors, i.e. it
sends a morphism written as a left fraction to the same morphism written as a right
fraction. The pair (equivalence, compatibility isomorphism) is what "canonically
isomorphic" amounts to here; Mathlib's universal property yields an equivalence rather
than a strict isomorphism of categories, which is the standard reading.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty

universe v u

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]

/-- The localisation functor of `C` at `W` through **right** fractions, realised via
op-duality as the opposite of the left-fraction localisation of `(Cᵒᵖ, W.op)`. -/
noncomputable def rightFractionQ : C ⥤ (LeftFraction.Localization W.op)ᵒᵖ :=
  (LeftFraction.Localization.Q W.op).rightOp

/-- The right-fraction construction really is a localisation of `C` at `W`. -/
@[sga "5 V 2.3.3"]
instance rightFractionQ_isLocalization : (rightFractionQ W).IsLocalization W := by
  rw [← Functor.IsLocalization.op_iff]
  exact Functor.IsLocalization.of_equivalence_target
    (LeftFraction.Localization.Q W.op) W.op _
    (opOpEquivalence (LeftFraction.Localization W.op)).symm (Iso.refl _)

/-- **Stacks 04VL.**
The category of left fractions `LeftFraction.Localization W` and the category of right
fractions `(LeftFraction.Localization W.op)ᵒᵖ` of `C` at the multiplicative system `W` are
canonically equivalent. The equivalence is the one induced by the universal property of the
localisation: both `LeftFraction.Localization.Q W` and `rightFractionQ W` invert exactly `W`,
so `Localization.uniq` produces the canonical comparison, compatible with the two
localisation functors (see `compLeftFractionEquivRightFractionFunctor`). -/
@[stacks 04VL, sga "4½ Etat_0 2.3.1" "partial"]
noncomputable def leftFractionEquivRightFraction :
    LeftFraction.Localization W ≌ (LeftFraction.Localization W.op)ᵒᵖ :=
  Localization.uniq (LeftFraction.Localization.Q W) (rightFractionQ W) W

/-- **Stacks 04VL.** The canonical equivalence of 04VL is *canonical*: it is compatible
with the two localisation functors out of `C`, i.e. it identifies a morphism written as a
left fraction with the same morphism written as a right fraction. -/
@[stacks 04VL]
noncomputable def compLeftFractionEquivRightFractionFunctor :
    LeftFraction.Localization.Q W ⋙ (leftFractionEquivRightFraction W).functor ≅
      rightFractionQ W :=
  Localization.compUniqFunctor _ _ _

end CategoryTheory.MorphismProperty
