module

public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom

/-!
# The relative descent situation over an affine open of the fixed stage

In the relative descent situation of Stacks 0DI6 the transition morphisms of the inverse system
`S = lim Sᵢ` are affine, hence so are the projections `S ⟶ Sᵢ` from the limit (Stacks 01YX). The
stages `Xᵢ = Sᵢ ×_{S₀} X₀` and the limit `X = S ×_{S₀} X₀` are base changes of these, so they lie
over `X₀` by an affine morphism. Consequently the part of the situation sitting over an affine
open `V₀ ⊆ X₀` consists of affine schemes: `Vᵢ = f_{i0}^{-1}(V₀)` and `V = f_0^{-1}(V₀)` are
affine opens of `Xᵢ` and of `X`, even though neither `Sᵢ` nor `S₀` is assumed affine.

This is the geometric input of the affine case of Stacks 0DI7, the hypothesis `haffine` of
`AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_of_isAffineOpen_of_sup`: the
situation restricted to an affine open of `X₀` has affine fixed stage, affine stages and affine
limit, which is what makes the derived morphism sets there computable by the affine derived
equivalence of Stacks 06Z0.

## Main results

* `AlgebraicGeometry.RelativeDescentSituation.isAffineHom_baseMap` and
  `isAffineHom_baseProjection`: the transition morphisms `Sᵢ ⟶ S₀` of the inverse system and the
  projections `S ⟶ Sᵢ` from its limit are affine. The second is Stacks 01YX.
* `AlgebraicGeometry.RelativeDescentSituation.isAffineHom_toFixedStage` and
  `isAffineHom_limitToFixedStage`: the morphisms `f_{i0} : Xᵢ ⟶ X₀` and `f₀ : X ⟶ X₀` are affine.
* `AlgebraicGeometry.RelativeDescentSituation.isAffineOpen_preimage_toFixedStage` and
  `isAffineOpen_preimage_limitToFixedStage`: the preimage in `Xᵢ` and in `X` of an affine open of
  `X₀` is an affine open.
* `AlgebraicGeometry.RelativeDescentSituation.isAffine_schemeAt_of_isAffine` and
  `isAffine_limitScheme_of_isAffine`: if `X₀` is affine then so is every stage `Xᵢ` and the limit
  `X`.
* `AlgebraicGeometry.RelativeDescentSituation.isAffine_restrict_X₀`,
  `isAffine_restrict_schemeAt` and `isAffine_restrict_limitScheme`: the fixed stage, the stages
  and the limit of the situation restricted to an affine open of `X₀` are all affine.
* `AlgebraicGeometry.RelativeDescentSituation.isAffineHom_restrict_transition` and
  `isAffineHom_restrict_projection`: the transition morphisms and the projections from the limit
  of the situation restricted to an affine open of `X₀` are affine.

## Implementation notes

Affineness of the limit projections is `AlgebraicGeometry.EventualLimit.isAffineHom_π_app`, the
index-universe polymorphic form of Mathlib's `AlgebraicGeometry.isAffineHom_π_app`; the index
category of a relative descent situation is `Iᵒᵖ` for a directed preorder `I` in an arbitrary
universe, so Mathlib's own form, which pins the index universe to that of the schemes, does not
apply. Its hypothesis `IsCofiltered Iᵒᵖ` is produced from `Nonempty I`, witnessed by the fixed
stage of the situation, together with the directedness carried by the situation.

The affineness statements for the restricted situation are read off from the statements for a
general situation applied to `AlgebraicGeometry.RelativeDescentSituation.restrict`, whose fixed
stage is `V₀` itself; no transport occurs. `restrict` is made `implicit_reducible` locally so
that unification sees that the restricted situation has the same inverse system.

## References

* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v u

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{v, u} I)

attribute [local implicit_reducible] restrict

/-! ### Affineness over the fixed stage -/

/-- The transition morphism `Sᵢ ⟶ S₀` of the inverse system is affine. -/
theorem isAffineHom_baseMap (i : D.LaterIndex) : IsAffineHom (D.baseMap i) :=
  D.descent.transition_affine _

/-- **Stacks 01YX.** The projection `S ⟶ Sᵢ` from the limit of the inverse system is affine. -/
theorem isAffineHom_baseProjection (i : D.LaterIndex) :
    IsAffineHom (D.descent.limitCone.π.app (op i.1)) := by
  have : Nonempty I := ⟨D.descent.base⟩
  have : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.descent.system.map g) :=
    fun g => D.descent.transition_affine g
  exact EventualLimit.isAffineHom_π_app D.descent.system D.descent.limitCone D.descent.isLimit _

/-- The first projection of a pullback along an affine morphism is affine. -/
private theorem isAffineHom_pullback_fst {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    (hg : IsAffineHom g) : IsAffineHom (pullback.fst f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback f g).flip hg

/-- The morphism `f_{i0} : Xᵢ ⟶ X₀` is affine, being a base change of `Sᵢ ⟶ S₀`. -/
theorem isAffineHom_toFixedStage (i : D.LaterIndex) : IsAffineHom (D.toFixedStage i) :=
  isAffineHom_pullback_fst _ _ (D.isAffineHom_baseMap i)

/-- The morphism `f₀ : X ⟶ X₀` is affine, being a base change of `S ⟶ S₀`. -/
theorem isAffineHom_limitToFixedStage : IsAffineHom D.limitToFixedStage :=
  isAffineHom_pullback_fst _ _ (D.isAffineHom_baseProjection ⟨D.descent.base, le_refl _⟩)

/-- **The preimage `Vᵢ = f_{i0}^{-1}(V₀)` of an affine open of `X₀` is an affine open of `Xᵢ`.** -/
theorem isAffineOpen_preimage_toFixedStage {V₀ : D.X₀.left.Opens} (hV₀ : IsAffineOpen V₀)
    (i : D.LaterIndex) : IsAffineOpen (D.toFixedStage i ⁻¹ᵁ V₀) :=
  have := D.isAffineHom_toFixedStage i
  hV₀.preimage (D.toFixedStage i)

/-- **The preimage `V = f_0^{-1}(V₀)` of an affine open of `X₀` is an affine open of `X`.** -/
theorem isAffineOpen_preimage_limitToFixedStage {V₀ : D.X₀.left.Opens}
    (hV₀ : IsAffineOpen V₀) : IsAffineOpen (D.limitToFixedStage ⁻¹ᵁ V₀) :=
  have := D.isAffineHom_limitToFixedStage
  hV₀.preimage D.limitToFixedStage

/-- If the fixed stage `X₀` is affine then so is every stage `Xᵢ`. -/
theorem isAffine_schemeAt_of_isAffine (h : IsAffine D.X₀.left) (i : D.LaterIndex) :
    IsAffine (D.schemeAt i) :=
  have := h
  have := D.isAffineHom_toFixedStage i
  isAffine_of_isAffineHom (D.toFixedStage i)

/-- If the fixed stage `X₀` is affine then so is the limit `X`. -/
theorem isAffine_limitScheme_of_isAffine (h : IsAffine D.X₀.left) : IsAffine D.limitScheme :=
  have := h
  have := D.isAffineHom_limitToFixedStage
  isAffine_of_isAffineHom D.limitToFixedStage

/-! ### The situation restricted to an affine open of the fixed stage -/

variable (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀)

/-- The fixed stage of the situation restricted to an affine open `V₀ ⊆ X₀` is `V₀`, hence
affine. -/
theorem isAffine_restrict_X₀ : IsAffine (D.restrict V₀ hV₀.isCompact).X₀.left :=
  hV₀

/-- **The stages `Vᵢ = Sᵢ ×_{S₀} V₀` of the situation restricted to an affine open `V₀ ⊆ X₀` are
affine**, although neither `Sᵢ` nor `S₀` need be. -/
theorem isAffine_restrict_schemeAt (i : D.LaterIndex) :
    IsAffine ((D.restrict V₀ hV₀.isCompact).schemeAt i) :=
  (D.restrict V₀ hV₀.isCompact).isAffine_schemeAt_of_isAffine (D.isAffine_restrict_X₀ V₀ hV₀) i

/-- **The limit `V = S ×_{S₀} V₀` of the situation restricted to an affine open `V₀ ⊆ X₀` is
affine**, although neither `S` nor `S₀` need be. -/
theorem isAffine_restrict_limitScheme :
    IsAffine (D.restrict V₀ hV₀.isCompact).limitScheme :=
  (D.restrict V₀ hV₀.isCompact).isAffine_limitScheme_of_isAffine
    (D.isAffine_restrict_X₀ V₀ hV₀)

/-- The transition morphisms `Vⱼ ⟶ Vᵢ` of the situation restricted to an affine open of `X₀` are
affine, both of their ends being affine schemes. -/
theorem isAffineHom_restrict_transition {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    IsAffineHom ((D.restrict V₀ hV₀.isCompact).transition h) :=
  have := D.isAffine_restrict_schemeAt V₀ hV₀ i
  have := D.isAffine_restrict_schemeAt V₀ hV₀ j
  inferInstance

/-- The projections `V ⟶ Vᵢ` of the situation restricted to an affine open of `X₀` are affine,
both of their ends being affine schemes. -/
theorem isAffineHom_restrict_projection (i : D.LaterIndex) :
    IsAffineHom ((D.restrict V₀ hV₀.isCompact).projection i) :=
  have := D.isAffine_restrict_schemeAt V₀ hV₀ i
  have := D.isAffine_restrict_limitScheme V₀ hV₀
  inferInstance

end AlgebraicGeometry.RelativeDescentSituation

end
