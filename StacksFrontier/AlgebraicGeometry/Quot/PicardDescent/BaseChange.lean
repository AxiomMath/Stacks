module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom

/-!
# Base change of algebraic spaces preserves fibre products of test schemes

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site.  The
base change `T ↦ X_T = X ×_Y T` along the test schemes over `Y` carries a square of test schemes
whose underlying square of schemes of the site is cartesian to a cartesian square of algebraic
spaces: `X_{T₁ ×_T T₂} = X_{T₁} ×_{X_T} X_{T₂}`.  This is the identification of the overlaps of
a base-changed covering with the base changes of the overlaps.

## Main results

* `AlgebraicGeometry.Space.isPullback_schemeSpaceFunctor_map`: the algebraic spaces represented
  by a cartesian square of schemes of the site form a cartesian square.
* `AlgebraicGeometry.Space.isPullback_baseChangeMap_of_isPullback`: base change carries a
  square of test schemes over `Y` with cartesian underlying square to a cartesian square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The algebraic spaces represented by a cartesian square of schemes of the site form a
cartesian square.**  The Yoneda embedding preserves fibre products and the algebraic spaces are
a full subcategory of the presheaves. -/
theorem isPullback_schemeSpaceFunctor_map {P V W Z : BigFppfOver B S hS} {a : P ⟶ V}
    {b : P ⟶ W} {c : V ⟶ Z} {d : W ⟶ Z} (h : IsPullback a b c d) :
    IsPullback ((schemeSpaceFunctor B S hS).map a) ((schemeSpaceFunctor B S hS).map b)
      ((schemeSpaceFunctor B S hS).map c) ((schemeSpaceFunctor B S hS).map d) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) (h.map yoneda)

/-- **Base change preserves fibre products of test schemes.**  For a square of test schemes over
`Y` whose underlying square of schemes of the site is cartesian, the square of base changes
`X_P ⟶ X_{T₁}, X_P ⟶ X_{T₂}, X_{T₁} ⟶ X_T, X_{T₂} ⟶ X_T` is cartesian.

The base change `X_P ⟶ X_{T₁}` is the pullback of `P ⟶ T₁` along `X_{T₁} ⟶ T₁`, so the
rectangle `X_P ⟶ X_{T₁} ⟶ T₁ ⟶ T` over `P ⟶ T₂ ⟶ T` is cartesian; it is also the composite of
the square in question with the cartesian square of `T₂ ⟶ T`, and cancelling that square gives
the claim. -/
theorem isPullback_baseChangeMap_of_isPullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {P T₁ T₂ T : SchemesOver Y} {β₁ : P ⟶ T₁} {β₂ : P ⟶ T₂} {g₁ : T₁ ⟶ T} {g₂ : T₂ ⟶ T}
    (h : IsPullback β₁.left β₂.left g₁.left g₂.left) :
    IsPullback (baseChangeMap f β₁) (baseChangeMap f β₂) (baseChangeMap f g₁)
      (baseChangeMap f g₂) := by
  have hrect : IsPullback (baseChangeMap f β₁)
      (baseChangeInclusion f P ≫ (schemeSpaceFunctor B S hS).map β₂.left)
      (baseChangeInclusion f T₁ ≫ (schemeSpaceFunctor B S hS).map g₁.left)
      ((schemeSpaceFunctor B S hS).map g₂.left) :=
    (isPullback_baseChangeMap f β₁).paste_vert (isPullback_schemeSpaceFunctor_map h)
  rw [← baseChangeMap_comp_inclusion, ← baseChangeMap_comp_inclusion] at hrect
  refine IsPullback.of_bot hrect ?_ (isPullback_baseChangeMap f g₂)
  rw [← baseChangeMap_comp, ← baseChangeMap_comp]
  congr 1
  exact CostructuredArrow.hom_ext _ _ h.w

end AlgebraicGeometry.Space

end
