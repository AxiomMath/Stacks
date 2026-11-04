module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffinePushoutTheorem
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07VX: the whole lemma

Stacks 07VX makes three assertions about a thickening `i : X ⟶ X'` and an affine morphism
`f : X ⟶ Y` of algebraic spaces over `S`: the pushout `Y' = Y ⨿_X X'` exists in the category of
algebraic spaces over `S`, `Y ⟶ Y'` is a thickening, and
`𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}` as sheaves on `Y_étale = (Y')_étale`.  This file states the
three on one theorem.

## Main results

* `AlgebraicGeometry.Space.exists_hasPushout_isThickeningHom_inr_isPullback_appTop`:
  **Stacks 07VX**, the whole lemma.

## Implementation notes

Each assertion is spelled exactly as the declaration proving it states it:
`AlgebraicGeometry.Space.hasPushout_of_isThickeningHom_of_isAffineHom` (existence),
`AlgebraicGeometry.Space.pushout_inr_isThickeningHom` (`Y ⟶ Y'` is a thickening) and
`AlgebraicGeometry.Space.pushout_isPullback_appTop` (the structure sheaf, evaluated on each scheme
étale over `Y'`).  The last two refer to the pushout, so the existence is the witness of the
existential and the other two are stated at it.

## References

* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 07VX.**  Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of
algebraic spaces over `S`.  Then

1. there is a pushout `Y' = Y ⨿_X X'` in the category of algebraic spaces over `S`;
2. `Y ⟶ Y'` is a thickening, so `Y'` is a thickening of `Y`;
3. `𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}` as sheaves on `Y_étale = (Y')_étale`, evaluated on each
   of its objects: for a scheme `W` étale over `Y'` with base changes `W₁` to `X'`, `W₂` to `Y`
   and `W₀` to `X`, the ring `Γ(W, 𝒪)` is the fibre product of `Γ(W₂, 𝒪)` and `Γ(W₁, 𝒪)` over
   `Γ(W₀, 𝒪)`.

The objects of the small étale site of `Y'` are the schemes étale over `Y'`, and the sections over
`W` of `𝒪_Y`, `f_*𝒪_X` and `f'_*𝒪_{X'}` are the rings of functions on `W₂`, `W₀` and `W₁`.  Limits
of sheaves are computed objectwise, so the objectwise statement (3) is the equality of sheaves of
the source. -/
@[stacks 07VX]
theorem exists_hasPushout_isThickeningHom_inr_isPullback_appTop
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) :
    ∃ _ : HasPushout i f,
      IsThickeningHom B S hS (pushout.inr i f) ∧
      ∀ {W W₁ W₂ W₀ : BigFppfOver B S hS} (w : yoneda.obj W ⟶ (pushout i f).1)
        (_hwE : IsEtale B S hS w)
        {u₁ : W₁ ⟶ W} {p₁ : yoneda.obj W₁ ⟶ X'.1}
        (_h₁ : IsPullback (yoneda.map u₁) p₁ w (pushout.inl i f).hom)
        {u₂ : W₂ ⟶ W} {p₂ : yoneda.obj W₂ ⟶ Y.1}
        (_h₂ : IsPullback (yoneda.map u₂) p₂ w (pushout.inr i f).hom)
        {iW : W₀ ⟶ W₁} {fW : W₀ ⟶ W₂} {p₀ : yoneda.obj W₀ ⟶ X.1}
        (_h₀₁ : IsPullback (yoneda.map iW) p₀ p₁ i.hom)
        (_h₀₂ : IsPullback (yoneda.map fW) p₀ p₂ f.hom)
        (hw₀ : iW ≫ u₁ = fW ≫ u₂),
        let Φ := BigFppfOver.toScheme B S hS
        IsPullback ((Φ.map u₂).app ⊤) ((Φ.map u₁).app ⊤) ((Φ.map fW).app ((Φ.map u₂) ⁻¹ᵁ ⊤))
          ((Φ.map iW).app ((Φ.map u₁) ⁻¹ᵁ ⊤) ≫ eqToHom (congrArg (fun O ↦ Γ(Φ.obj W₀, O))
            (congrArg (fun k : Φ.obj W₀ ⟶ Φ.obj W ↦ k ⁻¹ᵁ ⊤)
              (show Φ.map iW ≫ Φ.map u₁ = Φ.map fW ≫ Φ.map u₂ by
                rw [← Φ.map_comp, ← Φ.map_comp, hw₀])))) :=
  have := hasPushout_of_isThickeningHom_of_isAffineHom B S hS i f hi hf
  ⟨this, pushout_inr_isThickeningHom B S hS i f hi hf,
    fun {_ _ _ _} w hwE {_ _} h₁ {_ _} h₂ {_ _ _} h₀₁ h₀₂ hw₀ =>
      pushout_isPullback_appTop B S hS i f hi hf w hwE h₁ h₂ h₀₁ h₀₂ hw₀⟩

end AlgebraicGeometry.Space

end
