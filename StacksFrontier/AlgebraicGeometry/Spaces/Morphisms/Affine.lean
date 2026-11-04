module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# Affine morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *affine* when its base change along every
morphism from an affine scheme is represented by an affine scheme. Affine morphisms are closed
under composition.

## Main definitions

* `AlgebraicGeometry.Space.IsAffineHom` is affineness of a morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_comp`: a composite of affine morphisms is affine.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WH](https://stacks.math.columbia.edu/tag/03WH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of algebraic spaces is affine if each base change to an affine scheme is
represented by an affine scheme. -/
@[stacks 03WF]
abbrev IsAffineHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  ∀ (Z : BigAffineFppf B S hS)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ G),
    ∃ (W : BigAffineFppf B S hS)
      (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ F)
      (q : (BigAffineFppf.inclusion B S hS).obj W ⟶
        (BigAffineFppf.inclusion B S hS).obj Z), IsPullback p (yoneda.map q) f g

/-- The composition of affine morphisms is affine. -/
@[stacks 03WH]
theorem isAffineHom_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsAffineHom B S hS f) (hg : IsAffineHom B S hS g) :
    IsAffineHom B S hS (f ≫ g) := by
  intro Z a
  obtain ⟨W, p, q, h⟩ := hg Z a
  obtain ⟨V, r, s, k⟩ := hf W p
  exact ⟨V, r, s ≫ q, by simpa using k.paste_vert h⟩

end AlgebraicGeometry.Space

end
