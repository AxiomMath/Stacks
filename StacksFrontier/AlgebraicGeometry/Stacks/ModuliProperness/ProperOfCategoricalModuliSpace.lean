module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliProperness.ProperOfUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliSpaceBasics
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedBaseChangeChart

/-!
# Properness over the base of any categorical moduli space (for Stacks 0DUZ)

A categorical moduli space (Stacks 0DUG) of a category fibred in groupoids is unique up to a
unique isomorphism compatible with the 1-morphisms. So a property of the morphism `M ⟶ Y`
induced by one categorical moduli space `f₀ : 𝒳 ⟶ M₀` passes to the morphism induced by any
other one `f : 𝒳 ⟶ M`. This is how Stacks 0DUZ, stated for "the moduli space constructed in
Theorem 0DUT", is read for every categorical moduli space of `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.isProper_of_isCategoricalModuliSpace_of_isProper_comp`: if some
  categorical moduli space `f₀` of `𝒳` is a universal homeomorphism and the morphisms it induces
  to `Y` under `p` are locally of finite type, then for every categorical moduli space `f` of `𝒳`
  the induced morphism `M ⟶ Y` is proper, as soon as `p` is.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Properness of `M ⟶ Y` for every categorical moduli space, from one that is a universal
homeomorphism.** Let `p : 𝒳 ⟶ Y` be a proper 1-morphism from an algebraic stack to an algebraic
space and let `f₀ : 𝒳 ⟶ M₀` be a categorical moduli space (Stacks 0DUG) which is a universal
homeomorphism, such that every morphism `g₀ : M₀ ⟶ Y` with `f₀ ≫ g₀ ≅ p` is locally of finite
type. Then for every categorical moduli space `f : 𝒳 ⟶ M` and every `g : M ⟶ Y` with
`f ≫ g ≅ p`, the morphism `g` is proper.

The two moduli spaces are identified by an isomorphism `e : M₀ ≅ M` with `f₀ ≫ e = f`
(`AlgebraicGeometry.Stack.exists_iso_of_isCategoricalModuliSpace`); then `e ≫ g` is a
factorization of `p` through `f₀`, proper by
`AlgebraicGeometry.Stack.isProper_of_universalHomeomorphism_of_isProper_comp`, and properness
crosses the isomorphism. -/
theorem isProper_of_isCategoricalModuliSpace_of_isProper_comp
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (p : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (hp : AlgebraicStacks.IsProper B S hS p)
    {M₀ : AlgebraicSpaces B S hS} (f₀ : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M₀.obj M₀.property)
    (hf₀ : IsCategoricalModuliSpace B S hS M₀ f₀.hom)
    (hf₀UH : AlgebraicStacks.UniversalHomeomorphism B S hS f₀)
    (hlft : ∀ g₀ : M₀.obj ⟶ Y, Nonempty (f₀.hom ≫ (associatedMap B S hS g₀).1 ≅ p.hom) →
      Space.IsLocallyOfFiniteType B S hS g₀)
    {M : AlgebraicSpaces B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : IsCategoricalModuliSpace B S hS M f.hom)
    (g : M.obj ⟶ Y) (hfg : Nonempty (f.hom ≫ (associatedMap B S hS g).1 ≅ p.hom)) :
    Space.IsProper B S hS g := by
  obtain ⟨e, he⟩ := exists_iso_of_isCategoricalModuliSpace B S hS hf₀ hf
  obtain ⟨η⟩ := hfg
  have h₀ : Nonempty (f₀.hom ≫ (associatedMap B S hS (e.hom.hom ≫ g)).1 ≅ p.hom) := by
    rw [associatedMap_comp]
    exact ⟨(Bicategory.associator _ _ _).symm ≪≫ eqToIso (by rw [he]) ≪≫ η⟩
  have hprop := isProper_of_universalHomeomorphism_of_isProper_comp B S hS M₀.property hY f₀
    hf₀UH p hp _ h₀ (hlft _ h₀)
  exact (Space.isProper_iff_of_comm_iso B S hS M₀.property hY M.property hY _ g
    ((ObjectProperty.ι _).mapIso e) (Iso.refl Y) (by simp)).1 hprop

end AlgebraicGeometry.Stack

end
