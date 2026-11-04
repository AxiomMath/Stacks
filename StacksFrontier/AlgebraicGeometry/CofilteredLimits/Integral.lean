module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.AffineOpenSections

/-!
# Cofiltered limits of schemes integral over a base

Let `S` be a scheme and let `{ Xᵢ }` be an inverse system of `S`-schemes, indexed by a
cofiltered category, such that every structure morphism `Xᵢ ⟶ S` is integral. Then the limit
`X = lim Xᵢ` is integral over `S`. Over an affine open `U ⊆ S` this is the statement that a
filtered colimit of integral `Γ(S, U)`-algebras is integral: every function on the preimage of
`U` in `X` comes from a function on the preimage of `U` in some `Xⱼ`, where it is integral.

## Main results

* `AlgebraicGeometry.isIntegralHom_of_isLimit`: the structure morphism of a cofiltered limit of
  schemes integral over `S` is integral.

## Implementation notes

The transition morphisms need not be assumed affine: a morphism of `S`-schemes between schemes
integral over `S` is integral, because integral morphisms are separated
(`AlgebraicGeometry.IsIntegralHom.of_comp`). Affineness of the limit projections is then
`AlgebraicGeometry.isAffineHom_π_app`, and the descent of a section to a finite stage is
`AlgebraicGeometry.exists_appLE_π_eq_of_isAffineOpen_of_isLimit`, applied to the affine open
`p i ⁻¹ᵁ U` of a stage.

## References

* [Stacks Project, Tag 0CNK](https://stacks.math.columbia.edu/tag/0CNK)
* [Stacks Project, Tag 0DV7](https://stacks.math.columbia.edu/tag/0DV7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {S : Scheme.{u}} (D : I ⥤ Scheme.{u})
  (p : ∀ i, D.obj i ⟶ S) (hp : ∀ ⦃i j : I⦄ (a : i ⟶ j), D.map a ≫ p j = p i)
  [∀ i, IsIntegralHom (p i)]

include hp in
/-- A transition morphism of an inverse system of schemes integral over `S` is integral. -/
theorem isIntegralHom_map_of_isIntegralHom_comp {i j : I} (a : i ⟶ j) :
    IsIntegralHom (D.map a) := by
  have : IsIntegralHom (D.map a ≫ p j) := by rw [hp a]; infer_instance
  exact IsIntegralHom.of_comp (D.map a) (p j)

include hp in
/-- **A cofiltered limit of schemes integral over `S` is integral over `S`.** Let `{ Xᵢ }` be an
inverse system of schemes indexed by a cofiltered category, with compatible integral morphisms
`p i : Xᵢ ⟶ S`, and let `c` be a limit cone. Then the induced morphism
`c.π.app i ≫ p i : lim Xᵢ ⟶ S` (which does not depend on `i`) is integral. -/
theorem isIntegralHom_of_isLimit [IsCofiltered I] (c : Cone D) (hc : IsLimit c) (i : I) :
    IsIntegralHom (c.π.app i ≫ p i) := by
  have : ∀ {j k : I} (a : j ⟶ k), IsAffineHom (D.map a) := fun a =>
    (isIntegralHom_map_of_isIntegralHom_comp D p hp a).toIsAffineHom
  have := isAffineHom_π_app D c hc i
  refine { isIntegral_app := ?_ }
  intro U hU s
  have hW : IsAffineOpen (p i ⁻¹ᵁ U) := hU.preimage (p i)
  obtain ⟨j, a, t, ht⟩ := exists_appLE_π_eq_of_isAffineOpen_of_isLimit D c hc i hW s
  have hpre : D.map a ⁻¹ᵁ (p i ⁻¹ᵁ U) = p j ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, hp a]
  have hle := hpre.le
  have hint : ((p j).appLE U (D.map a ⁻¹ᵁ (p i ⁻¹ᵁ U)) hle).hom.IsIntegral := by
    rw [Scheme.Hom.appLE_congr _ hle rfl hpre (fun f => f.hom.IsIntegral),
      Scheme.Hom.appLE_eq_app]
    exact IsIntegralHom.isIntegral_app _ U hU
  have hcomp : c.π.app j ≫ p j = c.π.app i ≫ p i := by rw [← hp a, ← Category.assoc, c.w]
  have key : ∀ (f₁ f₂ : c.pt ⟶ S) (_ : f₁ = f₂) (V : c.pt.Opens) (e₁ : V ≤ f₁ ⁻¹ᵁ U)
      (e₂ : V ≤ f₂ ⁻¹ᵁ U), f₁.appLE U V e₁ = f₂.appLE U V e₂ := by
    rintro f₁ _ rfl V e₁ e₂; rfl
  have hπ : c.π.app i ⁻¹ᵁ (p i ⁻¹ᵁ U) ≤ c.π.app j ⁻¹ᵁ (D.map a ⁻¹ᵁ (p i ⁻¹ᵁ U)) :=
    le_of_eq (by rw [← Scheme.Hom.comp_preimage (c.π.app j), c.w])
  have heq : (p j).appLE U _ hle ≫ (c.π.app j).appLE _ (c.π.app i ⁻¹ᵁ (p i ⁻¹ᵁ U)) hπ =
      (c.π.app i ≫ p i).app U := by
    rw [Scheme.Hom.appLE_comp_appLE, ← Scheme.Hom.appLE_eq_app]
    exact key _ _ hcomp _ _ _
  have hs := (hint t).map ((c.π.app j).appLE _ _ hπ).hom
  rwa [ht, ← CommRingCat.hom_comp, heq] at hs

end AlgebraicGeometry

end
