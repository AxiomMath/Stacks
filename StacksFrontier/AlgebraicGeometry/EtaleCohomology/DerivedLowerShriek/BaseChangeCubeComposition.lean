module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCube
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnderivedExtensionByZeroPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompactificationMorphisms

/-!
# Base change maps of cubes of compactifications: naturality and composition

The naturality of the base change map of `Rf_!` for a cube of compactifications in morphisms of
compactifications, and its compatibility with horizontal composition of cubes
([Stacks, Tag 0F7L]), with the underived inputs discharged.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeCube_naturality`.
* `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeCube_paste`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedBaseChangePlus

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ]

section Naturality

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  {j₁ j₂ : CompactificationOf (Over.mk f)} {j₁' j₂' : CompactificationOf (Over.mk f')}
  (ψ : j₁ ⟶ j₂) (ψ' : j₁' ⟶ j₂') (φ₁ : j₁'.space ⟶ j₁.space) (φ₂ : j₂'.space ⟶ j₂.space)
  (hc₁ : IsPullback g' j₁'.immersion j₁.immersion φ₁)
  (hc₂ : IsPullback g' j₂'.immersion j₂.immersion φ₂)
  (wp : CompactificationOf.Hom.map ψ' ≫ φ₂ = φ₁ ≫ CompactificationOf.Hom.map ψ)
  (w₁ : j₁'.toBase ≫ g = φ₁ ≫ j₁.toBase) (w₂ : j₂'.toBase ≫ g = φ₂ ≫ j₂.toBase)

include wp in
/-- **The base change map of a cube of compactifications is natural in morphisms of
compactifications** ([Stacks, Tag 0F7L]): along `ψ : j₁ ⟶ j₂` and `ψ' : j₁' ⟶ j₂'` compatible with
the two cubes, the base change maps correspond under the comparisons
`Rf_!^{j₂} ⟶ Rf_!^{j₁}` of [Stacks, Tag 0F7I]. -/
theorem derivedLowerShriekBaseChangeCube_naturality :
    Functor.whiskerRight (derivedLowerShriekHom Λ ψ)
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g) ≫
      derivedLowerShriekBaseChangeCube Λ j₁ j₁' φ₁ hc₁ w₁ =
    derivedLowerShriekBaseChangeCube Λ j₂ j₂' φ₂ hc₂ w₂ ≫
      Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g')
        (derivedLowerShriekHom Λ ψ') :=
  derivedLowerShriekBaseChangeCube_hom Λ ψ ψ' φ₁ φ₂ hc₁ hc₂ wp w₁ w₂
    (etaleModuleRefinementComparison_baseChange Λ (CompactificationOf.immersion_comp_map ψ)
      (CompactificationOf.immersion_comp_map ψ') hc₁ hc₂ wp)

end Naturality

section Horizontal

variable {X Y X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
  {g₁ : Y' ⟶ Y} {g₁' : X' ⟶ X} {g₂ : Y'' ⟶ Y'} {g₂' : X'' ⟶ X'}
  (j : CompactificationOf (Over.mk f)) (j' : CompactificationOf (Over.mk f'))
  (j'' : CompactificationOf (Over.mk f'')) (φ₁ : j'.space ⟶ j.space) (φ₂ : j''.space ⟶ j'.space)
  (hc₁ : IsPullback g₁' j'.immersion j.immersion φ₁)
  (hc₂ : IsPullback g₂' j''.immersion j'.immersion φ₂)
  (w₁ : j'.toBase ≫ g₁ = φ₁ ≫ j.toBase) (w₂ : j''.toBase ≫ g₂ = φ₂ ≫ j'.toBase)
  (w₁₂ : j''.toBase ≫ (g₂ ≫ g₁) = (φ₂ ≫ φ₁) ≫ j.toBase)

/-- **The base change maps of cubes compose horizontally** ([Stacks, Tag 0F7L]). -/
theorem derivedLowerShriekBaseChangeCube_paste :
    derivedLowerShriekBaseChangeCube Λ j j'' (φ₂ ≫ φ₁) (hc₂.paste_horiz hc₁) w₁₂ =
      Functor.whiskerLeft (derivedLowerShriek.{u, 0} f j Λ)
          (Functor.mapDerivedCategoryPlusCompIsoh
            (etaleModuleInverseImageCompIso.{u, 0} Λ g₂ g₁).symm).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedLowerShriekBaseChangeCube Λ j j' φ₁ hc₁ w₁)
          (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g₂) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g₁')
          (derivedLowerShriekBaseChangeCube Λ j' j'' φ₂ hc₂ w₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryPlusCompIsoh
            (etaleModuleInverseImageCompIso.{u, 0} Λ g₂' g₁').symm).hom
          (derivedLowerShriek.{u, 0} f'' j'' Λ) :=
  derivedLowerShriekBaseChangeCube_comp Λ j j' j'' φ₁ φ₂ hc₁ hc₂ w₁ w₂ w₁₂
    (etaleModuleBaseChange_pasteH Λ j.toBase j'.toBase j''.toBase g₁ φ₁ g₂ φ₂ w₁ w₂ w₁₂)
    (etaleModuleInverseImageExtensionByZeroIso_pasteH Λ hc₁ hc₂)

end Horizontal

end Stacks.EtaleCohomology
