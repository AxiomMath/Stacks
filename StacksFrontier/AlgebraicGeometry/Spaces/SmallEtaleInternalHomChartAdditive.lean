module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartLinearMaps

/-!
# The identification of a chart section of an internal Hom with a linear map is additive

A section of the internal Hom `𝓗om_{𝒪_X}(G, G')` of two quasi-coherent `𝒪_X`-modules on an
algebraic space over an étale chart with affine underlying scheme is a `Γ(A, ⊤)`-linear map of
Zariski global sections,
`AlgebraicGeometry.Space.smallEtaleInternalHomChartAssociatedLinearEquiv`.  Both sides are abelian
groups — the first because the internal Hom is a sheaf of modules, the second because it is a
module of linear maps — and this file proves that the identification is additive.

## Main results

* `AlgebraicGeometry.Space.smallEtaleInternalHomChartAssociatedLinearEquiv_add`: **the
  identification is additive**, with
  `AlgebraicGeometry.Space.smallEtaleInternalHomChartPullbackHomEquiv_add` and
  `AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap_add` for its two halves.
* `Stacks.CategoryTheory.Iso.homCongr_add`: conjugation of a morphism by two isomorphisms in a
  preadditive category is additive.
* `Stacks.add_equiv_trans` and `Stacks.linearEquiv_toEquiv_add`: a composite of additive
  bijections is additive, and so is a linear equivalence read as a bijection.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/
@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks

/-- **Additivity passes to a composite of bijections.**  If two bijections are additive then so
is their composite. -/
theorem add_equiv_trans {α β γ : Type*} [Add α] [Add β] [Add γ] {e₁ : α ≃ β} {e₂ : β ≃ γ}
    (h₁ : ∀ x y : α, e₁ (x + y) = e₁ x + e₁ y)
    (h₂ : ∀ x y : β, e₂ (x + y) = e₂ x + e₂ y) (x y : α) :
    (e₁.trans e₂) (x + y) = (e₁.trans e₂) x + (e₁.trans e₂) y := by
  simp only [Equiv.trans_apply, h₁, h₂]

/-- A linear equivalence is additive when read as a bijection. -/
theorem linearEquiv_toEquiv_add {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (e : M ≃ₗ[R] N) (x y : M) :
    e.toEquiv (x + y) = e.toEquiv x + e.toEquiv y :=
  map_add e x y

end Stacks

namespace Stacks.CategoryTheory.Iso

open CategoryTheory

/-- **Conjugating a morphism by two isomorphisms is additive.**  In a preadditive category the
bijection `CategoryTheory.Iso.homCongr` of two isomorphisms is an additive map of the two
Hom-groups. -/
theorem homCongr_add {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C}
    (α : X ≅ X₁) (β : Y ≅ Y₁) (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  simp only [CategoryTheory.Iso.homCongr_apply, Preadditive.add_comp, Preadditive.comp_add]

end Stacks.CategoryTheory.Iso

namespace Stacks.AlgebraicGeometry.ModuleLimits

open CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{u}} [IsAffine X]

omit [IsAffine X] in
/-- Reading a morphism of sheaves of modules on an affine scheme on global sections is
additive. -/
theorem appTopₗ_add {F G : X.Modules} (χ₁ χ₂ : F ⟶ G) :
    appTopₗ (χ₁ + χ₂) = appTopₗ χ₁ + appTopₗ χ₂ :=
  rfl

end Stacks.AlgebraicGeometry.ModuleLimits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- Reading a chart-level section of the internal Hom as a morphism on the slice at the chart is
additive. -/
theorem smallEtaleInternalHomChartHomEquiv_add
    (G G' : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1)
    (α β : (smallEtaleInternalHom B S hS X.1 X.2 G G').val.obj (op A)) :
    smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A (α + β) =
      smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A α +
        smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A β :=
  rfl

/-- The functor of the comparison of [Stacks Project, Tag 04M0] at a chart, read on module
categories, is additive. -/
instance additive_chartModuleReindexEquivalence_functor (A : SmallEtale B S hS X.1) :
    (chartModuleReindexEquivalence B S hS X A).functor.Additive where
  map_add := rfl

/-- Transporting a morphism on the slice at a chart to the small étale site of the chart space is
additive. -/
theorem chartSmallEtaleRestrictionHomEquiv_add
    (M N : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1)
    (f g : M.over A ⟶ N.over A) :
    chartSmallEtaleRestrictionHomEquiv B S hS X M N A (f + g) =
      chartSmallEtaleRestrictionHomEquiv B S hS X M N A f +
        chartSmallEtaleRestrictionHomEquiv B S hS X M N A g :=
  (chartModuleReindexEquivalence B S hS X A).functor.map_add

/-- **Reading a chart-level section of the internal Hom as a morphism of the inverse images to
the small étale site of the chart space is additive.** -/
theorem smallEtaleInternalHomChartPullbackHomEquiv_add
    (G G' : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1)
    (α β : (smallEtaleInternalHom B S hS X.1 X.2 G G').val.obj (op A)) :
    smallEtaleInternalHomChartPullbackHomEquiv B S hS X G G' A (α + β) =
      smallEtaleInternalHomChartPullbackHomEquiv B S hS X G G' A α +
        smallEtaleInternalHomChartPullbackHomEquiv B S hS X G G' A β :=
  Stacks.add_equiv_trans (smallEtaleInternalHomChartHomEquiv_add B S hS X G G' A)
    (Stacks.add_equiv_trans (chartSmallEtaleRestrictionHomEquiv_add B S hS X G G' A)
      (fun f g => Stacks.CategoryTheory.Iso.homCongr_add _ _ f g)) α β

/-- **The inverse of `β ↦ βᵃ` is additive.**  For the associated-module functor on the small étale
site of a represented algebraic space, bijective on morphisms into a quasi-coherent target, the
morphism of Zariski modules that a morphism of associated modules comes from depends additively
on it. -/
theorem representedAssociatedModule_symm_add (U : BigFppfOver B S hS)
    (hF : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M N : ((BigFppfOver.toScheme B S hS).obj U).Modules) [N.IsQuasicoherent]
    (χ₁ χ₂ : (representedAssociatedModule B S hS U hF).obj M ⟶
      (representedAssociatedModule B S hS U hF).obj N) :
    (Equiv.ofBijective _ (bijective_representedAssociatedModule_map B S hS U hF M N)).symm
        (χ₁ + χ₂) =
      (Equiv.ofBijective _ (bijective_representedAssociatedModule_map B S hS U hF M N)).symm χ₁ +
        (Equiv.ofBijective _
          (bijective_representedAssociatedModule_map B S hS U hF M N)).symm χ₂ := by
  refine (bijective_representedAssociatedModule_map B S hS U hF M N).1 ?_
  simp only [Functor.map_add, Equiv.ofBijective_apply_symm_apply]

/-- **Reading a morphism of associated modules as a linear map of Zariski global sections is
additive.** -/
theorem representedAssociatedModuleHomEquivLinearMap_add (U : BigFppfOver B S hS)
    (hF : IsAlgebraicSpace B S hS (yoneda.obj U))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (M N : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (χ₁ χ₂ : (representedAssociatedModule B S hS U hF).obj M ⟶
      (representedAssociatedModule B S hS U hF).obj N) :
    representedAssociatedModuleHomEquivLinearMap B S hS U hF M N (χ₁ + χ₂) =
      representedAssociatedModuleHomEquivLinearMap B S hS U hF M N χ₁ +
        representedAssociatedModuleHomEquivLinearMap B S hS U hF M N χ₂ :=
  Stacks.add_equiv_trans (representedAssociatedModule_symm_add B S hS U hF M N)
    (fun β₁ β₂ => Stacks.AlgebraicGeometry.ModuleLimits.appTopₗ_add β₁ β₂) χ₁ χ₂

/-- **Conjugating by two presentations as associated modules and reading on global sections is
additive**, for an arbitrary object of the site, algebraic-space witness and pair of Zariski
modules. -/
theorem homCongr_representedAssociatedModuleHomEquivLinearMap_add (U : BigFppfOver B S hS)
    (hF : IsAlgebraicSpace B S hS (yoneda.obj U))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (M₀ N₀ : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    [M₀.IsQuasicoherent] [N₀.IsQuasicoherent]
    (G G' : Modules.{u, u} B S hS (yoneda.obj U) hF)
    (eG : G ≅ (representedAssociatedModule B S hS U hF).obj M₀)
    (eG' : G' ≅ (representedAssociatedModule B S hS U hF).obj N₀)
    (χ₁ χ₂ : G ⟶ G') :
    representedAssociatedModuleHomEquivLinearMap B S hS U hF M₀ N₀
        ((CategoryTheory.Iso.homCongr eG eG') (χ₁ + χ₂)) =
      representedAssociatedModuleHomEquivLinearMap B S hS U hF M₀ N₀
          ((CategoryTheory.Iso.homCongr eG eG') χ₁) +
        representedAssociatedModuleHomEquivLinearMap B S hS U hF M₀ N₀
          ((CategoryTheory.Iso.homCongr eG eG') χ₂) := by
  rw [Stacks.CategoryTheory.Iso.homCongr_add, representedAssociatedModuleHomEquivLinearMap_add]

/-- **The identification of a chart-level section of an internal Hom with a linear map of Zariski
global sections is additive.** -/
theorem smallEtaleInternalHomChartAssociatedLinearEquiv_add
    (G G' : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1)
    [IsAffine (chartScheme A)]
    (M₀ N₀ : (chartScheme A).Modules) [M₀.IsQuasicoherent] [N₀.IsQuasicoherent]
    (eG : (modulePullback B S hS (chartToSpace B S hS X A)).obj G ≅
      (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS X.1).obj A)
        (chartSpace B S hS X A).2).obj M₀)
    (eG' : (modulePullback B S hS (chartToSpace B S hS X A)).obj G' ≅
      (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS X.1).obj A)
        (chartSpace B S hS X A).2).obj N₀)
    (α β : (smallEtaleInternalHom B S hS X.1 X.2 G G').val.obj (op A)) :
    smallEtaleInternalHomChartAssociatedLinearEquiv B S hS X G G' A M₀ N₀ eG eG' (α + β) =
      smallEtaleInternalHomChartAssociatedLinearEquiv B S hS X G G' A M₀ N₀ eG eG' α +
        smallEtaleInternalHomChartAssociatedLinearEquiv B S hS X G G' A M₀ N₀ eG eG' β := by
  show representedAssociatedModuleHomEquivLinearMap B S hS
      ((SmallEtale.toOver B S hS X.1).obj A) (chartSpace B S hS X A).2 M₀ N₀
      ((CategoryTheory.Iso.homCongr eG eG')
        (smallEtaleInternalHomChartPullbackHomEquiv B S hS X G G' A (α + β))) = _
  rw [smallEtaleInternalHomChartPullbackHomEquiv_add]
  exact homCongr_representedAssociatedModuleHomEquivLinearMap_add B S hS
    ((SmallEtale.toOver B S hS X.1).obj A) (chartSpace B S hS X A).2 M₀ N₀ _ _ eG eG' _ _

end AlgebraicGeometry.Space

end
