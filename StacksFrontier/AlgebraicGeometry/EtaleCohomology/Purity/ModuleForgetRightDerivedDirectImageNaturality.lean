module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ModuleForgetRightDerivedNaturality

/-!
# Naturality of the identification of `R^q f_*` with `R^q f_*` of the underlying abelian sheaf

For a sheaf `G` of `Λ`-modules on `X_étale`, the underlying abelian sheaf of `R^q f_* G` is
`R^q f_*` of the underlying abelian sheaf of `G`
(`Stacks.EtaleCohomology.etaleModuleForgetRightDerivedDirectImageIso`). This file proves that
this identification is natural in `G`
(`Stacks.EtaleCohomology.etaleModuleForgetRightDerivedDirectImageIso_hom_naturality`), square
by square along the five factors of its definition.

This is used to compare towers `n ↦ R¹ j_*(j⁻¹ Gₙ)` of sheaves of `ℤ_ℓ`-modules on underlying
abelian sheaves, in the tower form of cohomological purity
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.etaleModuleForgetRightDerivedDirectImageIso_hom_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Five commuting squares pasted side by side. -/
private lemma paste_five_squares {E : Type*} [Category* E] {A₀ A₁ A₂ A₃ A₄ A₅ B₀ B₁ B₂ B₃ B₄ B₅ : E}
    (m₀ : A₀ ⟶ B₀) (m₁ : A₁ ⟶ B₁) (m₂ : A₂ ⟶ B₂) (m₃ : A₃ ⟶ B₃) (m₄ : A₄ ⟶ B₄) (m₅ : A₅ ⟶ B₅)
    (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₄) (a₅ : A₄ ⟶ A₅)
    (b₁ : B₀ ⟶ B₁) (b₂ : B₁ ⟶ B₂) (b₃ : B₂ ⟶ B₃) (b₄ : B₃ ⟶ B₄) (b₅ : B₄ ⟶ B₅)
    (h₁ : m₀ ≫ b₁ = a₁ ≫ m₁) (h₂ : m₁ ≫ b₂ = a₂ ≫ m₂) (h₃ : m₂ ≫ b₃ = a₃ ≫ m₃)
    (h₄ : m₃ ≫ b₄ = a₄ ≫ m₄) (h₅ : m₄ ≫ b₅ = a₅ ≫ m₅) :
    m₀ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ b₅ = (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅) ≫ m₅ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₅]
  simp only [Category.assoc]

/-- Applying a functor to a naturality square of a natural transformation. -/
private lemma map_comp_app_comm {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (G : D ⥤ E) {F H : C ⥤ D} (α : F ⟶ H) {X Y : C} (g : X ⟶ Y) :
    G.map (F.map g) ≫ G.map (α.app Y) = G.map (α.app X) ≫ G.map (H.map g) := by
  rw [← G.map_comp, ← G.map_comp, α.naturality]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The identification of the underlying abelian sheaf of `R^q f_* G` with `R^q f_*` of the
underlying abelian sheaf of `G` is natural in `G`.** -/
theorem etaleModuleForgetRightDerivedDirectImageIso_hom_naturality (q : ℕ)
    {G G' : EtaleModules.{u, 0} Λ X} (w : G ⟶ G') :
    (etaleModuleForgetAb.{u, 0} Λ Y).map
        (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).map w) ≫
      (etaleModuleForgetRightDerivedDirectImageIso Λ f G' q).hom =
    (etaleModuleForgetRightDerivedDirectImageIso Λ f G q).hom ≫
      ((etaleAbelianDirectImage.{u, 0} f).rightDerived q).map
        ((etaleModuleForgetAb.{u, 0} Λ X).map w) := by
  let := etaleModules_enoughInjectives.{u, 0} Λ X
  let UX := etaleModuleForgetAb.{u, 0} Λ X
  let UY := etaleModuleForgetAb.{u, 0} Λ Y
  let F := etaleModuleDirectImage.{u, 0} Λ f
  let F' := etaleAbelianDirectImage.{u, 0} f
  let HY := DerivedCategory.Plus.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℤ)
  let sX := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0
  let sX' := DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  -- (b) forgetting commutes with cohomology objects
  have hb : UY.map ((F.rightDerivedPlus (q : ℤ)).map w) ≫
      (etaleModuleForgetPlusHomologyIso Λ Y (F.rightDerivedFunctorPlus.obj (sX.obj G'))
        (q : ℤ)).inv =
      (etaleModuleForgetPlusHomologyIso Λ Y (F.rightDerivedFunctorPlus.obj (sX.obj G))
        (q : ℤ)).inv ≫
        HY.map (UY.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlus.map (sX.map w))) := by
    have hb' := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso UY
      (q : ℤ)).hom.naturality (DerivedCategory.Plus.ι.map
        (F.rightDerivedFunctorPlus.map (sX.map w)))
    exact (Iso.comp_inv_eq _).2 (((Iso.eq_inv_comp _).2 hb'.symm).trans
      (Category.assoc _ _ _).symm)
  -- (d) placing in degree `0` commutes with forgetting
  have hd : HY.map (F'.rightDerivedFunctorPlus.map (UX.mapDerivedCategoryPlus.map (sX.map w))) ≫
      HY.map (F'.rightDerivedFunctorPlus.map (etaleModuleForgetPlusSingleIso Λ X 0 G').hom) =
      HY.map (F'.rightDerivedFunctorPlus.map (etaleModuleForgetPlusSingleIso Λ X 0 G).hom) ≫
        HY.map (F'.rightDerivedFunctorPlus.map (sX'.map (UX.map w))) := by
    rw [← HY.map_comp, ← HY.map_comp, ← F'.rightDerivedFunctorPlus.map_comp,
      ← F'.rightDerivedFunctorPlus.map_comp, etaleModuleForgetPlusSingleIso_hom_naturality]
  -- (e) the comparison of indexings for `F'`
  have he : HY.map (F'.rightDerivedFunctorPlus.map (sX'.map (UX.map w))) ≫
      (Stacks.DerivedIndexing.rightDerivedIso F' q).inv.app (UX.obj G') =
      (Stacks.DerivedIndexing.rightDerivedIso F' q).inv.app (UX.obj G) ≫
        (F'.rightDerived q).map (UX.map w) :=
    ((Stacks.DerivedIndexing.rightDerivedIso F' q).inv.naturality (UX.map w))
  exact paste_five_squares _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (map_comp_app_comm UY (Stacks.DerivedIndexing.rightDerivedIso F q).hom w) hb
    (map_comp_app_comm HY (etaleModuleDerivedDirectImageForgetIso Λ f).hom (sX.map w)) hd he

end Stacks.EtaleCohomology

end
