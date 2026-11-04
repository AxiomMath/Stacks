module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedPerfectIsoDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelEtaleBaseChangeMate

/-!
# Pasting the squares of derived pullbacks on the spaces-étale models

For a commutative square `h ≫ j = j' ≫ g` of algebraic spaces,
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackSquare` is the 2-cell
`Lh^* ∘ Lj^* ⟶ Lj'^* ∘ Lg^*` of derived pullbacks on the models of the spaces-étale sites made of
the composition isomorphisms. For two such squares stacked along `j₁`, the square of the composite
is their pasting, read through the composition isomorphisms
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIsoOfEq` of the vertical sides. In the
proof of Stacks 09RI this is the compatibility of the base change bijections for the extensions by
zero along an étale morphism with the transition maps of the stages of a limit.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

attribute [local instance high] HasDerivedCategory.standard

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The square of derived pullbacks around `h ≫ j = j' ≫ g`, objectwise, through the
composition isomorphisms `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIsoOfEq`. -/
theorem spacesEtaleModelDerivedPullbackSquare_app {W W' Y Y' : AlgebraicSpaces B S hS}
    (g : W' ⟶ W) (h : Y' ⟶ Y) (j : Y ⟶ W) (j' : Y' ⟶ W') (comm : h ≫ j = j' ≫ g)
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS W).O))) :
    (spacesEtaleModelDerivedPullbackSquare B S hS g h j j' comm).app Z =
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS h j comm Z).hom ≫
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS j' g rfl Z).inv := by
  have hc : ∀ {k₁ k₂ : Y' ⟶ W} (hk : k₁ = k₂),
      (spacesEtaleModelDerivedPullbackCongr B S hS hk).hom.app Z =
        eqToHom
          (congrArg (fun k => (derivedPullback (spacesEtaleModelHom B S hS k)).obj Z) hk) := by
    rintro _ _ rfl
    rfl
  show (spacesEtaleModelDerivedPullbackCompIso B S hS h j).hom.app Z ≫
      (spacesEtaleModelDerivedPullbackCongr B S hS comm).hom.app Z ≫
        (spacesEtaleModelDerivedPullbackCompIso B S hS j' g).inv.app Z = _
  rw [hc comm]
  simp only [spacesEtaleModelDerivedPullbackCompIsoOfEq, Iso.trans_hom, Iso.trans_inv, Iso.app_hom,
    Iso.app_inv, eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp, Category.assoc]

/-- **Pasting of squares of derived pullbacks.** For squares `h₁ ≫ j₀ = j₁ ≫ g₁` and
`h' ≫ j₁ = j₂ ≫ g'` and their composite `h₂ ≫ j₀ = j₂ ≫ g₂` (`h' ≫ h₁ = h₂`, `g' ≫ g₁ = g₂`), the
square of the composite is the pasting of the two squares, read through the composition
isomorphisms of the vertical sides. -/
theorem spacesEtaleModelDerivedPullbackSquare_paste {Y₀ W₀ Y₁ W₁ Y₂ W₂ : AlgebraicSpaces B S hS}
    (j₀ : Y₀ ⟶ W₀) (j₁ : Y₁ ⟶ W₁) (j₂ : Y₂ ⟶ W₂) (g₁ : W₁ ⟶ W₀) (h₁ : Y₁ ⟶ Y₀)
    (g' : W₂ ⟶ W₁) (h' : Y₂ ⟶ Y₁) {g₂ : W₂ ⟶ W₀} {h₂ : Y₂ ⟶ Y₀} (hg : g' ≫ g₁ = g₂)
    (hh : h' ≫ h₁ = h₂) (comm₁ : h₁ ≫ j₀ = j₁ ≫ g₁) (comm' : h' ≫ j₁ = j₂ ≫ g')
    (comm₂ : h₂ ≫ j₀ = j₂ ≫ g₂)
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS W₀).O))) :
    (spacesEtaleModelDerivedPullbackSquare B S hS g₂ h₂ j₀ j₂ comm₂).app Z =
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS h' h₁ hh
          ((derivedPullback (spacesEtaleModelHom B S hS j₀)).obj Z)).inv ≫
        (derivedPullback (spacesEtaleModelHom B S hS h')).map
          ((spacesEtaleModelDerivedPullbackSquare B S hS g₁ h₁ j₀ j₁ comm₁).app Z) ≫
        (spacesEtaleModelDerivedPullbackSquare B S hS g' h' j₁ j₂ comm').app
          ((derivedPullback (spacesEtaleModelHom B S hS g₁)).obj Z) ≫
        (derivedPullback (spacesEtaleModelHom B S hS j₂)).map
          (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS g' g₁ hg Z).hom := by
  have hr₁ : (j₂ ≫ g') ≫ g₁ = j₂ ≫ g₂ := by rw [Category.assoc, hg]
  have hr₂ : h' ≫ (j₁ ≫ g₁) = j₂ ≫ g₂ := by rw [← Category.assoc, comm', Category.assoc, hg]
  have c₁ := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS j₂ g' g₁ rfl hg hr₁ rfl Z
  have c₂ := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS h' j₁ g₁ comm' rfl hr₁ hr₂ Z
  have c₃ := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS h' h₁ j₀ hh comm₁ comm₂ hr₂ Z
  rw [spacesEtaleModelDerivedPullbackSquare_app, spacesEtaleModelDerivedPullbackSquare_app,
    spacesEtaleModelDerivedPullbackSquare_app, Iso.comp_inv_eq]
  simp only [Category.assoc, Functor.map_comp]
  rw [c₁, Iso.inv_hom_id_assoc, ← c₂, Iso.map_inv_hom_id_assoc, c₃, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Space
